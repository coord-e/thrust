use std::collections::HashMap;

use rustc_hir::lang_items::LangItem;
use rustc_index::IndexVec;
use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::BasicBlockType;
use crate::rty;

mod annot;
mod basic_block;
mod crate_;
mod did_cache;
mod local_def;

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

pub fn resolve_discr<'tcx>(tcx: TyCtxt<'tcx>, discr: mir_ty::VariantDiscr) -> u32 {
    match discr {
        mir_ty::VariantDiscr::Relative(i) => i,
        mir_ty::VariantDiscr::Explicit(did) => {
            let val = tcx.const_eval_poly(did).unwrap();
            val.try_to_scalar_int().unwrap().try_to_u32().unwrap()
        }
    }
}

#[derive(Debug, Clone)]
struct EnumDatatype {
    def: rty::EnumDatatypeDef,
    matcher_preds: HashMap<Vec<chc::Sort>, chc::PredVarId>,
}

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Collection of refined known def types.
    ///
    /// currently contains only local-def templates,
    /// but will be extended to contain externally known def's refinement types
    /// (at least for every defs referenced by local def bodies)
    defs: HashMap<DefId, rty::RefinedType>,

    /// Resulting CHC system.
    system: chc::System,

    basic_blocks: HashMap<LocalDefId, HashMap<BasicBlock, BasicBlockType>>,
    def_ids: did_cache::DefIdCache<'tcx>,

    enum_datatypes: HashMap<DefId, EnumDatatype>,
}

impl<'tcx> crate::refine::MatcherPredGenerator for Analyzer<'tcx> {
    fn get_or_create_matcher_pred(
        &mut self,
        ty_sym: &chc::DatatypeSymbol,
        args: &[chc::Sort],
    ) -> chc::PredVarId {
        let (did, enum_datatype) = self.find_enum_datatype(ty_sym).unwrap();
        if let Some(matcher_pred) = enum_datatype.matcher_preds.get(args) {
            return *matcher_pred;
        }
        let matcher_pred = self.create_matcher_pred(did, args);
        self.enum_datatypes
            .get_mut(&did)
            .unwrap()
            .matcher_preds
            .insert(args.to_owned(), matcher_pred);
        matcher_pred
    }
}

impl<'tcx> crate::refine::TemplateTypeGenerator<'tcx> for Analyzer<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        tmpl.into_refined_type(|pred_sig| self.generate_pred_var(pred_sig))
    }
}

impl<'tcx> crate::refine::UnrefinedTypeGenerator<'tcx> for Analyzer<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn generate_pred_var(&mut self, pred_sig: chc::PredSig) -> chc::PredVarId {
        self.system.new_pred_var(pred_sig)
    }

    fn implied_atom<FV, F>(&mut self, atoms: Vec<chc::Atom<FV>>, mut fv_sort: F) -> chc::Atom<FV>
    where
        F: FnMut(FV) -> chc::Sort,
        FV: chc::Var + std::fmt::Debug + Clone,
    {
        let fvs: Vec<_> = atoms.iter().flat_map(|a| a.fv()).cloned().collect();
        let mut builder = chc::ClauseBuilder::default();
        let mut pred_sig = chc::PredSig::new();
        for fv in &fvs {
            let sort = fv_sort(fv.clone());
            builder.add_mapped_var(fv.clone(), sort.clone());
            pred_sig.push(sort);
        }
        for atom in atoms {
            builder.add_body_mapped(atom);
        }
        let pv = self.system.new_pred_var(pred_sig);
        let head = chc::Atom::new(pv.into(), fvs.into_iter().map(chc::Term::var).collect());
        let clause = builder.head_mapped(head.clone());
        self.add_clause(clause);
        head
    }

    fn find_enum_datatype(&self, ty_sym: &chc::DatatypeSymbol) -> Option<(DefId, &EnumDatatype)> {
        self.enum_datatypes
            .iter()
            .find(|(_, d)| &d.def.name == ty_sym)
            .map(|(did, d)| (*did, d))
    }

    fn create_matcher_pred(&mut self, did: DefId, args: &[chc::Sort]) -> chc::PredVarId {
        let def = self.enum_datatypes[&did].def.clone();
        let mut matcher_pred_sig: chc::PredSig = def
            .variants
            .iter()
            .map(|v| {
                let mut sort = v.ty.to_sort();
                sort.instantiate_params(args);
                sort
            })
            .collect();
        matcher_pred_sig.push(chc::Sort::datatype(def.name.clone(), args.to_vec()));
        let matcher_pred = self.generate_pred_var(matcher_pred_sig.clone());

        let vars = IndexVec::<chc::TermVarIdx, _>::from_raw(matcher_pred_sig);
        let head = chc::Atom::new(
            matcher_pred.into(),
            vars.indices().map(chc::Term::var).collect(),
        );
        for (variant_idx, variant) in def.variants.iter().enumerate() {
            let ctor_term = chc::Term::datatype_ctor(
                def.name.clone(),
                args.to_vec(),
                variant.name.clone(),
                vec![chc::Term::var(variant_idx.into())],
            );
            let data_var: chc::TermVarIdx = (vars.len() - 1).into();
            let body1 = chc::Term::var(data_var).equal_to(ctor_term);
            let body2 = chc::Term::datatype_discr(def.name.clone(), chc::Term::var(data_var))
                .equal_to(chc::Term::int(variant.discr as i64));
            let clause = chc::Clause {
                vars: vars.clone(),
                head: head.clone(),
                body: vec![body1, body2],
            };
            self.add_clause(clause);
        }

        matcher_pred
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let defs = Default::default();
        let system = Default::default();
        let basic_blocks = Default::default();
        let enum_datatypes = Default::default();
        Self {
            tcx,
            defs,
            system,
            basic_blocks,
            def_ids: did_cache::DefIdCache::new(tcx),
            enum_datatypes,
        }
    }

    pub fn add_clause(&mut self, clause: chc::Clause) {
        tracing::debug!(clause = %clause.display(), id = ?self.system.clauses.next_index(), "add_clause");
        self.system.clauses.push(clause);
    }

    pub fn extend_clauses(&mut self, clauses: impl IntoIterator<Item = chc::Clause>) {
        for clause in clauses {
            self.add_clause(clause);
        }
    }

    pub fn register_enum_def(&mut self, def_id: DefId, enum_def: rty::EnumDatatypeDef) {
        tracing::debug!(def_id = ?def_id, enum_def = ?enum_def, "register_enum_def");
        let ctors = enum_def
            .variants
            .iter()
            .map(|v| chc::DatatypeCtor {
                symbol: v.name.clone(),
                selectors: vec![chc::DatatypeSelector {
                    symbol: chc::DatatypeSymbol::new(format!("_get{}", v.name)),
                    sort: v.ty.to_sort(),
                }],
                discriminant: v.discr,
            })
            .collect();
        let datatype = chc::Datatype {
            symbol: enum_def.name.clone(),
            ctors,
        };
        self.enum_datatypes.insert(
            def_id,
            EnumDatatype {
                def: enum_def,
                matcher_preds: Default::default(),
            },
        );
        self.system.datatypes.push(datatype);
    }

    pub fn enum_defs(&self) -> impl Iterator<Item = (&DefId, &rty::EnumDatatypeDef)> {
        self.enum_datatypes
            .iter()
            .map(|(did, enum_datatype)| (did, &enum_datatype.def))
    }

    pub fn find_enum_variant(
        &self,
        ty_sym: &chc::DatatypeSymbol,
        v_sym: &chc::DatatypeSymbol,
    ) -> Option<&rty::EnumVariantDef> {
        self.enum_datatypes
            .iter()
            .find(|(_, d)| &d.def.name == ty_sym)
            .and_then(|(_, d)| d.def.variants.iter().find(|v| &v.name == v_sym))
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        tracing::debug!(def_id = ?def_id, rty = %rty.display(), "register_def");
        self.defs.insert(def_id, rty);
    }

    pub fn def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.defs.get(&def_id)
    }

    pub fn register_basic_block_ty(
        &mut self,
        def_id: LocalDefId,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        tracing::debug!(def_id = ?def_id, ?bb, rty = %rty.display(), "register_basic_block_ty");
        self.basic_blocks.entry(def_id).or_default().insert(bb, rty);
    }

    pub fn basic_block_ty(&self, def_id: LocalDefId, bb: BasicBlock) -> &BasicBlockType {
        &self.basic_blocks[&def_id][&bb]
    }

    pub fn register_well_known_defs(&mut self) {
        let panic_ty = {
            let param = rty::RefinedType::new(
                rty::PointerType::immut_to(rty::Type::string()).into(),
                rty::Refinement::bottom(),
            );
            let ret = rty::RefinedType::new(rty::Type::never(), rty::Refinement::bottom());
            rty::FunctionType::new([param.vacuous()].into_iter().collect(), ret)
        };
        let panic_def_id = self.tcx.require_lang_item(LangItem::Panic, None);
        self.register_def(panic_def_id, rty::RefinedType::unrefined(panic_ty.into()));
    }

    pub fn crate_analyzer(&mut self) -> crate_::Analyzer<'tcx, '_> {
        crate_::Analyzer::new(self)
    }

    pub fn local_def_analyzer(
        &mut self,
        local_def_id: LocalDefId,
    ) -> local_def::Analyzer<'tcx, '_> {
        local_def::Analyzer::new(self, local_def_id)
    }

    pub fn basic_block_analyzer(
        &mut self,
        local_def_id: LocalDefId,
        bb: BasicBlock,
    ) -> basic_block::Analyzer<'tcx, '_> {
        basic_block::Analyzer::new(self, local_def_id, bb)
    }

    pub fn solve(&mut self) {
        if let Err(err) = self.system.solve() {
            self.tcx.dcx().err(format!("verification error: {:?}", err));
        }
    }
}
