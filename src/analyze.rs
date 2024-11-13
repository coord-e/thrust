use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{self, BasicBlockType};
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
    system: Rc<RefCell<chc::System>>,

    basic_blocks: HashMap<LocalDefId, HashMap<BasicBlock, BasicBlockType>>,
    def_ids: did_cache::DefIdCache<'tcx>,

    enum_defs: Rc<RefCell<HashMap<DefId, rty::EnumDatatypeDef>>>,
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
    pub fn generate_pred_var(&mut self, sig: chc::PredSig) -> chc::PredVarId {
        self.system
            .borrow_mut()
            .new_pred_var(sig, chc::DebugInfo::from_current_span())
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
        let pv = self.generate_pred_var(pred_sig);
        let head = chc::Atom::new(pv.into(), fvs.into_iter().map(chc::Term::var).collect());
        let clause = builder.head_mapped(head.clone());
        self.add_clause(clause);
        head
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let defs = Default::default();
        let system = Default::default();
        let basic_blocks = Default::default();
        let enum_defs = Default::default();
        Self {
            tcx,
            defs,
            system,
            basic_blocks,
            def_ids: did_cache::DefIdCache::new(tcx),
            enum_defs,
        }
    }

    pub fn add_clause(&mut self, clause: chc::Clause) {
        self.system.borrow_mut().push_clause(clause);
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
                selectors: v
                    .field_tys
                    .clone()
                    .into_iter()
                    .enumerate()
                    .map(|(idx, ty)| chc::DatatypeSelector {
                        symbol: chc::DatatypeSymbol::new(format!("_get{}.{}", v.name, idx)),
                        sort: ty.to_sort(),
                    })
                    .collect(),
                discriminant: v.discr,
            })
            .collect();
        let datatype = chc::Datatype {
            symbol: enum_def.name.clone(),
            params: enum_def.ty_params,
            ctors,
        };
        self.enum_defs.borrow_mut().insert(def_id, enum_def);
        self.system.borrow_mut().datatypes.push(datatype);
    }

    pub fn find_enum_variant(
        &self,
        ty_sym: &chc::DatatypeSymbol,
        v_sym: &chc::DatatypeSymbol,
    ) -> Option<rty::EnumVariantDef> {
        self.enum_defs
            .borrow()
            .iter()
            .find(|(_, d)| &d.name == ty_sym)
            .and_then(|(_, d)| d.variants.iter().find(|v| &v.name == v_sym))
            .cloned()
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        tracing::info!(def_id = ?def_id, rty = %rty.display(), "register_def");
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

    pub fn new_env(&self) -> refine::Env {
        let defs = self
            .enum_defs
            .borrow()
            .values()
            .map(|def| (def.name.clone(), def.clone()))
            .collect();
        refine::Env::new(defs)
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
        if let Err(err) = self.system.borrow().solve() {
            self.tcx.dcx().err(format!("verification error: {:?}", err));
        }
    }
}
