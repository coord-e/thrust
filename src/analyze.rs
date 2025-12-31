//! Analysis of Rust MIR to generate a CHC system.
//!
//! The [`Analyzer`] generates subtyping constraints in the form of CHCs ([`chc::System`]).
//! The entry point is [`crate_::Analyzer::run`], followed by [`local_def::Analyzer::run`]
//! and [`basic_block::Analyzer::run`], while accumulating the necessary information in
//! [`Analyzer`]. Once [`chc::System`] is collected for the entire input, it invokes an external
//! CHC solver with the [`Analyzer::solve`] and subsequently reports the result.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_hir::lang_items::LangItem;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{self, BasicBlockType, TypeBuilder};
use crate::rty;

mod annot;
mod basic_block;
mod crate_;
mod did_cache;
mod local_def;

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

pub fn resolve_discr(tcx: TyCtxt<'_>, discr: mir_ty::VariantDiscr) -> u32 {
    match discr {
        mir_ty::VariantDiscr::Relative(i) => i,
        mir_ty::VariantDiscr::Explicit(did) => {
            let val = tcx.const_eval_poly(did).unwrap();
            val.try_to_scalar_int().unwrap().try_to_u32().unwrap()
        }
    }
}

pub struct ReplacePlacesVisitor<'tcx> {
    replacements: HashMap<(Local, &'tcx [mir::PlaceElem<'tcx>]), mir::Place<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for ReplacePlacesVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        _: mir::visit::PlaceContext,
        _: mir::Location,
    ) {
        let proj = place.projection.as_slice();
        for i in 0..=proj.len() {
            if let Some(to) = self.replacements.get(&(place.local, &proj[0..i])) {
                place.local = to.local;
                place.projection = self.tcx.mk_place_elems_from_iter(
                    to.projection.iter().chain(proj.iter().skip(i).cloned()),
                );
                return;
            }
        }
    }
}

impl<'tcx> ReplacePlacesVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            replacements: Default::default(),
        }
    }

    pub fn with_replacement(
        tcx: TyCtxt<'tcx>,
        from: mir::Place<'tcx>,
        to: mir::Place<'tcx>,
    ) -> Self {
        let mut visitor = Self::new(tcx);
        visitor.add_replacement(from, to);
        visitor
    }

    pub fn add_replacement(&mut self, from: mir::Place<'tcx>, to: mir::Place<'tcx>) {
        self.replacements
            .insert((from.local, from.projection.as_slice()), to);
    }

    pub fn visit_statement(&mut self, stmt: &mut mir::Statement<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_statement(self, stmt, mir::Location::START);
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
    }
}

#[derive(Debug, Clone)]
struct DeferredDefTy<'tcx> {
    cache: Rc<RefCell<HashMap<mir_ty::GenericArgsRef<'tcx>, rty::RefinedType>>>,
}

#[derive(Debug, Clone)]
enum DefTy<'tcx> {
    Concrete(rty::RefinedType),
    Deferred(DeferredDefTy<'tcx>),
}

#[derive(Debug, Clone, Default)]
pub struct EnumDefs {
    defs: HashMap<DefId, rty::EnumDatatypeDef>,
}

impl EnumDefs {
    pub fn find_by_name(&self, name: &chc::DatatypeSymbol) -> Option<&rty::EnumDatatypeDef> {
        self.defs.values().find(|def| &def.name == name)
    }

    pub fn get(&self, def_id: DefId) -> Option<&rty::EnumDatatypeDef> {
        self.defs.get(&def_id)
    }

    pub fn insert(&mut self, def_id: DefId, def: rty::EnumDatatypeDef) {
        self.defs.insert(def_id, def);
    }
}

impl refine::EnumDefProvider for Rc<RefCell<EnumDefs>> {
    fn enum_def(&self, name: &chc::DatatypeSymbol) -> rty::EnumDatatypeDef {
        self.borrow().find_by_name(name).unwrap().clone()
    }
}

pub type Env = refine::Env<Rc<RefCell<EnumDefs>>>;

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Collection of refined known def types.
    ///
    /// currently contains only local-def templates,
    /// but will be extended to contain externally known def's refinement types
    /// (at least for every defs referenced by local def bodies)
    defs: HashMap<DefId, DefTy<'tcx>>,

    /// Resulting CHC system.
    system: Rc<RefCell<chc::System>>,

    basic_blocks: HashMap<LocalDefId, HashMap<BasicBlock, BasicBlockType>>,
    def_ids: did_cache::DefIdCache<'tcx>,

    enum_defs: Rc<RefCell<EnumDefs>>,
}

impl<'tcx> crate::refine::TemplateRegistry for Analyzer<'tcx> {
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        tmpl.into_refined_type(|pred_sig| self.generate_pred_var(pred_sig))
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn generate_pred_var(&mut self, sig: chc::PredSig) -> chc::PredVarId {
        self.system
            .borrow_mut()
            .new_pred_var(sig, chc::DebugInfo::from_current_span())
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

    fn build_enum_def(&self, def_id: DefId) -> rty::EnumDatatypeDef {
        let adt = self.tcx.adt_def(def_id);

        let name = refine::datatype_symbol(self.tcx, def_id);
        let variants: IndexVec<_, _> = adt
            .variants()
            .iter()
            .map(|variant| {
                // TODO: consider using TyCtxt::tag_for_variant
                let discr = resolve_discr(self.tcx, variant.discr);
                let field_tys = variant
                    .fields
                    .iter()
                    .map(|field| {
                        let field_ty = self.tcx.type_of(field.did).instantiate_identity();
                        TypeBuilder::new(self.tcx, def_id).build(field_ty)
                    })
                    .collect();
                rty::EnumVariantDef {
                    name: chc::DatatypeSymbol::new(format!("{}.{}", name, variant.name)),
                    discr,
                    field_tys,
                }
            })
            .collect();

        let generics = self.tcx.generics_of(def_id);
        let ty_params = (0..generics.count())
            .filter(|idx| {
                matches!(
                    generics.param_at(*idx, self.tcx).kind,
                    mir_ty::GenericParamDefKind::Type { .. }
                )
            })
            .count();
        tracing::debug!(?def_id, ?name, ?ty_params, "ty_params count");

        rty::EnumDatatypeDef {
            name,
            ty_params,
            variants,
        }
    }

    pub fn get_or_register_enum_def(&self, def_id: DefId) -> rty::EnumDatatypeDef {
        let mut enum_defs = self.enum_defs.borrow_mut();
        if let Some(enum_def) = enum_defs.get(def_id) {
            return enum_def.clone();
        }

        let enum_def = self.build_enum_def(def_id);
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
        enum_defs.insert(def_id, enum_def.clone());
        self.system.borrow_mut().datatypes.push(datatype);

        enum_def
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        tracing::info!(def_id = ?def_id, rty = %rty.display(), "register_def");
        self.defs.insert(def_id, DefTy::Concrete(rty));
    }

    pub fn register_deferred_def(&mut self, def_id: DefId) {
        tracing::info!(def_id = ?def_id, "register_deferred_def");
        self.defs.insert(
            def_id,
            DefTy::Deferred(DeferredDefTy {
                cache: Rc::new(RefCell::new(HashMap::new())),
            }),
        );
    }

    pub fn concrete_def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.defs.get(&def_id).and_then(|def_ty| match def_ty {
            DefTy::Concrete(rty) => Some(rty),
            DefTy::Deferred(_) => None,
        })
    }

    pub fn def_ty_with_args(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<rty::RefinedType> {
        let deferred_ty = match self.defs.get(&def_id)? {
            DefTy::Concrete(rty) => {
                let type_builder = TypeBuilder::new(self.tcx, def_id);

                let mut def_ty = rty.clone();
                def_ty.instantiate_ty_params(
                    generic_args
                        .types()
                        .map(|ty| type_builder.build(ty))
                        .map(rty::RefinedType::unrefined)
                        .collect(),
                );
                return Some(def_ty);
            }
            DefTy::Deferred(deferred) => deferred,
        };

        let deferred_ty_cache = Rc::clone(&deferred_ty.cache); // to cut reference to allow &mut self
        if let Some(rty) = deferred_ty_cache.borrow().get(&generic_args) {
            return Some(rty.clone());
        }

        let mut analyzer = self.local_def_analyzer(def_id.as_local()?);
        analyzer.generic_args(generic_args);

        let expected = analyzer.expected_ty();
        deferred_ty_cache
            .borrow_mut()
            .insert(generic_args, expected.clone());

        analyzer.run(&expected);
        Some(expected)
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

    pub fn new_env(&self) -> Env {
        refine::Env::new(Rc::clone(&self.enum_defs))
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

    /// Computes the signature of the local function.
    ///
    /// This works like `self.tcx.fn_sig(local_def_id).instantiate_identity().skip_binder()`,
    /// but extracts parameter and return types directly from the given `body` to obtain a signature that
    /// reflects potential type instantiations happened after `optimized_mir`.
    pub fn local_fn_sig_with_body(
        &self,
        local_def_id: LocalDefId,
        body: &mir::Body<'tcx>,
    ) -> mir_ty::FnSig<'tcx> {
        let ty = self.tcx.type_of(local_def_id).instantiate_identity();
        let sig = if let mir_ty::TyKind::Closure(_, substs) = ty.kind() {
            substs.as_closure().sig().skip_binder()
        } else {
            ty.fn_sig(self.tcx).skip_binder()
        };

        self.tcx.mk_fn_sig(
            body.args_iter().map(|arg| body.local_decls[arg].ty),
            body.return_ty(),
            sig.c_variadic,
            sig.unsafety,
            sig.abi,
        )
    }

    /// Computes the signature of the local function.
    ///
    /// This works like `self.tcx.fn_sig(local_def_id).instantiate_identity().skip_binder()`,
    /// but extracts parameter and return types directly from [`mir::Body`] to obtain a signature that
    /// reflects the actual type of lifted closure functions.
    pub fn local_fn_sig(&self, local_def_id: LocalDefId) -> mir_ty::FnSig<'tcx> {
        let body = self.tcx.optimized_mir(local_def_id);
        self.local_fn_sig_with_body(local_def_id, body)
    }
}
