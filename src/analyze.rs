//! Analysis of Rust MIR to generate a CHC system.
//!
//! The [`Analyzer`] generates subtyping constraints in the form of CHCs ([`chc::System`]).
//! The entry point is [`crate_::Analyzer::run`], followed by [`local_def::Analyzer::run`]
//! and [`basic_block::Analyzer::run`], while accumulating the necessary information in
//! [`Analyzer`]. Once [`chc::System`] is collected for the entire input, it invokes an external
//! CHC solver with the [`Analyzer::solve`] and subsequently reports the result.

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

use rustc_hir::lang_items::LangItem;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::Symbol;

use crate::analyze;
use crate::annot::{AnnotFormula, AnnotParser, Resolver};
use crate::chc::{self, ForallSortIdx};
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{self, BasicBlockType, TypeBuilder};
use crate::rty;

mod annot;
mod annot_fn;
mod basic_block;
mod crate_;
mod did_cache;
mod local_def;

// TODO: organize structure and remove cross dependency between refine
pub use did_cache::DefIdCache;

pub fn mir_borrowck_skip_formula_fn(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_def_id: rustc_span::def_id::LocalDefId,
) -> rustc_middle::query::queries::mir_borrowck::ProvidedValue<'_> {
    // TODO: unify impl with local_def::Analyzer
    // if the def is closure defined in formula_fn
    let root_def_id = tcx.typeck_root_def_id(local_def_id.to_def_id());
    let is_annotated_as_formula_fn = tcx
        .get_attrs_by_path(local_def_id.to_def_id(), &analyze::annot::formula_fn_path())
        .next()
        .is_some()
        || tcx
            .get_attrs_by_path(root_def_id, &analyze::annot::formula_fn_path())
            .next()
            .is_some();

    if is_annotated_as_formula_fn {
        tracing::debug!(?local_def_id, "skipping borrow check for formula fn");
        let dummy_result = rustc_middle::mir::ConcreteOpaqueTypes(Default::default());
        return Ok(tcx.arena.alloc(dummy_result));
    }

    (rustc_interface::DEFAULT_QUERY_PROVIDERS
        .queries
        .mir_borrowck)(tcx, local_def_id)
}

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

pub fn resolve_discr(tcx: TyCtxt<'_>, discr: mir_ty::VariantDiscr) -> u32 {
    match discr {
        mir_ty::VariantDiscr::Relative(i) => i,
        mir_ty::VariantDiscr::Explicit(did) => {
            let val = tcx.const_eval_poly(did).unwrap();
            val.try_to_scalar_int().unwrap().to_u32()
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeferredDefMode {
    Analyze,
    NoAnalyze,
}

impl DeferredDefMode {
    fn should_analyze(&self) -> bool {
        matches!(self, DeferredDefMode::Analyze)
    }
}

#[derive(Debug, Clone)]
struct DeferredDefTy<'tcx> {
    // the def that provides the spec (`expected_ty`). this is different from a key in defs when
    // the def is an extern_spec_fn (then it is the extern_spec_fn wrapper carrying the contract).
    local_def_id: LocalDefId,
    cache: Rc<RefCell<HashMap<mir_ty::GenericArgsRef<'tcx>, rty::RefinedType>>>,
    mode: DeferredDefMode,
}

#[derive(Debug, Clone)]
enum DefTy<'tcx> {
    Concrete(rty::RefinedType),
    Deferred(DeferredDefTy<'tcx>),
}

#[derive(Debug, Clone)]
struct BasicBlockDef {
    ty: BasicBlockType,
    has_precondition: bool,
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
pub type TypeParamMap = HashMap<TypeParam, ForallSortIdx>;

#[derive(Eq, PartialEq, Hash)]
pub enum TypeParam {
    GenericType(DefId, u32),
    AssocType(DefId),
}

#[derive(Debug, Clone)]
struct DeferredFormulaFnDef<'tcx> {
    cache: Rc<RefCell<HashMap<mir_ty::GenericArgsRef<'tcx>, annot_fn::FormulaFn<'tcx>>>>,
}

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Collection of refined known def types.
    ///
    /// currently contains only local-def templates,
    /// but will be extended to contain externally known def's refinement types
    /// (at least for every defs referenced by local def bodies)
    defs: HashMap<DefId, DefTy<'tcx>>,

    /// Collection of functions with `#[thrust::formula_fn]` attribute.
    formula_fns: HashMap<LocalDefId, DeferredFormulaFnDef<'tcx>>,

    /// Resulting CHC system.
    system: Rc<RefCell<chc::System>>,

    basic_blocks: HashMap<LocalDefId, HashMap<BasicBlock, BasicBlockDef>>,
    def_ids: did_cache::DefIdCache<'tcx>,

    enum_defs: Rc<RefCell<EnumDefs>>,

    type_params: Rc<RefCell<TypeParamMap>>,
}

impl<'tcx> crate::refine::TemplateRegistry for Analyzer<'tcx> {
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        tmpl.into_refined_type(|pred_sig| self.generate_pred_var(pred_sig))
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn generate_pred_var(&mut self, sig: chc::PredSig) -> chc::PredVarId {
        self.system
            .borrow_mut()
            .new_pred_var(sig, chc::DebugInfo::from_current_span())
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let defs = Default::default();
        let formula_fns = Default::default();
        let system = Default::default();
        let basic_blocks = Default::default();
        let enum_defs = Default::default();
        let type_params = Default::default();
        Self {
            tcx,
            defs,
            formula_fns,
            system,
            basic_blocks,
            def_ids: did_cache::DefIdCache::new(tcx),
            enum_defs,
            type_params,
        }
    }

    pub fn def_ids(&self) -> did_cache::DefIdCache<'tcx> {
        // DefIdCache is backed by Rc
        self.def_ids.clone()
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
                        self.type_builder(self.def_ids(), def_id).build(field_ty)
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

    pub fn register_deferred_def(&mut self, target_def_id: DefId, local_def_id: LocalDefId) {
        self.register_deferred_def_impl(target_def_id, local_def_id, DeferredDefMode::Analyze);
    }

    pub fn register_deferred_def_without_analysis(
        &mut self,
        target_def_id: DefId,
        local_def_id: LocalDefId,
    ) {
        self.register_deferred_def_impl(target_def_id, local_def_id, DeferredDefMode::NoAnalyze);
    }

    fn register_deferred_def_impl(
        &mut self,
        target_def_id: DefId,
        local_def_id: LocalDefId,
        mode: DeferredDefMode,
    ) {
        tracing::info!(
            ?target_def_id,
            ?local_def_id,
            ?mode,
            "register_deferred_def"
        );
        self.defs.entry(target_def_id).or_insert_with(|| {
            DefTy::Deferred(DeferredDefTy {
                local_def_id,
                cache: Rc::new(RefCell::new(HashMap::new())),
                mode,
            })
        });
    }

    pub fn concrete_def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.defs.get(&def_id).and_then(|def_ty| match def_ty {
            DefTy::Concrete(rty) => Some(rty),
            DefTy::Deferred(_) => None,
        })
    }

    // TODO: Remove this cache-only accessor together with
    // `local_def::Analyzer::precompute_callable_param_contracts` once `def_ty_with_args` can be
    // used from formula translation without requiring `&mut Analyzer`.
    pub fn known_function_ty_with_args(
        &self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<rty::FunctionType> {
        let type_builder = TypeBuilder::new(
            self.tcx,
            self.def_ids(),
            def_id,
            self.type_params.clone(),
            self.system.clone(),
        );
        let mut def_ty = match self.defs.get(&def_id)? {
            DefTy::Concrete(rty) => rty.clone(),
            DefTy::Deferred(deferred) => deferred.cache.borrow().get(&generic_args)?.clone(),
        };
        def_ty.instantiate_ty_params(
            generic_args
                .types()
                .map(|ty| type_builder.build(ty))
                .map(rty::RefinedType::unrefined)
                .collect(),
        );
        def_ty.ty.as_function().cloned()
    }

    pub fn formula_fn_with_args(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<annot_fn::FormulaFn<'tcx>> {
        let deferred_formula_fn = self.formula_fns.get(&local_def_id)?;

        let deferred_formula_fn_cache = Rc::clone(&deferred_formula_fn.cache);
        if let Some(formula_fn) = deferred_formula_fn_cache.borrow().get(&generic_args) {
            return Some(formula_fn.clone());
        }

        let translator = annot_fn::AnnotFnTranslator::new(self, local_def_id)
            .with_generic_args(generic_args)
            .with_def_id_cache(self.def_ids(), owner_fn_id);
        let formula_fn = translator.to_formula_fn();
        deferred_formula_fn_cache
            .borrow_mut()
            .insert(generic_args, formula_fn.clone());

        tracing::info!(?local_def_id, formula_fn = %formula_fn.display(), ?generic_args, "formula_fn_with_args");
        Some(formula_fn)
    }

    pub fn def_ty_with_args(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<rty::RefinedType> {
        let type_builder = self.type_builder(self.def_ids(), caller_def_id);

        let deferred_ty = match self.defs.get(&def_id)? {
            DefTy::Concrete(rty) => {
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
        let deferred_ty_mode = deferred_ty.mode;

        let mut analyzer = self.local_def_analyzer(deferred_ty.local_def_id);
        analyzer.generic_args(generic_args);

        let mut expected = analyzer.expected_ty();
        // parameters in annotations are left as params
        // TODO: remove this after annotation V2
        expected.instantiate_ty_params(
            generic_args
                .types()
                .map(|ty| type_builder.build(ty))
                .map(rty::RefinedType::unrefined)
                .collect(),
        );
        deferred_ty_cache
            .borrow_mut()
            .insert(generic_args, expected.clone());
        tracing::info!(?def_id, rty = %expected.display(), ?generic_args, "deferred def");

        if deferred_ty_mode.should_analyze() {
            let mut body_analyzer = if analyzer.local_def_id().to_def_id() == def_id {
                analyzer
            } else {
                let body_local_def_id = def_id
                    .as_local()
                    .expect("Analyze mode is only set for deferred defs keyed on a local def");
                let mut body_analyzer = self.local_def_analyzer(body_local_def_id);
                body_analyzer.generic_args(generic_args);
                body_analyzer
            };
            body_analyzer.run(&expected);
        }
        Some(expected)
    }

    pub fn register_formula_fn(&mut self, local_def_id: LocalDefId) {
        tracing::info!(?local_def_id, "register_formula_fn");
        self.formula_fns.insert(
            local_def_id,
            DeferredFormulaFnDef {
                cache: Rc::new(RefCell::new(HashMap::new())),
            },
        );
    }

    pub fn register_basic_block_ty_with_precondition(
        &mut self,
        def_id: LocalDefId,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        self.register_basic_block_def(
            def_id,
            bb,
            BasicBlockDef {
                ty: rty,
                has_precondition: true,
            },
        );
    }

    pub fn register_basic_block_ty_without_precondition(
        &mut self,
        def_id: LocalDefId,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        self.register_basic_block_def(
            def_id,
            bb,
            BasicBlockDef {
                ty: rty,
                has_precondition: false,
            },
        );
    }

    fn register_basic_block_def(&mut self, def_id: LocalDefId, bb: BasicBlock, def: BasicBlockDef) {
        tracing::debug!(
            def_id = ?def_id,
            ?bb,
            rty = %def.ty.display(),
            has_precondition = def.has_precondition,
            "register_basic_block_def",
        );
        self.basic_blocks.entry(def_id).or_default().insert(bb, def);
    }

    pub fn register_basic_block_precondition(
        &mut self,
        def_id: LocalDefId,
        bb: BasicBlock,
        precondition: rty::Refinement<rty::FunctionParamIdx>,
    ) {
        let bb_def = &mut self
            .basic_blocks
            .get_mut(&def_id)
            .unwrap()
            .get_mut(&bb)
            .unwrap();
        assert!(
            !bb_def.has_precondition,
            "precondition is already registered for basic block"
        );
        bb_def.has_precondition = true;
        bb_def.ty.set_precondition(precondition);
    }

    pub fn basic_block_ty(&self, def_id: LocalDefId, bb: BasicBlock) -> &BasicBlockType {
        &self.basic_blocks[&def_id][&bb].ty
    }

    pub fn basic_block_ty_with_precondition(
        &self,
        def_id: LocalDefId,
        bb: BasicBlock,
    ) -> &BasicBlockType {
        let def = &self.basic_blocks[&def_id][&bb];
        assert!(
            def.has_precondition,
            "basic block does not have precondition"
        );
        &def.ty
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
        let panic_def_id = self
            .tcx
            .require_lang_item(LangItem::Panic, rustc_span::DUMMY_SP);
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
        owner_fn_id: DefId,
    ) -> basic_block::Analyzer<'tcx, '_> {
        basic_block::Analyzer::new(self, local_def_id, bb, owner_fn_id)
    }

    pub fn type_builder(&self, def_ids: DefIdCache<'tcx>, owner_fn_id: DefId) -> TypeBuilder<'tcx> {
        TypeBuilder::new(
            self.tcx,
            def_ids,
            owner_fn_id,
            self.type_params.clone(),
            self.system.clone(),
        )
    }

    pub fn solve(&mut self) {
        if let Err(err) = self.system.borrow().solve() {
            self.tcx.dcx().err(format!("verification error: {:?}", err));
        }
    }

    /// Computes the signature of the function using the given `body`.
    ///
    /// This works like `self.tcx.fn_sig(def_id).instantiate_identity().skip_binder()`,
    /// but extracts parameter and return types directly from the given `body` to obtain a signature that
    /// reflects potential type instantiations happened after `optimized_mir`.
    pub fn fn_sig_with_body(&self, def_id: DefId, body: &mir::Body<'tcx>) -> mir_ty::FnSig<'tcx> {
        let ty = self.tcx.type_of(def_id).instantiate_identity();
        let sig = if let mir_ty::TyKind::Closure(_, substs) = ty.kind() {
            substs.as_closure().sig().skip_binder()
        } else {
            ty.fn_sig(self.tcx).skip_binder()
        };

        self.tcx.mk_fn_sig(
            body.args_iter().map(|arg| body.local_decls[arg].ty),
            body.return_ty(),
            sig.c_variadic,
            sig.safety,
            sig.abi,
        )
    }

    /// Computes the signature of the function.
    ///
    /// This works like `self.tcx.fn_sig(def_id).instantiate_identity().skip_binder()`,
    /// but extracts parameter and return types directly from [`mir::Body`] to obtain a signature that
    /// reflects the actual type of lifted closure functions.
    pub fn fn_sig(&self, def_id: DefId) -> mir_ty::FnSig<'tcx> {
        let body = self.tcx.optimized_mir(def_id);
        self.fn_sig_with_body(def_id, body)
    }

    fn extract_path_with_attr(
        &self,
        local_def_id: LocalDefId,
        attr_path: &[Symbol],
    ) -> Option<DefId> {
        let body = self.tcx.hir_maybe_body_owned_by(local_def_id)?;

        let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
            return None;
        };
        for stmt in block.stmts {
            if self
                .tcx
                .hir_attrs(stmt.hir_id)
                .iter()
                .all(|attr| !attr.path_matches(attr_path))
            {
                continue;
            }
            let rustc_hir::StmtKind::Semi(expr) = stmt.kind else {
                self.tcx.dcx().span_err(
                    stmt.span,
                    "annotated path is expected to be a semi statement",
                );
                continue;
            };
            let rustc_hir::ExprKind::Path(qpath) = expr.kind else {
                self.tcx.dcx().span_err(
                    expr.span,
                    "annotated path is expected to be a path expression",
                );
                continue;
            };
            let typeck = self.tcx.typeck(local_def_id);
            let rustc_hir::def::Res::Def(_, def_id) = typeck.qpath_res(&qpath, expr.hir_id) else {
                self.tcx.dcx().span_err(
                    expr.span,
                    "annotated path is expected to refer to a definition",
                );
                continue;
            };
            return Some(def_id);
        }
        None
    }

    // TODO: reduce number of args
    fn extract_require_annot<T>(
        &self,
        local_def_id: LocalDefId,
        resolver: T,
        self_type_name: Option<String>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<AnnotFormula<T::Output>>
    where
        T: Resolver<Output = rty::FunctionParamIdx>,
    {
        let mut require_annot = None;
        let parser = AnnotParser::new(&resolver, self_type_name);
        for attrs in self
            .tcx
            .get_attrs_by_path(local_def_id.to_def_id(), &analyze::annot::requires_path())
        {
            if require_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let require = parser.parse_formula(ts).unwrap();
            require_annot = Some(require);
        }

        if let Some(formula_def_id) =
            self.extract_path_with_attr(local_def_id, &analyze::annot::requires_path_path())
        {
            let Some(formula_def_id) = formula_def_id.as_local() else {
                panic!(
                    "require annotation with path is expected to refer to a local def, but found: {:?}",
                    formula_def_id
                );
            };
            if require_annot.is_some() {
                unimplemented!();
            }
            let Some(formula_fn) =
                self.formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
            else {
                panic!(
                    "require annotation {:?} is not a formula function",
                    formula_def_id
                );
            };
            require_annot = Some(formula_fn.to_require_annot());
        }

        require_annot
    }

    // TODO: reduce number of args
    fn extract_ensure_annot<T>(
        &self,
        local_def_id: LocalDefId,
        resolver: T,
        self_type_name: Option<String>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<AnnotFormula<T::Output>>
    where
        T: Resolver<Output = rty::RefinedTypeVar<rty::FunctionParamIdx>>,
    {
        let mut ensure_annot = None;

        let parser = AnnotParser::new(&resolver, self_type_name);
        for attrs in self
            .tcx
            .get_attrs_by_path(local_def_id.to_def_id(), &analyze::annot::ensures_path())
        {
            if ensure_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let ensure = parser.parse_formula(ts).unwrap();
            ensure_annot = Some(ensure);
        }

        if let Some(formula_def_id) =
            self.extract_path_with_attr(local_def_id, &analyze::annot::ensures_path_path())
        {
            let Some(formula_def_id) = formula_def_id.as_local() else {
                panic!(
                    "ensure annotation with path is expected to refer to a local def, but found: {:?}",
                    formula_def_id
                );
            };
            if ensure_annot.is_some() {
                unimplemented!();
            }
            let Some(formula_fn) =
                self.formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
            else {
                panic!(
                    "ensure annotation {:?} is not a formula function",
                    formula_def_id
                );
            };
            ensure_annot = Some(formula_fn.to_ensure_annot());
        }

        ensure_annot
    }

    /// Whether the given `def_id` corresponds to a method of one of the `Fn` traits.
    fn is_fn_trait_method(&self, def_id: DefId) -> bool {
        self.tcx
            .opt_associated_item(def_id)
            .and_then(|item| item.trait_container(self.tcx))
            .and_then(|trait_did| self.tcx.fn_trait_kind_from_def_id(trait_did))
            .is_some()
    }
}
