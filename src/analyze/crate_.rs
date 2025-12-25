//! Analyze a local crate.

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;
use crate::chc;
use crate::refine::{self, TypeBuilder};
use crate::rty::{self, ClauseBuilderExt as _};

/// An implementation of local crate analysis.
///
/// The entry point is [`Analyzer::run`], which performs the following steps in order:
///
/// 1. Register enum definitions found in the crate.
/// 2. Give initial refinement types to local function definitions based on their signatures and
///    annotations. This generates template refinement types with predicate variables for parameters and
///    return types that are not known via annotations.
/// 3. Type local function definition bodies via [`super::local_def::Analyzer`] using the refinement types
///    generated in the previous step.
pub struct Analyzer<'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    trusted: HashSet<DefId>,
    predicates: HashSet<DefId>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn refine_local_defs(&mut self) {
        for local_def_id in self.tcx.mir_keys(()) {
            if self.tcx.def_kind(*local_def_id).is_fn_like() {
                self.refine_fn_def(*local_def_id);
            }
        }
    }

    #[tracing::instrument(skip(self), fields(def_id = %self.tcx.def_path_str(local_def_id)))]
    fn refine_fn_def(&mut self, local_def_id: LocalDefId) {
        let mut analyzer = self.ctx.local_def_analyzer(local_def_id);

        if analyzer.is_annotated_as_trusted() {
            assert!(analyzer.is_fully_annotated());
            self.trusted.insert(local_def_id.to_def_id());
        }

        if analyzer.is_annotated_as_predicate() {
            self.predicates.insert(local_def_id.to_def_id());
        }

        let sig = self
            .tcx
            .fn_sig(local_def_id)
            .instantiate_identity()
            .skip_binder();
        use mir_ty::TypeVisitableExt as _;
        if sig.has_param() && !analyzer.is_fully_annotated() {
            self.ctx.register_deferred_def(local_def_id.to_def_id());
        } else {
            let expected = analyzer.expected_ty();
            self.ctx.register_def(local_def_id.to_def_id(), expected);
        }
    }

    fn analyze_local_defs(&mut self) {
        for local_def_id in self.tcx.mir_keys(()) {
            if !self.tcx.def_kind(*local_def_id).is_fn_like() {
                continue;
            };
            if self.trusted.contains(&local_def_id.to_def_id()) {
                tracing::info!(?local_def_id, "trusted");
                continue;
            }
            let Some(expected) = self.ctx.concrete_def_ty(local_def_id.to_def_id()) else {
                // when the local_def_id is deferred it would be skipped
                continue;
            };

            // check polymorphic function def by replacing type params with some opaque type
            // (and this is no-op if the function is mono)
            let type_builder = TypeBuilder::new(self.tcx, local_def_id.to_def_id())
                .with_param_mapper(|_| rty::Type::int());
            let mut expected = expected.clone();
            let subst = rty::TypeParamSubst::new(
                expected
                    .free_ty_params()
                    .into_iter()
                    .map(|ty_param| (ty_param, rty::RefinedType::unrefined(rty::Type::int())))
                    .collect(),
            );
            expected.subst_ty_params(&subst);
            self.ctx
                .local_def_analyzer(*local_def_id)
                .type_builder(type_builder)
                .run(&expected);
        }
    }

    fn assert_callable_entry(&mut self) {
        if let Some((def_id, _)) = self.tcx.entry_fn(()) {
            // we want to assert entry function is safe to execute without any assumption
            // TODO: replace code here with relate_* in Env + Refine context (created with empty env)
            let entry_ty = self
                .ctx
                .concrete_def_ty(def_id)
                .unwrap()
                .ty
                .as_function()
                .unwrap()
                .clone();
            let mut builder = chc::ClauseBuilder::default();
            for (param_idx, param_ty) in entry_ty.params.iter_enumerated() {
                let param_sort = param_ty.ty.to_sort();
                if !param_sort.is_singleton() {
                    builder.add_mapped_var(param_idx, param_sort);
                }
            }
            builder.add_body(chc::Atom::top());
            for param_ty in entry_ty.params {
                let cs = builder
                    .clone()
                    .with_value_var(&param_ty.ty)
                    .head(param_ty.refinement);
                self.ctx.extend_clauses(cs);
            }
        }
    }

    fn register_enum_defs(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            let DefKind::Enum = self.tcx.def_kind(local_def_id) else {
                continue;
            };
            let adt = self.tcx.adt_def(local_def_id);

            let name = refine::datatype_symbol(self.tcx, local_def_id.to_def_id());
            let variants: IndexVec<_, _> = adt
                .variants()
                .iter()
                .map(|variant| {
                    let name = refine::datatype_symbol(self.tcx, variant.def_id);
                    // TODO: consider using TyCtxt::tag_for_variant
                    let discr = analyze::resolve_discr(self.tcx, variant.discr);
                    let field_tys = variant
                        .fields
                        .iter()
                        .map(|field| {
                            let field_ty = self.tcx.type_of(field.did).instantiate_identity();
                            TypeBuilder::new(self.tcx, local_def_id.to_def_id()).build(field_ty)
                        })
                        .collect();
                    rty::EnumVariantDef {
                        name,
                        discr,
                        field_tys,
                    }
                })
                .collect();

            let generics = self.tcx.generics_of(local_def_id);
            let ty_params = (0..generics.count())
                .filter(|idx| {
                    matches!(
                        generics.param_at(*idx, self.tcx).kind,
                        mir_ty::GenericParamDefKind::Type { .. }
                    )
                })
                .count();
            tracing::debug!(?local_def_id, ?name, ?ty_params, "ty_params count");

            let def = rty::EnumDatatypeDef {
                name,
                ty_params,
                variants,
            };
            self.ctx.register_enum_def(local_def_id.to_def_id(), def);
        }
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(ctx: &'ctx mut analyze::Analyzer<'tcx>) -> Self {
        let tcx = ctx.tcx;
        let trusted = HashSet::default();
        let predicates = HashSet::default();
        Self { ctx, tcx, trusted, predicates }
    }

    pub fn run(&mut self) {
        let span = tracing::debug_span!("crate", krate = %self.tcx.crate_name(rustc_span::def_id::LOCAL_CRATE));
        let _guard = span.enter();

        self.register_enum_defs();
        self.refine_local_defs();
        self.analyze_local_defs();
        self.assert_callable_entry();
    }
}
