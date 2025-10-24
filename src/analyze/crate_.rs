//! Analyze a local crate.

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;

use crate::analyze;
use crate::annot::{self, AnnotFormula, AnnotParser, ResolverExt as _};
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
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn refine_local_defs(&mut self) {
        for local_def_id in self.tcx.mir_keys(()) {
            if self.tcx.def_kind(*local_def_id).is_fn_like() {
                self.refine_fn_def(local_def_id.to_def_id());
            }
        }
    }

    fn extract_require_annot<T>(
        &self,
        resolver: T,
        def_id: DefId,
    ) -> Option<AnnotFormula<T::Output>>
    where
        T: annot::Resolver,
    {
        let mut require_annot = None;
        for attrs in self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::requires_path())
        {
            if require_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let require = AnnotParser::new(&resolver).parse_formula(ts).unwrap();
            require_annot = Some(require);
        }
        require_annot
    }

    fn extract_ensure_annot<T>(&self, resolver: T, def_id: DefId) -> Option<AnnotFormula<T::Output>>
    where
        T: annot::Resolver,
    {
        let mut ensure_annot = None;
        for attrs in self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::ensures_path())
        {
            if ensure_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let ensure = AnnotParser::new(&resolver).parse_formula(ts).unwrap();
            ensure_annot = Some(ensure);
        }
        ensure_annot
    }

    fn extract_param_annots<T>(
        &self,
        resolver: T,
        def_id: DefId,
    ) -> Vec<(Ident, rty::RefinedType<T::Output>)>
    where
        T: annot::Resolver,
    {
        let mut param_annots = Vec::new();
        for attrs in self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::param_path())
        {
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let (ident, ts) = analyze::annot::split_param(&ts);
            let param = AnnotParser::new(&resolver).parse_rty(ts).unwrap();
            param_annots.push((ident, param));
        }
        param_annots
    }

    fn extract_ret_annot<T>(
        &self,
        resolver: T,
        def_id: DefId,
    ) -> Option<rty::RefinedType<T::Output>>
    where
        T: annot::Resolver,
    {
        let mut ret_annot = None;
        for attrs in self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::ret_path())
        {
            if ret_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let ret = AnnotParser::new(&resolver).parse_rty(ts).unwrap();
            ret_annot = Some(ret);
        }
        ret_annot
    }

    #[tracing::instrument(skip(self), fields(def_id = %self.tcx.def_path_str(def_id)))]
    fn refine_fn_def(&mut self, def_id: DefId) {
        let sig = self.tcx.fn_sig(def_id);
        let sig = sig.instantiate_identity().skip_binder(); // TODO: is it OK?

        let mut param_resolver = analyze::annot::ParamResolver::default();
        for (input_ident, input_ty) in self.tcx.fn_arg_names(def_id).iter().zip(sig.inputs()) {
            let input_ty = TypeBuilder::new(self.tcx).build(*input_ty);
            param_resolver.push_param(input_ident.name, input_ty.to_sort());
        }

        let mut require_annot = self.extract_require_annot(&param_resolver, def_id);
        let mut ensure_annot = {
            let output_ty = TypeBuilder::new(self.tcx).build(sig.output());
            let resolver = annot::StackedResolver::default()
                .resolver(analyze::annot::ResultResolver::new(output_ty.to_sort()))
                .resolver((&param_resolver).map(rty::RefinedTypeVar::Free));
            self.extract_ensure_annot(resolver, def_id)
        };
        let param_annots = self.extract_param_annots(&param_resolver, def_id);
        let ret_annot = self.extract_ret_annot(&param_resolver, def_id);

        if self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::callable_path())
            .next()
            .is_some()
        {
            if require_annot.is_some() || ensure_annot.is_some() {
                unimplemented!();
            }

            require_annot = Some(AnnotFormula::top());
            ensure_annot = Some(AnnotFormula::top());
        }

        assert!(require_annot.is_none() || param_annots.is_empty());
        assert!(ensure_annot.is_none() || ret_annot.is_none());

        if self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::trusted_path())
            .next()
            .is_some()
        {
            assert!(require_annot.is_some() || !param_annots.is_empty());
            assert!(ensure_annot.is_some() || ret_annot.is_some());
            self.trusted.insert(def_id);
        }

        let mut builder = TypeBuilder::new(self.tcx).for_function_template(&mut self.ctx, sig);
        if let Some(AnnotFormula::Formula(require)) = require_annot {
            let formula = require.map_var(|idx| {
                if idx.index() == sig.inputs().len() - 1 {
                    rty::RefinedTypeVar::Value
                } else {
                    rty::RefinedTypeVar::Free(idx)
                }
            });
            builder.param_refinement(formula.into());
        }
        if let Some(AnnotFormula::Formula(ensure)) = ensure_annot {
            builder.ret_refinement(ensure.into());
        }
        for (ident, annot_rty) in param_annots {
            use annot::Resolver as _;
            let (idx, _) = param_resolver.resolve(ident).expect("unknown param");
            builder.param_rty(idx, annot_rty);
        }
        if let Some(ret_rty) = ret_annot {
            builder.ret_rty(ret_rty);
        }
        let rty = rty::RefinedType::unrefined(builder.build().into());
        self.ctx.register_def(def_id, rty);
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
            let expected = self.ctx.def_ty(local_def_id.to_def_id()).unwrap().clone();
            self.ctx.local_def_analyzer(*local_def_id).run(&expected);
        }
    }

    fn assert_callable_entry(&mut self) {
        if let Some((def_id, _)) = self.tcx.entry_fn(()) {
            // we want to assert entry function is safe to execute without any assumption
            // TODO: replace code here with relate_* in Env + Refine context (created with empty env)
            let entry_ty = self
                .ctx
                .def_ty(def_id)
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

            // The index of TyKind::ParamTy is based on the every generic parameters in
            // the definition, including lifetimes. Given the following definition:
            //
            // struct X<'a, T> { f: &'a T }
            //
            // The type of field `f` is &T1 (not T0). However, in Thrust, we ignore lifetime
            // parameters and the index of rty::ParamType is based on type parameters only.
            // We're building a mapping from the original index to the new index here.
            let generics = self.tcx.generics_of(local_def_id);
            let mut type_param_mapping: std::collections::HashMap<usize, usize> =
                Default::default();
            for i in 0..generics.count() {
                let generic_param = generics.param_at(i, self.tcx);
                match generic_param.kind {
                    mir_ty::GenericParamDefKind::Lifetime => {}
                    mir_ty::GenericParamDefKind::Type { .. } => {
                        type_param_mapping.insert(i, type_param_mapping.len());
                    }
                    mir_ty::GenericParamDefKind::Const { .. } => unimplemented!(),
                }
            }

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

                            // see the comment above about this mapping
                            let subst = rty::TypeParamSubst::new(
                                type_param_mapping
                                    .iter()
                                    .map(|(old, new)| {
                                        let old = rty::TypeParamIdx::from(*old);
                                        let new =
                                            rty::ParamType::new(rty::TypeParamIdx::from(*new));
                                        (old, rty::RefinedType::unrefined(new.into()))
                                    })
                                    .collect(),
                            );

                            // the subst doesn't contain refinements, so it's OK to take ty only
                            // after substitution
                            let mut field_rty = rty::RefinedType::unrefined(
                                TypeBuilder::new(self.tcx).build(field_ty),
                            );
                            field_rty.subst_ty_params(&subst);
                            field_rty.ty
                        })
                        .collect();
                    rty::EnumVariantDef {
                        name,
                        discr,
                        field_tys,
                    }
                })
                .collect();

            let ty_params = type_param_mapping.len();
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
        Self { ctx, tcx, trusted }
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
