use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze;
use crate::annot::{AnnotAtom, AnnotParser};
use crate::chc;
use crate::refine::{self, TemplateTypeGenerator, UnrefinedTypeGenerator};
use crate::rty::{self, ClauseBuilderExt as _};

pub struct Analyzer<'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    trusted: HashSet<DefId>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn refine_local_defs(&mut self) {
        for local_def_id in self.tcx.mir_keys(()) {
            if let DefKind::Fn = self.tcx.def_kind(*local_def_id) {
                self.refine_fn_def(local_def_id.to_def_id());
            }
        }
    }

    #[tracing::instrument(skip(self), fields(def_id = %self.tcx.def_path_str(def_id)))]
    fn refine_fn_def(&mut self, def_id: DefId) {
        let sig = self.tcx.fn_sig(def_id);
        let sig = sig.instantiate_identity().skip_binder(); // TODO: is it OK?

        // TODO: merge this into FunctionTemplateBuilder or something like that
        let mut rty = self.ctx.function_template_ty(sig);

        let mut param_resolver = analyze::annot::ParamResolver::default();
        for (input_ident, input_ty) in self.tcx.fn_arg_names(def_id).into_iter().zip(sig.inputs()) {
            param_resolver.push_param(input_ident.name, input_ty);
        }

        let mut require_annot = None;
        for require in self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::requires_path())
        {
            let require = AnnotParser::default()
                .resolver(&param_resolver)
                .parse(require)
                .unwrap();
            if require_annot.is_some() {
                unimplemented!();
            }
            require_annot = Some(require);
        }
        let mut ensure_annot = None;
        for ensure in self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::ensures_path())
        {
            let ensure = AnnotParser::default()
                .resolver(analyze::annot::ResultResolver::new(&sig.output()))
                .resolver(&param_resolver)
                .parse(ensure)
                .unwrap();
            if ensure_annot.is_some() {
                unimplemented!();
            }
            ensure_annot = Some(ensure);
        }

        assert!(require_annot.is_some() == ensure_annot.is_some());
        if self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::trusted_path())
            .next()
            .is_some()
        {
            assert!(require_annot.is_some());
            self.trusted.insert(def_id);
        }
        if let Some(AnnotAtom::Atom(require)) = require_annot {
            let last_idx = rty.params.last_index().unwrap();
            for (param_idx, param_ty) in rty.params.iter_enumerated_mut() {
                let refinement = if param_idx == last_idx {
                    require.clone().into()
                } else {
                    rty::Refinement::top()
                };
                *param_ty = rty::RefinedType::new(
                    param_ty.clone().strip_refinement().vacuous(),
                    refinement,
                );
            }
        }
        if let Some(AnnotAtom::Atom(ensure)) = ensure_annot {
            *rty.ret =
                rty::RefinedType::new(rty.ret.clone().strip_refinement().vacuous(), ensure.into());
        }

        let rty = rty::RefinedType::unrefined(rty.into());
        self.ctx.register_def(def_id, rty);
    }

    fn analyze_local_defs(&mut self) {
        for local_def_id in self.tcx.mir_keys(()) {
            let DefKind::Fn = self.tcx.def_kind(*local_def_id) else {
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
                let clause = builder
                    .clone()
                    .with_value_var(&param_ty.ty)
                    .head(param_ty.refinement);
                self.ctx.add_clause(clause);
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
                            let field_ty = self.ctx.unrefined_ty(field_ty);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(field_ty).into()
                        })
                        .collect();
                    rty::EnumVariantDef {
                        name,
                        discr,
                        field_tys,
                    }
                })
                .collect();

            let ty_params = adt
                .all_fields()
                .map(|f| self.tcx.type_of(f.did).instantiate_identity())
                .flat_map(|ty| {
                    if let mir_ty::TyKind::Param(p) = ty.kind() {
                        Some(p.index as usize)
                    } else {
                        None
                    }
                })
                .max()
                .map(|max| max + 1)
                .unwrap_or(0);
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
