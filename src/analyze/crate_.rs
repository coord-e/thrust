use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;

use crate::analyze;
use crate::annot::{AnnotAtom, AnnotParser};
use crate::chc;
use crate::refine::{self, PredVarGenerator, TemplateTypeGenerator};
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

    fn refine_fn_def(&mut self, def_id: DefId) {
        let sig = self.tcx.fn_sig(def_id);
        let sig = sig.instantiate_identity().skip_binder(); // TODO: is it OK?

        // TODO: merge this into FunctionTemplateBuilder or something like that
        let mut rty = self.ctx.mir_function_ty(sig);

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
                if param_idx == last_idx {
                    param_ty.refinement = require.clone().into();
                } else {
                    param_ty.refinement = rty::Refinement::top();
                }
            }
        }
        if let Some(AnnotAtom::Atom(ensure)) = ensure_annot {
            rty.ret.refinement = ensure.into();
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
                builder.add_mapped_var(param_idx, param_ty.ty.to_sort());
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
                            // TODO: generic args
                            let field_ty = field.ty(self.tcx, self.tcx.mk_args(&[]));
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.ctx.mir_ty(field_ty)).into()
                        })
                        .collect();
                    let ty = rty::TupleType::new(field_tys).into();
                    rty::EnumVariantDef { name, discr, ty }
                })
                .collect();

            let mut matcher_pred_sig: chc::PredSig =
                variants.iter().map(|v| v.ty.to_sort()).collect();
            matcher_pred_sig.push(chc::Sort::datatype(name.clone()));
            let matcher_pred = self.ctx.generate_pred_var(matcher_pred_sig.clone());

            let vars = IndexVec::<chc::TermVarIdx, _>::from_raw(matcher_pred_sig);
            let head = chc::Atom::new(
                matcher_pred.into(),
                vars.indices().map(chc::Term::var).collect(),
            );
            for (variant_idx, variant) in variants.iter().enumerate() {
                let ctor_term = chc::Term::datatype_ctor(
                    name.clone(),
                    variant.name.clone(),
                    vec![chc::Term::var(variant_idx.into())],
                );
                let data_var: chc::TermVarIdx = (vars.len() - 1).into();
                let body1 = chc::Term::var(data_var).equal_to(ctor_term);
                let body2 = chc::Term::datatype_discr(name.clone(), chc::Term::var(data_var))
                    .equal_to(chc::Term::int(variant.discr as i64));
                let clause = chc::Clause {
                    vars: vars.clone(),
                    head: head.clone(),
                    body: vec![body1, body2],
                };
                self.ctx.add_clause(clause);
            }

            let def = rty::EnumDatatypeDef {
                name,
                variants,
                matcher_pred,
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
        self.register_enum_defs();
        self.refine_local_defs();
        self.analyze_local_defs();
        self.assert_callable_entry();
    }
}
