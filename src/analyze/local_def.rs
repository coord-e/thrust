//! Analyze a local definition.

use std::collections::{HashMap, HashSet};

use rustc_index::bit_set::BitSet;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeAndMut};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::symbol::Ident;

use crate::analyze;
use crate::annot::{self, AnnotFormula, AnnotParser, ResolverExt as _};
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{BasicBlockType, TypeBuilder};
use crate::rty;

fn stmt_str_literal(stmt: &rustc_hir::Stmt) -> Option<String> {
    use rustc_ast::LitKind;
    use rustc_hir::{Expr, ExprKind, Stmt, StmtKind};

    match stmt {
        Stmt {
            kind:
                StmtKind::Semi(Expr {
                    kind:
                        ExprKind::Lit(rustc_hir::Lit {
                            node: LitKind::Str(symbol, _),
                            ..
                        }),
                    ..
                }),
            ..
        } => Some(symbol.to_string()),
        _ => None,
    }
}

/// An implementation of the typing of local definitions.
///
/// The current implementation only applies to function definitions. The entry point is
/// [`Analyzer::run`], which generates constraints during typing, given the expected type of the function.
pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,

    body: Body<'tcx>,
    drop_points: HashMap<BasicBlock, analyze::basic_block::DropPoints>,
    type_builder: TypeBuilder<'tcx>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn extract_param_annots<T>(
        &self,
        resolver: T,
        self_type_name: Option<String>,
    ) -> Vec<(Ident, rty::RefinedType<T::Output>)>
    where
        T: annot::Resolver,
    {
        let mut param_annots = Vec::new();
        let parser = AnnotParser::new(&resolver, self_type_name);
        for attrs in self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::param_path())
        {
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let (ident, ts) = analyze::annot::split_param(&ts);
            let param = parser.parse_rty(ts).unwrap();
            param_annots.push((ident, param));
        }
        param_annots
    }

    fn extract_ret_annot<T>(
        &self,
        resolver: T,
        self_type_name: Option<String>,
    ) -> Option<rty::RefinedType<T::Output>>
    where
        T: annot::Resolver,
    {
        let mut ret_annot = None;
        let parser = AnnotParser::new(&resolver, self_type_name);
        for attrs in self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::ret_path())
        {
            if ret_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let ret = parser.parse_rty(ts).unwrap();
            ret_annot = Some(ret);
        }
        ret_annot
    }

    fn impl_type(&self) -> Option<rustc_middle::ty::Ty<'tcx>> {
        use rustc_hir::def::DefKind;

        let parent_def_id = self.tcx.parent(self.local_def_id.to_def_id());

        if !matches!(self.tcx.def_kind(parent_def_id), DefKind::Impl { .. }) {
            return None;
        }

        let self_ty = self.tcx.type_of(parent_def_id).instantiate_identity();

        Some(self_ty)
    }

    pub fn analyze_predicate_definition(&self, local_def_id: LocalDefId) {
        // predicate's name
        let impl_type = self.impl_type();
        let pred_item_name = self.tcx.item_name(local_def_id.to_def_id()).to_string();
        let pred_name = match impl_type {
            Some(t) => t.to_string() + "_" + &pred_item_name,
            None => pred_item_name,
        };

        // function's body
        use rustc_hir::{Block, Expr, ExprKind};

        let hir_map = self.tcx.hir();
        let body_id = hir_map.maybe_body_owned_by(local_def_id).unwrap();
        let hir_body = hir_map.body(body_id);

        let predicate_body = match hir_body.value {
            Expr {
                kind: ExprKind::Block(Block { stmts, .. }, _),
                ..
            } => stmts
                .iter()
                .find_map(stmt_str_literal)
                .expect("invalid predicate definition: no string literal was found."),
            _ => panic!("expected function body, got: {hir_body:?}"),
        };

        // names and sorts of arguments
        let arg_names = self
            .tcx
            .fn_arg_names(local_def_id.to_def_id())
            .iter()
            .map(|ident| ident.to_string());

        let sig = self.ctx.local_fn_sig(local_def_id);
        let arg_sorts = sig
            .inputs()
            .iter()
            .map(|input_ty| self.type_builder.build(*input_ty).to_sort());

        let arg_name_and_sorts = arg_names.into_iter().zip(arg_sorts).collect::<Vec<_>>();

        self.ctx.system.borrow_mut().push_pred_define(
            chc::UserDefinedPred::new(pred_name),
            chc::UserDefinedPredSig::from(arg_name_and_sorts),
            predicate_body,
        );
    }

    pub fn is_annotated_as_trusted(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::trusted_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_callable(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::callable_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_extern_spec_fn(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::extern_spec_fn_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_predicate(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::predicate_path(),
            )
            .next()
            .is_some()
    }

    // TODO: unify this logic with extraction functions above
    pub fn is_fully_annotated(&self) -> bool {
        let has_require = self
            .tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::requires_path(),
            )
            .next()
            .is_some();
        let has_ensure = self
            .tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::ensures_path(),
            )
            .next()
            .is_some();
        let annotated_params: Vec<_> = self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::param_path())
            .map(|attrs| {
                let ts = analyze::annot::extract_annot_tokens(attrs.clone());
                let (ident, _) = analyze::annot::split_param(&ts);
                ident
            })
            .collect();
        let has_ret = self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::ret_path())
            .next()
            .is_some();

        let arg_names = self.tcx.fn_arg_names(self.local_def_id.to_def_id());
        let all_params_annotated = arg_names
            .iter()
            .all(|ident| annotated_params.contains(ident));
        self.is_annotated_as_callable()
            || (has_require && has_ensure)
            || (all_params_annotated && has_ret)
    }

    pub fn trait_item_id(&self) -> Option<LocalDefId> {
        let impl_item_assoc = self
            .tcx
            .opt_associated_item(self.local_def_id.to_def_id())?;
        let trait_item_id = impl_item_assoc
            .trait_item_def_id
            .and_then(|id| id.as_local())?;

        Some(trait_item_id)
    }

    pub fn expected_ty(&mut self) -> rty::RefinedType {
        let sig = self
            .ctx
            .local_fn_sig_with_body(self.local_def_id, &self.body);

        let mut param_resolver = analyze::annot::ParamResolver::default();
        for (input_ident, input_ty) in self
            .tcx
            .fn_arg_names(self.local_def_id.to_def_id())
            .iter()
            .zip(sig.inputs())
        {
            let input_ty = self.type_builder.build(*input_ty);
            param_resolver.push_param(input_ident.name, input_ty.to_sort());
        }

        let output_ty = self.type_builder.build(sig.output());
        let result_param_resolver = annot::StackedResolver::default()
            .resolver(analyze::annot::ResultResolver::new(output_ty.to_sort()))
            .resolver((&param_resolver).map(rty::RefinedTypeVar::Free));

        let self_type_name = self.impl_type().map(|ty| ty.to_string());

        let mut require_annot = self.ctx.extract_require_annot(
            self.local_def_id.to_def_id(),
            &param_resolver,
            self_type_name.clone(),
        );

        let mut ensure_annot = self.ctx.extract_ensure_annot(
            self.local_def_id.to_def_id(),
            &result_param_resolver,
            self_type_name.clone(),
        );

        if let Some(trait_item_id) = self.trait_item_id() {
            tracing::info!("trait item fonud: {:?}", trait_item_id);
            let trait_require_annot = self.ctx.extract_require_annot(
                trait_item_id.into(),
                &param_resolver,
                self_type_name.clone(),
            );
            let trait_ensure_annot = self.ctx.extract_ensure_annot(
                trait_item_id.into(),
                &result_param_resolver,
                self_type_name.clone(),
            );

            assert!(require_annot.is_none() || trait_require_annot.is_none());
            require_annot = require_annot.or(trait_require_annot);

            assert!(ensure_annot.is_none() || trait_ensure_annot.is_none());
            ensure_annot = ensure_annot.or(trait_ensure_annot);
        }

        let param_annots = self.extract_param_annots(&param_resolver, self_type_name.clone());
        let ret_annot = self.extract_ret_annot(&param_resolver, self_type_name);

        if self.is_annotated_as_callable() {
            if require_annot.is_some() || ensure_annot.is_some() {
                unimplemented!();
            }
            if !param_annots.is_empty() || ret_annot.is_some() {
                unimplemented!();
            }

            require_annot = Some(AnnotFormula::top());
            ensure_annot = Some(AnnotFormula::top());
        }

        assert!(require_annot.is_none() || param_annots.is_empty());
        assert!(ensure_annot.is_none() || ret_annot.is_none());

        let mut builder = self.type_builder.for_function_template(&mut self.ctx, sig);
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

        // Note that we do not expect predicate variables to be generated here
        // when type params are still present in the type. Callers should ensure either
        // - type params are fully instantiated, or
        // - the function is fully annotated
        rty::RefinedType::unrefined(builder.build().into())
    }

    /// Extract the target DefId from `#[thrust::extern_spec_fn]` function.
    pub fn extern_spec_fn_target_def_id(&self) -> DefId {
        struct ExtractDefId<'tcx> {
            tcx: TyCtxt<'tcx>,
            outer_def_id: LocalDefId,
            inner_def_id: Option<DefId>,
        }

        impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for ExtractDefId<'tcx> {
            type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

            fn nested_visit_map(&mut self) -> Self::Map {
                self.tcx.hir()
            }

            fn visit_qpath(
                &mut self,
                qpath: &rustc_hir::QPath<'tcx>,
                hir_id: rustc_hir::HirId,
                _span: rustc_span::Span,
            ) {
                let typeck_result = self.tcx.typeck(self.outer_def_id);
                if let rustc_hir::def::Res::Def(_, def_id) = typeck_result.qpath_res(qpath, hir_id)
                {
                    if matches!(
                        self.tcx.def_kind(def_id),
                        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
                    ) {
                        assert!(self.inner_def_id.is_none(), "invalid extern_spec_fn");
                        self.inner_def_id = Some(def_id);
                    }
                }
            }
        }

        use rustc_hir::intravisit::Visitor as _;
        let mut visitor = ExtractDefId {
            tcx: self.tcx,
            outer_def_id: self.local_def_id,
            inner_def_id: None,
        };
        if let rustc_hir::Node::Item(item) = self.tcx.hir_node_by_def_id(self.local_def_id) {
            visitor.visit_item(item);
        }
        visitor.inner_def_id.expect("invalid extern_spec_fn")
    }

    fn is_mut_param(&self, param_idx: rty::FunctionParamIdx) -> bool {
        let param_local = analyze::local_of_function_param(param_idx);
        self.body.local_decls[param_local].mutability.is_mut()
    }

    fn extract_elaborated_deref(
        &self,
        stmt: &mir::Statement<'tcx>,
    ) -> Option<(Local, mir::Place<'tcx>)> {
        let mir::StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        let (lhs, rvalue) = &**assign;
        if !lhs.projection.as_ref().is_empty() {
            return None;
        }
        let lhs_local = lhs.local;

        if let mir::Rvalue::CopyForDeref(place) = &rvalue {
            return Some((lhs_local, *place));
        }

        let mir::Rvalue::Use(mir::Operand::Copy(place)) = &rvalue else {
            return None;
        };

        let unique_did = self.ctx.def_ids.unique()?;
        let nonnull_did = self.ctx.def_ids.nonnull()?;

        let (rest, chunk) = place.projection.as_slice().split_last_chunk::<3>()?;
        let rest_place = mir::Place {
            local: place.local,
            projection: self.tcx.mk_place_elems(rest),
        };
        let local_ty = rest_place.ty(&self.body.local_decls, self.tcx).ty;
        if !local_ty.is_box() {
            return None;
        }
        let inner_ty = local_ty.boxed_ty();

        use mir::ProjectionElem::Field;
        use rustc_target::abi::FieldIdx;
        const ZERO_FIELD: FieldIdx = FieldIdx::from_u32(0);
        let [Field(ZERO_FIELD, ty0), Field(ZERO_FIELD, ty1), Field(ZERO_FIELD, ty2)] = chunk else {
            return None;
        };

        if !matches!(
            ty0.kind(), mir_ty::TyKind::Adt(def, args)
            if def.did() == unique_did && args.type_at(0) == inner_ty
        ) {
            return None;
        }

        if !matches!(
            ty1.kind(), mir_ty::TyKind::Adt(def, args)
            if def.did() == nonnull_did && args.type_at(0) == inner_ty
        ) {
            return None;
        }

        if !matches!(
            ty2.kind(), mir_ty::TyKind::RawPtr(t)
            if t.ty == inner_ty && t.mutbl.is_not()
        ) {
            return None;
        }

        Some((lhs_local, rest_place))
    }

    fn unelaborate_derefs(&mut self) {
        let mut v = analyze::ReplacePlacesVisitor::new(self.tcx);
        for (block, data) in self.body.basic_blocks.clone().iter_enumerated() {
            for (idx, _stmt) in data.statements.iter().enumerate() {
                let stmt =
                    &mut self.body.basic_blocks.as_mut().as_mut_slice()[block].statements[idx];
                v.visit_statement(stmt);
                let stmt = stmt.clone();
                let Some((dest_local, box_place)) = self.extract_elaborated_deref(&stmt) else {
                    continue;
                };
                self.body.basic_blocks.as_mut().as_mut_slice()[block].statements[idx].kind =
                    mir::StatementKind::Nop;
                v.add_replacement(dest_local.into(), box_place);
            }
            if let Some(tmnt) =
                &mut self.body.basic_blocks.as_mut().as_mut_slice()[block].terminator
            {
                v.visit_terminator(tmnt);
            }
        }
    }

    fn mut_locals<'a, T>(&self, visitable: &'a T) -> BitSet<Local>
    where
        T: mir::visit::MirVisitable<'tcx> + ?Sized,
    {
        struct Visitor<'tcx, 'a> {
            tcx: TyCtxt<'tcx>,
            body: &'a Body<'tcx>,

            locals: BitSet<Local>,
        }
        impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'tcx, '_> {
            fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
                if let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place) = rvalue {
                    self.locals.insert(place.local);
                }
                self.super_rvalue(rvalue, location);
            }

            fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: mir::Location) {
                if let mir::Operand::Move(place) = operand {
                    // to be reborrowed; see analyze::basic_block::visitor
                    if place
                        .ty(&self.body.local_decls, self.tcx)
                        .ty
                        .is_mutable_ptr()
                    {
                        self.locals.insert(place.local);
                    }
                }
                self.super_operand(operand, location);
            }

            fn visit_assign(
                &mut self,
                place: &mir::Place<'tcx>,
                rvalue: &mir::Rvalue<'tcx>,
                location: mir::Location,
            ) {
                self.locals.insert(place.local);
                self.super_assign(place, rvalue, location);
            }
        }

        let mut visitor = Visitor {
            tcx: self.tcx,
            body: &self.body,
            locals: BitSet::new_empty(self.body.local_decls.len()),
        };
        visitable.apply(mir::Location::START, &mut visitor);
        visitor.locals
    }

    fn reassign_local_mutabilities(&mut self) {
        use rustc_mir_dataflow::{
            move_paths::{HasMoveData as _, MoveData},
            Analysis as _, MaybeReachable, MoveDataParamEnv,
        };

        for local_decl in &mut self.body.local_decls {
            local_decl.mutability = mir::Mutability::Not;
        }

        let move_data_param_env = {
            // XXX: what...
            let mut body = self.body.clone();
            struct Visitor {
                deref_temps: BitSet<Local>,
            }
            impl<'tcx> mir::visit::Visitor<'tcx> for Visitor {
                fn visit_assign(
                    &mut self,
                    place: &mir::Place<'tcx>,
                    rvalue: &mir::Rvalue<'tcx>,
                    _location: mir::Location,
                ) {
                    if let mir::Rvalue::CopyForDeref { .. } = rvalue {
                        self.deref_temps.insert(place.local);
                    }
                }
            }
            let mut visitor = Visitor {
                deref_temps: BitSet::new_empty(body.local_decls.len()),
            };
            use mir::visit::Visitor as _;
            visitor.visit_body(&body);
            for (local, local_decl) in body.local_decls.iter_enumerated_mut() {
                let local_info = if visitor.deref_temps.contains(local) {
                    mir::LocalInfo::DerefTemp
                } else {
                    mir::LocalInfo::Boring
                };
                local_decl.local_info = mir::ClearCrossCrate::Set(Box::new(local_info));
            }
            let param_env = self.tcx.param_env_reveal_all_normalized(self.local_def_id);
            let move_data = MoveData::gather_moves(&body, self.tcx, param_env, |_| true);
            MoveDataParamEnv {
                move_data,
                param_env,
            }
        };
        let tmp_body = self.body.clone();
        let mut results = rustc_mir_dataflow::impls::MaybeInitializedPlaces::new(
            self.tcx,
            &tmp_body,
            &move_data_param_env,
        )
        .into_engine(self.tcx, &self.body)
        .iterate_to_fixpoint()
        .into_results_cursor(&tmp_body);

        for (block, data) in mir::traversal::preorder(&tmp_body) {
            for statement_index in 0..=data.statements.len() {
                let loc = mir::Location {
                    statement_index,
                    block,
                };
                results.seek_before_primary_effect(loc);
                let MaybeReachable::Reachable(init_places) = results.get() else {
                    continue;
                };
                let init_locals: HashSet<_> = init_places
                    .iter()
                    .map(|p| results.analysis().move_data().move_paths[p].place.local)
                    .collect();
                let mut_locals = self.mut_locals(data.visitable(statement_index));
                tracing::info!(?init_locals, ?mut_locals, ?statement_index, ?block, stmt = ?data.statements.get(statement_index));
                for mut_local in mut_locals.iter() {
                    if init_locals.contains(&mut_local) {
                        self.body.local_decls[mut_local].mutability = mir::Mutability::Mut;
                        tracing::info!(?mut_local, ?statement_index, ?block, "marking mut");
                    }
                }
            }
        }
    }

    fn refine_basic_blocks(&mut self) {
        use rustc_mir_dataflow::Analysis as _;
        let mut results = rustc_mir_dataflow::impls::MaybeLiveLocals
            .into_engine(self.tcx, &self.body)
            .iterate_to_fixpoint()
            .into_results_cursor(&self.body);

        let mut builder = analyze::basic_block::DropPoints::builder(&self.body);
        for (bb, _data) in mir::traversal::postorder(&self.body) {
            let span = tracing::info_span!("refine_basic_block", ?bb);
            let _guard = span.enter();

            self.drop_points.insert(bb, builder.build(&mut results, bb));
            results.seek_to_block_start(bb);
            let mut live_locals: Vec<_> = results
                .get()
                .iter()
                .map(|in_local| {
                    let decl = &self.body.local_decls[in_local];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    (in_local, type_and_mut)
                })
                .collect();
            // TODO: ad-hoc
            if bb == mir::START_BLOCK {
                for a in self.body.args_iter() {
                    if live_locals.iter().any(|(l, _)| *l == a) {
                        continue;
                    }
                    let decl = &self.body.local_decls[a];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    live_locals.push((a, type_and_mut));
                    self.drop_points
                        .get_mut(&bb)
                        .unwrap()
                        .before_statements
                        .push(a);
                }
            }
            // function return type is basic block return type
            let ret_ty = self.body.local_decls[mir::RETURN_PLACE].ty;
            let rty = self
                .type_builder
                .for_template(&mut self.ctx)
                .build_basic_block(live_locals, ret_ty);
            self.ctx.register_basic_block_ty(self.local_def_id, bb, rty);
        }
    }

    fn analyze_basic_blocks(&mut self) {
        for bb in self.body.basic_blocks.indices() {
            let rty = self.ctx.basic_block_ty(self.local_def_id, bb).clone();
            let drop_points = self.drop_points[&bb].clone();
            self.ctx
                .basic_block_analyzer(self.local_def_id, bb)
                .body(self.body.clone())
                .drop_points(drop_points)
                .run(&rty);
        }
    }

    fn elaborate_mut_params(&self, fn_ty: &mut rty::FunctionType) {
        if self.body.arg_count == 0 {
            return;
        }

        for (param_idx, param_ty) in fn_ty.params.iter_enumerated_mut() {
            let ty = if self.is_mut_param(param_idx) {
                rty::PointerType::own(param_ty.ty.clone()).into()
            } else {
                param_ty.ty.clone()
            };
            *param_ty = rty::RefinedType::new(
                ty,
                param_ty
                    .refinement
                    .clone()
                    .subst_value_var(|| {
                        if self.is_mut_param(param_idx) {
                            chc::Term::var(rty::RefinedTypeVar::Value).box_current()
                        } else {
                            chc::Term::var(rty::RefinedTypeVar::Value)
                        }
                    })
                    .subst_var(|v| {
                        if self.is_mut_param(v) {
                            chc::Term::var(v).box_current()
                        } else {
                            chc::Term::var(v)
                        }
                    }),
            );
        }

        fn_ty.ret.refinement = fn_ty.ret.refinement.clone().subst_var(|v| {
            if self.is_mut_param(v) {
                chc::Term::var(v).box_current()
            } else {
                chc::Term::var(v)
            }
        });
    }

    // TODO: remove this
    fn elaborate_unused_args(
        &self,
        bb_ty: &BasicBlockType,
        expected_ty: &rty::FunctionType,
    ) -> rty::FunctionType {
        let mut params = IndexVec::new();
        let mut subst = HashMap::new();
        for (param_idx, param_ty) in bb_ty.as_ref().params.iter_enumerated() {
            if let Some(param_local) = bb_ty.local_of_param(param_idx) {
                // unit return may use _0 without preceeding def
                if param_local == mir::RETURN_PLACE {
                    subst.extend(
                        bb_ty
                            .as_ref()
                            .params
                            .indices()
                            .skip_while(|idx| idx.index() <= param_idx.index())
                            .map(|idx| (idx, idx + 1)),
                    );
                    if bb_ty.as_ref().params.len() == 1 {
                        params.push(rty::RefinedType::new(
                            rty::Type::unit(),
                            param_ty.refinement.clone(),
                        ));
                    }
                    continue;
                }
                while analyze::local_of_function_param(params.next_index()) != param_local {
                    tracing::debug!(next_idx = ?params.next_index(), param_local = ?param_local, "elaborate_unused_args");
                    let mock_ty = expected_ty.params[params.next_index()].ty.clone();
                    params.push(rty::RefinedType::unrefined(mock_ty));
                }
            }
            subst.insert(param_idx, params.next_index());
            params.push(param_ty.clone().map_var(|v| subst[&v]));
        }
        rty::FunctionType::new(params, bb_ty.as_ref().ret.clone().map_var(|v| subst[&v]))
    }

    fn assert_entry(&mut self, expected: &rty::RefinedType) {
        let entry_ty = self.ctx.basic_block_ty(self.local_def_id, mir::START_BLOCK);
        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry before");
        let mut expected = expected.ty.as_function().cloned().unwrap();
        self.elaborate_mut_params(&mut expected);

        let entry_ty = self.elaborate_unused_args(entry_ty, &expected);

        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry after");
        let clauses = rty::relate_sub_closed_type(&entry_ty.into(), &expected.into());
        self.ctx.extend_clauses(clauses);
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(ctx: &'ctx mut analyze::Analyzer<'tcx>, local_def_id: LocalDefId) -> Self {
        let tcx = ctx.tcx;
        let body = tcx.optimized_mir(local_def_id.to_def_id()).clone();
        let drop_points = Default::default();
        let type_builder = TypeBuilder::new(tcx, local_def_id.to_def_id());
        Self {
            ctx,
            tcx,
            local_def_id,
            body,
            drop_points,
            type_builder,
        }
    }

    pub fn generic_args(&mut self, generic_args: mir_ty::GenericArgsRef<'tcx>) -> &mut Self {
        self.body =
            mir_ty::EarlyBinder::bind(self.body.clone()).instantiate(self.tcx, generic_args);
        self
    }

    pub fn run(&mut self, expected: &rty::RefinedType) {
        let span = tracing::info_span!("def", def = %self.tcx.def_path_str(self.local_def_id));
        let _guard = span.enter();

        self.unelaborate_derefs();
        self.reassign_local_mutabilities();
        self.refine_basic_blocks();
        self.analyze_basic_blocks();
        self.assert_entry(expected);
    }
}
