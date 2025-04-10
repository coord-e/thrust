use std::collections::{HashMap, HashSet};

use rustc_index::bit_set::BitSet;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeAndMut};
use rustc_span::def_id::LocalDefId;

use crate::analyze;
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{BasicBlockType, TemplateTypeGenerator};
use crate::rty;

pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,

    body: Body<'tcx>,
    drop_points: HashMap<BasicBlock, analyze::basic_block::DropPoints>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
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
            let rty = self.ctx.basic_block_template_ty(live_locals, ret_ty);
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
        Self {
            ctx,
            tcx,
            local_def_id,
            body,
            drop_points,
        }
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
