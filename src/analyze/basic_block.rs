use std::collections::HashMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{
    self, BasicBlock, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_target::abi::FieldIdx;

use crate::analyze;
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{BasicBlockType, Env, TempVarIdx, TemplateTypeGenerator, Var};
use crate::rty::{self, ClauseBuilderExt as _};

mod drop_point;
mod visitor;
pub use drop_point::DropPoints;

pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,
    drop_points: DropPoints,
    basic_block: BasicBlock,
    body: &'tcx Body<'tcx>,

    env: Env,
    local_decls: IndexVec<Local, mir::LocalDecl<'tcx>>,
    elaborated_locals: HashMap<Local, mir::Place<'tcx>>,
    // TODO: remove this
    prophecy_vars: HashMap<usize, TempVarIdx>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn def_ids(&self) -> &analyze::did_cache::DefIdCache<'tcx> {
        &self.ctx.def_ids
    }

    fn is_defined(&self, local: Local) -> bool {
        self.env.contains_local(local)
    }

    fn is_mut_local(&self, local: Local) -> bool {
        self.local_decls[local].mutability.is_mut()
    }

    fn reborrow_visitor<'a>(&'a mut self) -> visitor::ReborrowVisitor<'a, 'tcx, 'ctx> {
        visitor::ReborrowVisitor::new(self)
    }

    fn replace_elaborated_locals_visitor(&self) -> visitor::ReplacePlacesVisitor<'tcx> {
        let mut visitor = visitor::ReplacePlacesVisitor::new(self.tcx);
        for (from, to) in &self.elaborated_locals {
            visitor.add_replacement((*from).into(), to.clone());
        }
        visitor
    }

    fn basic_block_ty(&self, bb: BasicBlock) -> &BasicBlockType {
        &self.ctx.basic_block_ty(self.local_def_id, bb)
    }

    // TODO: reconsider API
    fn bind_locals(&mut self, ty: &BasicBlockType) -> rty::RefinedType<Var> {
        let subst_var_fn = |env: &Env, idx| {
            // TODO: this would be broken when we turned args mutually-referenced...
            let (_, term) = env.local_type(ty.local_of_param(idx).unwrap());
            term
        };
        for (param_idx, param_ty) in ty.as_ref().params.iter_enumerated() {
            // TODO: reconsider clone()
            let param_ty = param_ty
                .clone()
                .subst_var(|idx| subst_var_fn(&self.env, idx));
            if let Some(local) = ty.local_of_param(param_idx) {
                self.env.bind(local, param_ty);
            } else {
                let param_refinement = param_ty.to_free_refinement(|| {
                    panic!("non-local basic block function param must not mention value var")
                });
                self.env.assume(param_refinement);
            }
        }
        ty.as_ref()
            .ret
            .clone()
            .subst_var(|idx| subst_var_fn(&self.env, idx))
    }

    fn mir_refined_ty(&mut self, ty: mir_ty::Ty<'_>) -> rty::RefinedType<Var> {
        let ty = self.ctx.mir_ty(ty);
        let mut builder = rty::TemplateBuilder::default();
        for (v, sort) in self.env.dependencies() {
            builder.add_dependency(v, sort);
        }
        let tmpl = builder.build(ty);
        self.ctx.register_template(tmpl)
    }

    fn bind_local(&mut self, local: Local, rty: rty::RefinedType<Var>, mutbl: mir::Mutability) {
        // elaboration:
        let elaborated_rty = if mutbl.is_mut() {
            let refinement = rty.refinement.subst_var(|v| match v {
                rty::RefinedTypeVar::Value => {
                    chc::Term::var(rty::RefinedTypeVar::Value).box_current()
                }
                v => chc::Term::var(v),
            });
            let ty = rty::PointerType::own(rty.ty).into();
            rty::RefinedType::new(ty, refinement)
        } else {
            rty
        };
        self.env.bind(local, elaborated_rty);
    }

    fn relate_sub_refined_type(
        &mut self,
        got: &rty::RefinedType<Var>,
        expected: &rty::RefinedType<Var>,
    ) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_refined_type");

        self.ctx.relate_sub_type(&got.ty, &expected.ty);

        let clause = self
            .env
            .build_clause()
            .with_value_var(&got.ty)
            .add_body(got.refinement.clone())
            .head(expected.refinement.clone());
        self.ctx.add_clause(clause);
    }

    // this can't be implmeneted in relate_sub_type because rty::FunctionType is free from Var
    fn relate_fn_sub_type(
        &mut self,
        got: rty::FunctionType,
        mut expected_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<Var>>,
        expected_ret: rty::RefinedType<Var>,
    ) {
        if expected_args.is_empty() {
            // elaboration: we need at least one predicate variable in parameter (see mir_function_ty_impl)
            expected_args.push(rty::RefinedType::unrefined(rty::Type::unit()).vacuous());
        }
        tracing::debug!(
            got = %got.display(),
            expected = %crate::pretty::FunctionType::new(&expected_args, &expected_ret).display(),
            "fn_sub_type"
        );

        // TODO: check sty and length is equal
        let mut builder = self.env.build_clause();
        for (param_idx, param_rty) in got.params.iter_enumerated() {
            builder.add_mapped_var(param_idx, param_rty.ty.to_sort());
        }
        for ((param_idx, got_ty), expected_ty) in got.params.iter_enumerated().zip(&expected_args) {
            // TODO we can use relate_sub_refined_type here when we implemenented builder-aware relate_*
            let clause = builder
                .clone()
                .with_value_var(&got_ty.ty)
                .add_body(expected_ty.refinement.clone())
                .head(got_ty.refinement.clone());
            self.ctx.add_clause(clause);
            builder
                .with_mapped_value_var(param_idx)
                .add_body(expected_ty.refinement.clone());
            self.ctx.relate_sub_type(&expected_ty.ty, &got_ty.ty);
        }

        let clause = builder
            .with_value_var(&got.ret.ty)
            .add_body(got.ret.refinement)
            .head(expected_ret.refinement);
        self.ctx.add_clause(clause);
        self.ctx.relate_sub_type(&got.ret.ty, &expected_ret.ty);
    }

    fn operand_type(&self, operand: Operand<'_>) -> (rty::Type, chc::Term<Var>) {
        let (sty, term) = self.env.operand_type(operand.clone());
        tracing::debug!(operand = ?operand, sty = %sty.display(), "operand_type");
        if matches!(operand, Operand::Copy(p) | Operand::Move(p) if self.is_mut_local(p.local)) {
            (sty.deref(), term.box_current())
        } else {
            (sty, term)
        }
    }

    fn rvalue_type(&mut self, rvalue: Rvalue<'_>) -> (rty::Type, Option<chc::Term<Var>>) {
        match rvalue {
            Rvalue::Use(operand) => {
                let (ty, term) = self.operand_type(operand);
                (ty, Some(term))
            }
            Rvalue::BinaryOp(op, operands) => {
                let (lhs, rhs) = *operands;
                let (lhs_ty, lhs_term) = self.operand_type(lhs);
                let (rhs_ty, rhs_term) = self.operand_type(rhs);
                // NOTE: BinOp::Offset accepts operands with different types
                //       but we don't support it here
                self.ctx.relate_equal_type(&lhs_ty, &rhs_ty);
                let (ty, term) = match (&lhs_ty, op) {
                    (rty::Type::Int, mir::BinOp::Add) => (lhs_ty, lhs_term.add(rhs_term)),
                    (rty::Type::Int, mir::BinOp::Sub) => (lhs_ty, lhs_term.sub(rhs_term)),
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Ge) => {
                        (rty::Type::Bool, lhs_term.ge(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Gt) => {
                        (rty::Type::Bool, lhs_term.gt(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Le) => {
                        (rty::Type::Bool, lhs_term.le(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Lt) => {
                        (rty::Type::Bool, lhs_term.lt(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Eq) => {
                        (rty::Type::Bool, lhs_term.eq(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Ne) => {
                        (rty::Type::Bool, lhs_term.ne(rhs_term))
                    }
                    _ => unimplemented!("ty={}, op={:?}", lhs_ty.display(), op),
                };
                (ty, Some(term))
            }
            Rvalue::Cast(
                mir::CastKind::PointerCoercion(mir_ty::adjustment::PointerCoercion::ReifyFnPointer),
                operand,
                _ty,
            ) => {
                let func_ty = match operand.const_fn_def() {
                    Some((def_id, args)) => {
                        if !args.is_empty() {
                            tracing::warn!(?args, ?def_id, "generic args ignored");
                        }
                        self.ctx.def_ty(def_id).expect("unknown def").ty.clone()
                    }
                    _ => unimplemented!(),
                };
                (func_ty.into(), None)
            }
            _ => unimplemented!("rvalue={:?}", rvalue),
        }
    }

    fn rvalue_refined_type(&mut self, rvalue: Rvalue<'_>) -> rty::RefinedType<Var> {
        let (sty, term) = self.rvalue_type(rvalue);

        if let Some(term) = term {
            // TODO: should we cover "is_singleton" ness in relate_* methods or here?
            if !sty.to_sort().is_singleton() {
                return rty::RefinedType::refined_with_term(sty, term);
            }
        }

        rty::RefinedType::unrefined(sty).vacuous()
    }

    fn type_rvalue(&mut self, rvalue: Rvalue<'_>, expected: &rty::RefinedType<Var>) {
        let got = self.rvalue_refined_type(rvalue);
        self.relate_sub_refined_type(&got, expected);
    }

    fn operand_refined_type(&mut self, operand: Operand<'_>) -> rty::RefinedType<Var> {
        self.rvalue_refined_type(Rvalue::Use(operand))
    }

    fn type_operand(&mut self, operand: Operand<'_>, expected: &rty::RefinedType<Var>) {
        self.type_rvalue(Rvalue::Use(operand), expected);
    }

    fn type_return(&mut self, expected: &rty::RefinedType<Var>) {
        self.type_operand(Operand::Move(mir::RETURN_PLACE.into()), expected);
    }

    fn type_goto(&mut self, bb: BasicBlock, expected_ret: &rty::RefinedType<Var>) {
        tracing::debug!(bb = ?bb, "type_goto");
        let bty = self.basic_block_ty(bb);
        let expected_args: IndexVec<_, _> = bty
            .as_ref()
            .params
            .iter_enumerated()
            .map(|(param_idx, rty)| {
                if let Some(arg_local) = bty.local_of_param(param_idx) {
                    let (sty, term) = self.env.local_type(arg_local);
                    // TODO: should we cover "is_singleton" ness in relate_* methods or here?
                    if !rty.ty.to_sort().is_singleton() {
                        rty::RefinedType::refined_with_term(sty, term)
                    } else {
                        rty::RefinedType::unrefined(sty).vacuous()
                    }
                } else {
                    rty::RefinedType::unrefined(rty.ty.clone()).vacuous()
                }
            })
            .collect();
        self.relate_fn_sub_type(bty.to_function_ty(), expected_args, expected_ret.clone());
    }

    fn with_assumptions<F, T>(&mut self, assumptions: Vec<chc::Atom<Var>>, callback: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let old_env = self.env.clone();
        self.env.extend_assumptions(assumptions);
        let result = callback(self);
        self.env = old_env;
        result
    }

    fn with_assumption<F, T>(&mut self, assumption: chc::Atom<Var>, callback: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let old_env = self.env.clone();
        self.env.assume(assumption);
        let result = callback(self);
        self.env = old_env;
        result
    }

    fn type_switch_int<F>(
        &mut self,
        discr: Operand<'_>,
        targets: mir::SwitchTargets,
        expected_ret: &rty::RefinedType<Var>,
        mut callback: F,
    ) where
        F: FnMut(&mut Self, BasicBlock),
    {
        let (discr_ty, discr_term) = self.operand_type(discr);
        let mut negations = Vec::new();
        for (val, bb) in targets.iter() {
            let val: i64 = val.try_into().unwrap();
            let target_term = match (val, &discr_ty) {
                (0, rty::Type::Bool) => chc::Term::bool(false),
                (1, rty::Type::Bool) => chc::Term::bool(true),
                (n, rty::Type::Int) => chc::Term::int(n),
                _ => unimplemented!(),
            };
            self.with_assumption(discr_term.clone().equal_to(target_term.clone()), |ecx| {
                callback(ecx, bb);
                ecx.type_goto(bb, expected_ret);
            });
            negations.push(discr_term.clone().not_equal_to(target_term));
        }
        self.with_assumptions(negations, |ecx| {
            callback(ecx, targets.otherwise());
            ecx.type_goto(targets.otherwise(), expected_ret);
        });
    }

    fn is_box_new(&self, def_id: DefId) -> bool {
        // TODO: stop using diagnositc item for semantic purpose
        self.tcx.all_diagnostic_items(()).id_to_name.get(&def_id)
            == Some(&rustc_span::symbol::sym::box_new)
    }

    fn type_call<I>(&mut self, func: Operand<'tcx>, args: I, expected_ret: &rty::RefinedType<Var>)
    where
        I: IntoIterator<Item = Operand<'tcx>>,
    {
        // TODO: handle const_fn_def on Env side
        let func_ty = match func.const_fn_def() {
            // TODO: move this to well-known defs?
            Some((def_id, args)) if self.is_box_new(def_id) => {
                let inner_ty = self.ctx.mir_ty(args.type_at(0));
                let param = rty::RefinedType::unrefined(inner_ty.clone());
                let ret_term =
                    chc::Term::box_(chc::Term::var(rty::FunctionParamIdx::from(0_usize)));
                let ret = rty::RefinedType::refined_with_term(
                    rty::PointerType::own(inner_ty).into(),
                    ret_term,
                );
                rty::FunctionType::new([param.vacuous()].into_iter().collect(), ret).into()
            }
            Some((def_id, args)) => {
                if !args.is_empty() {
                    tracing::warn!(?args, ?def_id, "generic args ignored");
                }
                self.ctx.def_ty(def_id).expect("unknown def").ty.clone()
            }
            _ => {
                let (ty, _) = self.env.operand_type(func.clone());
                ty
            }
        };
        let expected_args: IndexVec<_, _> = args
            .into_iter()
            .map(|op| self.operand_refined_type(op))
            .collect();
        if let rty::Type::Function(func_ty) = func_ty {
            self.relate_fn_sub_type(func_ty, expected_args, expected_ret.clone());
        } else {
            panic!("unexpected def type: {:?}", func_ty);
        }
    }

    fn assign_to_local(&mut self, local: Local, rvalue: Rvalue<'tcx>) {
        let (_local_ty, local_term) = self.env.local_type(local);
        let (_rvalue_ty, rvalue_term) = self.rvalue_type(rvalue);
        if let Some(rvalue_term) = rvalue_term {
            self.env
                .assume(local_term.mut_final().equal_to(rvalue_term));
        }
    }

    fn drop_local(&mut self, local: Local) {
        self.env.drop_local(local);
    }

    fn add_prophecy_var(&mut self, statement_index: usize, ty: mir_ty::Ty<'_>) {
        let ty = self.ctx.mir_ty(ty);
        let temp_var = self.env.push_temp_var(ty);
        self.prophecy_vars.insert(statement_index, temp_var);
        tracing::debug!(stmt_idx = %statement_index, temp_var = ?temp_var, "add_prophecy_var");
    }

    fn mutable_borrow(
        &mut self,
        statement_index: usize,
        referent: mir::Place<'tcx>,
    ) -> rty::RefinedType<Var> {
        let temp_var = self.prophecy_vars[&statement_index];
        let (ty, term) = self.env.borrow_place(referent, temp_var);
        rty::RefinedType::refined_with_term(ty, term)
    }

    fn borrow_place_(
        &mut self,
        place: mir::Place<'tcx>,
        prophecy_ty: mir_ty::Ty<'tcx>,
    ) -> rty::RefinedType<Var> {
        let prophecy_ty = self.ctx.mir_ty(prophecy_ty);
        let prophecy = self.env.push_temp_var(prophecy_ty);
        let (ty, term) = self.env.borrow_place(place, prophecy);
        rty::RefinedType::refined_with_term(ty, term)
    }

    fn merge_drop_points(&mut self, from: Local, to: Local) {
        let from_pos = self.drop_points.position(from).unwrap();
        self.drop_points.remove_after_statement(from_pos, from);

        let Some(to_pos) = self.drop_points.position(to) else {
            return;
        };
        if from_pos > to_pos {
            self.drop_points.remove_after_statement(to_pos, to);
            self.drop_points.insert_after_statement(from_pos, to);
        }
    }

    fn unelaborate_box_deref(&self, place: &mir::Place<'tcx>) -> Option<mir::Place<'tcx>> {
        let unique_did = self.def_ids().unique()?;
        let nonnull_did = self.def_ids().nonnull()?;

        let (rest, chunk) = place.projection.as_slice().split_last_chunk::<3>()?;
        let rest_place = mir::Place {
            local: place.local,
            projection: self.tcx.mk_place_elems(rest),
        };
        let local_ty = rest_place.ty(&self.local_decls, self.tcx).ty;
        if !local_ty.is_box() {
            return None;
        }
        let inner_ty = local_ty.boxed_ty();

        use mir::ProjectionElem::Field;
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

        Some(rest_place)
    }

    #[tracing::instrument(skip(self, lhs, rvalue))]
    fn analyze_assignment(
        &mut self,
        lhs: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        stmt_idx: usize,
    ) {
        if self.is_defined(lhs.local) {
            // assignment
            assert!(lhs.projection.as_slice() == &[mir::PlaceElem::Deref]);
            self.assign_to_local(lhs.local, rvalue.clone());
            return;
        }

        // definition
        assert!(lhs.projection.is_empty());

        if let Rvalue::Use(Operand::Copy(operand)) = rvalue {
            if let Some(place) = self.unelaborate_box_deref(operand) {
                self.elaborated_locals.insert(lhs.local, place);
                self.merge_drop_points(lhs.local, place.local);
                tracing::info!(ptr_local = ?lhs.local, ?place, "skipped elaborated box deref");
                return;
            }
        }

        if let Rvalue::CopyForDeref(place) = rvalue {
            self.elaborated_locals.insert(lhs.local, place.clone());
            self.merge_drop_points(lhs.local, place.local);
            tracing::info!(ret_local = ?lhs.local, ?place, "skipped deref_copy");
            return;
        }

        if let Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, referent) = rvalue {
            // mutable borrow
            let mutbl = self.local_decls[lhs.local].mutability;
            let rty = self.mutable_borrow(stmt_idx, referent.clone());
            self.bind_local(lhs.local, rty, mutbl);
            return;
        }

        // new binding
        let mutbl = self.local_decls[lhs.local].mutability;
        let rty = self.rvalue_refined_type(rvalue.clone());
        self.bind_local(lhs.local, rty, mutbl);
    }

    fn analyze_statements(&mut self) {
        for (stmt_idx, mut stmt) in self.body.basic_blocks[self.basic_block]
            .statements
            .iter()
            .cloned()
            .enumerate()
        {
            self.reborrow_visitor().visit_statement(&mut stmt);
            self.replace_elaborated_locals_visitor()
                .visit_statement(&mut stmt);
            tracing::debug!(%stmt_idx, ?stmt);
            match &stmt.kind {
                StatementKind::Assign(x) => {
                    let (lhs, rvalue) = &**x;
                    self.analyze_assignment(lhs, rvalue, stmt_idx);
                }
                StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                _ => unimplemented!("stmt={:?}", stmt.kind),
            }
            for local in self.drop_points.after_statement(stmt_idx).iter() {
                tracing::info!(?local, ?stmt_idx, "implicitly dropped after statement");
                self.drop_local(local);
            }
        }
    }

    fn analyze_terminator(&mut self, expected_ret: &rty::RefinedType<Var>) {
        let mut term = self.body.basic_blocks[self.basic_block]
            .terminator()
            .clone();
        self.reborrow_visitor().visit_terminator(&mut term);
        self.replace_elaborated_locals_visitor()
            .visit_terminator(&mut term);
        tracing::debug!(term = ?term.kind);
        match &term.kind {
            TerminatorKind::Return => {
                self.type_return(&expected_ret);
            }
            TerminatorKind::Goto { target } => {
                self.type_goto(*target, &expected_ret);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.type_switch_int(
                    discr.clone(),
                    targets.clone(),
                    &expected_ret,
                    |a, target| {
                        for local in a.drop_points.after_terminator(&target).iter() {
                            tracing::info!(?local, ?target, "implicitly dropped for target");
                            a.drop_local(local);
                        }
                    },
                );
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let destination = match destination {
                    p if p.projection.len() == 0 => p.local,
                    _ => unimplemented!(),
                };
                if self.is_defined(destination) {
                    unimplemented!()
                }

                let decl = self.local_decls[destination].clone();
                let rty = self.mir_refined_ty(decl.ty);
                self.type_call(func.clone(), args.clone().into_iter().map(|a| a.node), &rty);
                self.bind_local(destination, rty, decl.mutability);
                if let Some(target) = target {
                    for local in self.drop_points.after_terminator(target).iter() {
                        tracing::info!(?local, "implicitly dropped after call");
                        self.drop_local(local);
                    }
                    self.type_goto(*target, &expected_ret);
                }
            }
            TerminatorKind::Drop { target, .. } => {
                for local in self.drop_points.after_terminator(target).iter() {
                    tracing::info!(?local, "dropped");
                    self.drop_local(local);
                }
                self.type_goto(*target, &expected_ret);
            }
            TerminatorKind::UnwindResume {} => {}
            _ => unimplemented!("term={:?}", term.kind),
        }
    }

    // TODO: remove this
    fn alloc_prophecies(&mut self) {
        for (stmt_idx, stmt) in self.body.basic_blocks[self.basic_block]
            .statements
            .iter()
            .enumerate()
        {
            if let Some((p, Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, _))) = stmt.kind.as_assign()
            {
                if p.projection.len() != 0 {
                    unimplemented!();
                }
                // TODO: is it appropriate to use builtin_deref here... maybe we should handle dereferencing logic in `refine`
                let inner_ty = self.local_decls[p.local].ty.builtin_deref(true).unwrap().ty;
                self.add_prophecy_var(stmt_idx, inner_ty);
            }
        }
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(
        ctx: &'ctx mut analyze::Analyzer<'tcx>,
        local_def_id: LocalDefId,
        basic_block: BasicBlock,
    ) -> Self {
        let tcx = ctx.tcx;
        let drop_points = DropPoints::default();
        let body = tcx.optimized_mir(local_def_id.to_def_id());
        let env = Env::default();
        let local_decls = body.local_decls.clone();
        let prophecy_vars = Default::default();
        let elaborated_locals = Default::default();
        Self {
            ctx,
            tcx,
            local_def_id,
            drop_points,
            basic_block,
            body,
            env,
            local_decls,
            prophecy_vars,
            elaborated_locals,
        }
    }

    pub fn drop_points(&mut self, drop_points: DropPoints) -> &mut Self {
        self.drop_points = drop_points;
        self
    }

    pub fn env(&mut self, env: Env) -> &mut Self {
        self.env = env;
        self
    }

    pub fn run(&mut self, expected: &BasicBlockType) {
        let expected_ret = self.bind_locals(&expected);
        self.alloc_prophecies();
        self.analyze_statements();
        self.analyze_terminator(&expected_ret);
    }
}
