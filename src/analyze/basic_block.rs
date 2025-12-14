use std::borrow::Cow;
use std::collections::HashMap;

use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_middle::mir::{
    self, BasicBlock, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{
    self, Assumption, BasicBlockType, Env, PlaceType, PlaceTypeBuilder, PlaceTypeVar, TempVarIdx,
    TypeBuilder, Var,
};
use crate::rty::{
    self, ClauseBuilderExt as _, ClauseScope as _, ShiftExistential as _, Subtyping as _,
};

mod drop_point;
mod visitor;
pub use drop_point::DropPoints;

pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,
    drop_points: DropPoints,
    basic_block: BasicBlock,
    body: Cow<'tcx, Body<'tcx>>,

    type_builder: TypeBuilder<'tcx>,
    env: Env,
    local_decls: IndexVec<Local, mir::LocalDecl<'tcx>>,
    // TODO: remove this
    prophecy_vars: HashMap<usize, TempVarIdx>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn is_defined(&self, local: Local) -> bool {
        self.env.contains_local(local)
    }

    fn is_mut_local(&self, local: Local) -> bool {
        self.local_decls[local].mutability.is_mut()
    }

    fn reborrow_visitor<'a>(&'a mut self) -> visitor::ReborrowVisitor<'a, 'tcx, 'ctx> {
        visitor::ReborrowVisitor::new(self)
    }

    fn basic_block_ty(&self, bb: BasicBlock) -> &BasicBlockType {
        self.ctx.basic_block_ty(self.local_def_id, bb)
    }

    fn bind_local(&mut self, local: Local, rty: rty::RefinedType<Var>) {
        let rty = if self.is_mut_local(local) {
            // elaboration:
            let refinement = rty
                .refinement
                .subst_value_var(|| chc::Term::var(rty::RefinedTypeVar::Value).box_current());
            let ty = rty::PointerType::own(rty.ty).into();
            rty::RefinedType::new(ty, refinement)
        } else {
            rty
        };
        if self.is_mut_local(local) || rty.ty.is_mut() {
            self.env.mut_bind(local, rty);
        } else {
            self.env.immut_bind(local, rty);
        }
    }

    // this can't be implmeneted in relate_sub_type because rty::FunctionType is free from Var
    fn relate_fn_sub_type(
        &mut self,
        got: rty::FunctionType,
        mut expected_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<Var>>,
        expected_ret: rty::RefinedType<Var>,
    ) -> Vec<chc::Clause> {
        let mut clauses = Vec::new();

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
            let param_sort = param_rty.ty.to_sort();
            if !param_sort.is_singleton() {
                builder.add_mapped_var(param_idx, param_sort);
            }
        }
        for ((param_idx, got_ty), expected_ty) in got.params.iter_enumerated().zip(&expected_args) {
            // TODO we can use relate_sub_refined_type here when we implemenented builder-aware relate_*
            let cs = builder
                .clone()
                .with_value_var(&got_ty.ty)
                .add_body(expected_ty.refinement.clone())
                .head(got_ty.refinement.clone());
            clauses.extend(cs);
            builder
                .with_mapped_value_var(param_idx)
                .add_body(expected_ty.refinement.clone());
            clauses.extend(builder.relate_sub_type(&expected_ty.ty, &got_ty.ty));
        }

        let cs = builder
            .with_value_var(&got.ret.ty)
            .add_body(got.ret.refinement)
            .head(expected_ret.refinement);
        clauses.extend(cs);
        clauses.extend(builder.relate_sub_type(&got.ret.ty, &expected_ret.ty));
        clauses
    }

    fn operand_type(&self, mut operand: Operand<'tcx>) -> PlaceType {
        if let Operand::Copy(p) | Operand::Move(p) = &mut operand {
            *p = self.elaborate_place(p);
        }
        let ty = self.env.operand_type(operand.clone());
        tracing::debug!(operand = ?operand, ty = %ty.display(), "operand_type");
        ty
    }

    fn rvalue_type(&mut self, rvalue: Rvalue<'tcx>) -> PlaceType {
        match rvalue {
            Rvalue::Use(operand) => self.operand_type(operand),
            Rvalue::UnaryOp(op, operand) => {
                let operand_ty = self.operand_type(operand);

                let mut builder = PlaceTypeBuilder::default();
                let (operand_ty, operand_term) = builder.subsume(operand_ty);
                match (&operand_ty, op) {
                    (rty::Type::Bool, mir::UnOp::Not) => {
                        builder.build(rty::Type::Bool, operand_term.not())
                    }
                    (rty::Type::Int, mir::UnOp::Neg) => {
                        builder.build(rty::Type::Int, operand_term.neg())
                    }
                    _ => unimplemented!("ty={}, op={:?}", operand_ty.display(), op),
                }
            }
            Rvalue::BinaryOp(op, operands) => {
                let (lhs, rhs) = *operands;
                let lhs_ty = self.operand_type(lhs);
                let rhs_ty = self.operand_type(rhs);

                let mut builder = PlaceTypeBuilder::default();
                let (lhs_ty, lhs_term) = builder.subsume(lhs_ty);
                let (_rhs_ty, rhs_term) = builder.subsume(rhs_ty);
                match (&lhs_ty, op) {
                    (rty::Type::Int, mir::BinOp::Add) => {
                        builder.build(lhs_ty, lhs_term.add(rhs_term))
                    }
                    (rty::Type::Int, mir::BinOp::Sub) => {
                        builder.build(lhs_ty, lhs_term.sub(rhs_term))
                    }
                    (rty::Type::Int, mir::BinOp::Mul) => {
                        builder.build(lhs_ty, lhs_term.mul(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Ge) => {
                        builder.build(rty::Type::Bool, lhs_term.ge(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Gt) => {
                        builder.build(rty::Type::Bool, lhs_term.gt(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Le) => {
                        builder.build(rty::Type::Bool, lhs_term.le(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Lt) => {
                        builder.build(rty::Type::Bool, lhs_term.lt(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Eq) => {
                        builder.build(rty::Type::Bool, lhs_term.eq(rhs_term))
                    }
                    (rty::Type::Int | rty::Type::Bool, mir::BinOp::Ne) => {
                        builder.build(rty::Type::Bool, lhs_term.ne(rhs_term))
                    }
                    _ => unimplemented!("ty={}, op={:?}", lhs_ty.display(), op),
                }
            }
            Rvalue::Ref(_, mir::BorrowKind::Shared, place) => {
                let ty = self.env.place_type(self.elaborate_place(&place));

                let mut builder = PlaceTypeBuilder::default();
                let (ty, term) = builder.subsume(ty);
                builder.build(rty::PointerType::immut_to(ty).into(), chc::Term::box_(term))
            }
            Rvalue::Aggregate(kind, fields) => {
                // elaboration: all fields are boxed
                let field_tys: Vec<_> = fields
                    .into_iter()
                    .map(|operand| self.operand_type(operand).boxed())
                    .collect();
                match *kind {
                    mir::AggregateKind::Adt(did, variant_id, args, _, _)
                        if self.tcx.def_kind(did) == DefKind::Enum =>
                    {
                        let adt = self.tcx.adt_def(did);
                        let ty_sym = refine::datatype_symbol(self.tcx, did);
                        let variant = adt.variant(variant_id);
                        let v_sym = refine::datatype_symbol(self.tcx, variant.def_id);

                        let enum_variant_def = self.ctx.find_enum_variant(&ty_sym, &v_sym).unwrap();
                        let variant_rtys = enum_variant_def
                            .field_tys
                            .clone()
                            .into_iter()
                            .map(|ty| rty::RefinedType::unrefined(ty.vacuous()));

                        let rty_args: IndexVec<_, _> = args
                            .types()
                            .map(|ty| {
                                self.type_builder
                                    .for_template(&mut self.ctx)
                                    .with_scope(&self.env)
                                    .build_refined(ty)
                            })
                            .collect();
                        for (field_pty, mut variant_rty) in
                            field_tys.clone().into_iter().zip(variant_rtys)
                        {
                            variant_rty.instantiate_ty_params(rty_args.clone());
                            let cs = self
                                .env
                                .relate_sub_refined_type(&field_pty.into(), &variant_rty.boxed());
                            self.ctx.extend_clauses(cs);
                        }

                        let sort_args: Vec<_> =
                            rty_args.iter().map(|rty| rty.ty.to_sort()).collect();
                        let ty = rty::EnumType::new(ty_sym.clone(), rty_args).into();

                        let mut builder = PlaceTypeBuilder::default();
                        let mut field_terms = Vec::new();
                        for field_ty in field_tys {
                            let (_, field_term) = builder.subsume(field_ty);
                            field_terms.push(field_term);
                        }
                        builder.build(
                            ty,
                            chc::Term::datatype_ctor(ty_sym, sort_args, v_sym, field_terms),
                        )
                    }
                    _ => PlaceType::tuple(field_tys),
                }
            }
            Rvalue::Cast(
                mir::CastKind::PointerCoercion(mir_ty::adjustment::PointerCoercion::ReifyFnPointer),
                operand,
                _ty,
            ) => {
                let func_ty = match operand.const_fn_def() {
                    Some((def_id, args)) => self
                        .ctx
                        .def_ty_with_args(def_id, args)
                        .expect("unknown def")
                        .ty
                        .clone(),
                    _ => unimplemented!(),
                };
                PlaceType::with_ty_and_term(func_ty.vacuous(), chc::Term::null())
            }
            Rvalue::Discriminant(place) => {
                let place = self.elaborate_place(&place);
                let ty = self.env.place_type(place);
                let sym = ty
                    .ty
                    .as_enum()
                    .expect("discriminant of non-enum")
                    .symbol
                    .clone();

                let mut builder = PlaceTypeBuilder::default();
                let (_, term) = builder.subsume(ty);
                builder.build(rty::Type::Int, chc::Term::datatype_discr(sym, term))
            }
            _ => unimplemented!(
                "rvalue={:?} ({:?})",
                rvalue,
                std::mem::discriminant(&rvalue)
            ),
        }
    }

    fn rvalue_refined_type(&mut self, rvalue: Rvalue<'tcx>) -> rty::RefinedType<Var> {
        let ty = self.rvalue_type(rvalue);

        // TODO: should we cover "is_singleton" ness in relate_* methods or here?
        if !ty.ty.to_sort().is_singleton() {
            return ty.into();
        }

        rty::RefinedType::unrefined(ty.ty)
    }

    fn type_rvalue(&mut self, rvalue: Rvalue<'tcx>, expected: &rty::RefinedType<Var>) {
        let got = self.rvalue_refined_type(rvalue);
        let clauses = self.env.relate_sub_refined_type(&got, expected);
        self.ctx.extend_clauses(clauses);
    }

    fn operand_refined_type(&mut self, operand: Operand<'tcx>) -> rty::RefinedType<Var> {
        self.rvalue_refined_type(Rvalue::Use(operand))
    }

    fn type_operand(&mut self, operand: Operand<'tcx>, expected: &rty::RefinedType<Var>) {
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
                    let arg_local_ty = self.env.local_type(arg_local);
                    // TODO: should we cover "is_singleton" ness in relate_* methods or here?
                    if !rty.ty.to_sort().is_singleton() {
                        arg_local_ty.into()
                    } else {
                        rty::RefinedType::unrefined(arg_local_ty.ty)
                    }
                } else {
                    rty::RefinedType::unrefined(rty.ty.clone().assert_closed().vacuous())
                }
            })
            .collect();
        let clauses =
            self.relate_fn_sub_type(bty.to_function_ty(), expected_args, expected_ret.clone());
        self.ctx.extend_clauses(clauses);
    }

    fn with_assumptions<F, T>(&mut self, assumptions: Vec<impl Into<Assumption>>, callback: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let old_env = self.env.clone();
        self.env.extend_assumptions(assumptions);
        let result = callback(self);
        self.env = old_env;
        result
    }

    fn with_assumption<F, T>(&mut self, assumption: impl Into<Assumption>, callback: F) -> T
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
        discr: Operand<'tcx>,
        targets: mir::SwitchTargets,
        expected_ret: &rty::RefinedType<Var>,
        mut callback: F,
    ) where
        F: FnMut(&mut Self, BasicBlock),
    {
        let discr_ty = self.operand_type(discr);
        let mut negations = Vec::new();
        for (val, bb) in targets.iter() {
            let val: i64 = val.try_into().unwrap();
            let target_term = match (val, &discr_ty.ty) {
                (0, rty::Type::Bool) => chc::Term::bool(false),
                (1, rty::Type::Bool) => chc::Term::bool(true),
                (n, rty::Type::Int) => chc::Term::int(n),
                _ => unimplemented!(),
            };

            let pos_assumption = {
                let mut builder = PlaceTypeBuilder::default();
                let (_, discr_term) = builder.subsume(discr_ty.clone());
                builder.push_formula(discr_term.equal_to(target_term.clone()));
                builder.build_assumption()
            };
            self.with_assumption(pos_assumption, |ecx| {
                callback(ecx, bb);
                ecx.type_goto(bb, expected_ret);
            });
            let neg_assumption = {
                let mut builder = PlaceTypeBuilder::default();
                let (_, discr_term) = builder.subsume(discr_ty.clone());
                builder.push_formula(discr_term.not_equal_to(target_term.clone()));
                builder.build_assumption()
            };
            negations.push(neg_assumption);
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

    fn is_mem_swap(&self, def_id: DefId) -> bool {
        // TODO: stop using diagnositc item for semantic purpose
        self.tcx.all_diagnostic_items(()).id_to_name.get(&def_id)
            == Some(&rustc_span::symbol::sym::mem_swap)
    }

    fn type_call<I>(&mut self, func: Operand<'tcx>, args: I, expected_ret: &rty::RefinedType<Var>)
    where
        I: IntoIterator<Item = Operand<'tcx>>,
    {
        // TODO: handle const_fn_def on Env side
        let func_ty = match func.const_fn_def() {
            // TODO: move this to well-known defs?
            Some((def_id, args)) if self.is_box_new(def_id) => {
                let inner_ty = self
                    .type_builder
                    .for_template(&mut self.ctx)
                    .build(args.type_at(0))
                    .vacuous();
                let param = rty::RefinedType::unrefined(inner_ty.clone());
                let ret_term =
                    chc::Term::box_(chc::Term::var(rty::FunctionParamIdx::from(0_usize)));
                let ret = rty::RefinedType::refined_with_term(
                    rty::PointerType::own(inner_ty).into(),
                    ret_term,
                );
                rty::FunctionType::new([param].into_iter().collect(), ret).into()
            }
            Some((def_id, args)) if self.is_mem_swap(def_id) => {
                let inner_ty = self.type_builder.build(args.type_at(0)).vacuous();
                let param1 =
                    rty::RefinedType::unrefined(rty::PointerType::mut_to(inner_ty.clone()).into());
                let param2 =
                    rty::RefinedType::unrefined(rty::PointerType::mut_to(inner_ty.clone()).into());
                let param1_var = rty::RefinedTypeVar::Free(rty::FunctionParamIdx::from(0_usize));
                let param2_var = rty::RefinedTypeVar::Free(rty::FunctionParamIdx::from(1_usize));
                let ret1 = chc::Term::var(param1_var)
                    .mut_current()
                    .equal_to(chc::Term::var(param2_var).mut_final());
                let ret2 = chc::Term::var(param2_var)
                    .mut_current()
                    .equal_to(chc::Term::var(param1_var).mut_final());
                let ret_formula = chc::Formula::Atom(ret1).and(chc::Formula::Atom(ret2));
                let ret = rty::RefinedType::new(rty::Type::unit(), ret_formula.into());
                rty::FunctionType::new([param1, param2].into_iter().collect(), ret).into()
            }
            Some((def_id, args)) => self
                .ctx
                .def_ty_with_args(def_id, args)
                .expect("unknown def")
                .ty
                .vacuous(),
            _ => self.operand_type(func.clone()).ty,
        };
        let expected_args: IndexVec<_, _> = args
            .into_iter()
            .map(|op| self.operand_refined_type(op))
            .collect();
        if let rty::Type::Function(func_ty) = func_ty {
            let clauses = self.relate_fn_sub_type(func_ty, expected_args, expected_ret.clone());
            self.ctx.extend_clauses(clauses);
        } else {
            panic!("unexpected def type: {:?}", func_ty);
        }
    }

    fn elaborate_place(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let mut projection = Vec::new();
        if self.is_mut_local(place.local) {
            projection.push(mir::PlaceElem::Deref);
        }
        for elem in place.projection {
            projection.push(elem);
            // elaboration: all fields are boxed
            if matches!(elem, mir::PlaceElem::Field { .. }) {
                projection.push(mir::PlaceElem::Deref);
            }
        }

        let mut p = *place;
        p.projection = self.tcx.mk_place_elems(&projection);
        p
    }

    fn elaborate_place_for_borrow(&self, place: &mir::Place<'tcx>) -> mir::Place<'tcx> {
        let mut place = self.elaborate_place(place);
        assert!(place.projection.last() == Some(&mir::ProjectionElem::Deref));
        place.projection = self
            .tcx
            .mk_place_elems(&place.projection.as_slice()[..place.projection.len() - 1]);
        place
    }

    fn assign_to_local(&mut self, local: Local, rvalue: mir::Rvalue<'tcx>) {
        let local_ty = self.env.local_type(local);
        let rvalue_ty = self.rvalue_type(rvalue);
        if !rvalue_ty.ty.to_sort().is_singleton() {
            let mut builder = PlaceTypeBuilder::default();
            let (_, local_term) = builder.subsume(local_ty);
            let (_, rvalue_term) = builder.subsume(rvalue_ty);
            builder.push_formula(local_term.mut_final().equal_to(rvalue_term));
            let assumption = builder.build_assumption();
            self.env.assume(assumption);
        }
    }

    fn drop_local(&mut self, local: Local) {
        self.env.drop_local(local);
    }

    fn add_prophecy_var(&mut self, statement_index: usize, ty: mir_ty::Ty<'tcx>) {
        let ty = self.type_builder.build(ty);
        let temp_var = self.env.push_temp_var(ty.vacuous());
        self.prophecy_vars.insert(statement_index, temp_var);
        tracing::debug!(stmt_idx = %statement_index, temp_var = ?temp_var, "add_prophecy_var");
    }

    fn mutable_borrow(
        &mut self,
        statement_index: usize,
        referent: mir::Place<'tcx>,
    ) -> rty::RefinedType<Var> {
        let temp_var = self.prophecy_vars[&statement_index];
        let place = self.elaborate_place_for_borrow(&referent);
        self.env.borrow_place(place, temp_var).into()
    }

    fn borrow_place_(
        &mut self,
        referent: mir::Place<'tcx>,
        prophecy_ty: mir_ty::Ty<'tcx>,
    ) -> rty::RefinedType<Var> {
        let prophecy_ty = self.type_builder.build(prophecy_ty);
        let prophecy = self.env.push_temp_var(prophecy_ty.vacuous());
        let place = self.elaborate_place_for_borrow(&referent);
        self.env.borrow_place(place, prophecy).into()
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
            // ReborrowVisitor must transform every assignment into this form
            assert!(lhs.projection.as_slice() == [mir::PlaceElem::Deref]);
            self.assign_to_local(lhs.local, rvalue.clone());
            return;
        }

        // definition
        assert!(lhs.projection.is_empty());

        if let Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, referent) = rvalue {
            // mutable borrow
            let rty = self.mutable_borrow(stmt_idx, *referent);
            self.bind_local(lhs.local, rty);
            return;
        }

        // new binding
        let rty = self.rvalue_refined_type(rvalue.clone());
        self.bind_local(lhs.local, rty);
    }

    fn terminator_is_drop_call(&self) -> Option<BasicBlock> {
        // XXX: hack
        let term = &self.body.basic_blocks[self.basic_block].terminator().kind;
        if let TerminatorKind::Call { func, target, .. } = term {
            if let Some((def_id, _)) = func.const_fn_def() {
                return (self.tcx.def_path_str(def_id) == "std::ops::Drop::drop")
                    .then(|| target.unwrap());
            }
        }
        None
    }

    fn analyze_statements(&mut self) {
        for local in self.drop_points.before_statements.clone() {
            tracing::info!(?local, "implicitly dropped before statements");
            self.drop_local(local);
        }
        let statements = self.body.basic_blocks[self.basic_block].statements.clone();
        for (stmt_idx, mut stmt) in statements.iter().cloned().enumerate() {
            if stmt_idx == statements.len() - 1 && self.terminator_is_drop_call().is_some() {
                tracing::warn!(%stmt_idx, ?stmt, "skip before std::ops::Drop");
                continue;
            }
            self.reborrow_visitor().visit_statement(&mut stmt);
            tracing::debug!(%stmt_idx, ?stmt);
            match &stmt.kind {
                StatementKind::Assign(x) => {
                    let (lhs, rvalue) = &**x;
                    self.analyze_assignment(lhs, rvalue, stmt_idx);
                }
                StatementKind::Nop
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_) => {}
                _ => unimplemented!("stmt={:?}", stmt.kind),
            }
            for local in self.drop_points.after_statement(stmt_idx).iter() {
                tracing::info!(?local, ?stmt_idx, "implicitly dropped after statement");
                self.drop_local(local);
            }
        }
    }

    fn elaborated_terminator(&mut self) -> mir::Terminator<'tcx> {
        let mut term = self.body.basic_blocks[self.basic_block]
            .terminator()
            .clone();
        if let Some(target) = self.terminator_is_drop_call() {
            tracing::warn!(?term, "skip std::ops::Drop");
            return mir::Terminator {
                kind: TerminatorKind::Goto { target },
                source_info: term.source_info,
            };
        }
        self.reborrow_visitor().visit_terminator(&mut term);
        tracing::debug!(term = ?term.kind);
        term
    }

    #[tracing::instrument(skip(self), fields(term = ?term.kind))]
    fn analyze_terminator_binds(&mut self, term: &mir::Terminator<'tcx>) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        {
            let destination = match destination {
                p if p.projection.len() == 0 => p.local,
                _ => unimplemented!(),
            };
            if self.is_defined(destination) {
                unimplemented!()
            }

            let decl = self.local_decls[destination].clone();
            let rty = self
                .type_builder
                .for_template(&mut self.ctx)
                .with_scope(&self.env)
                .build_refined(decl.ty);
            self.type_call(func.clone(), args.clone().into_iter().map(|a| a.node), &rty);
            self.bind_local(destination, rty);
        }
    }

    #[tracing::instrument(skip(self, expected_ret), fields(term = ?term.kind))]
    fn analyze_terminator_goto(
        &mut self,
        term: &mir::Terminator<'tcx>,
        expected_ret: &rty::RefinedType<Var>,
    ) {
        match &term.kind {
            TerminatorKind::Return => {
                self.type_return(expected_ret);
            }
            TerminatorKind::Goto { target } => {
                self.type_goto(*target, expected_ret);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.type_switch_int(discr.clone(), targets.clone(), expected_ret, |a, target| {
                    for local in a.drop_points.after_terminator(&target).iter() {
                        tracing::info!(?local, ?target, "implicitly dropped for target");
                        a.drop_local(local);
                    }
                });
            }
            TerminatorKind::Call { target, .. } => {
                if let Some(target) = target {
                    for local in self.drop_points.after_terminator(target).iter() {
                        tracing::info!(?local, "implicitly dropped after call");
                        self.drop_local(local);
                    }
                    self.type_goto(*target, expected_ret);
                }
            }
            TerminatorKind::Drop { target, .. } => {
                for local in self.drop_points.after_terminator(target).iter() {
                    tracing::info!(?local, "dropped");
                    self.drop_local(local);
                }
                self.type_goto(*target, expected_ret);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                for local in self.drop_points.after_terminator(target).iter() {
                    tracing::info!(?local, "dropped");
                    self.drop_local(local);
                }
                self.type_operand(
                    cond.clone(),
                    &rty::RefinedType::refined_with_term(
                        rty::Type::bool(),
                        chc::Term::bool(*expected),
                    ),
                );
                self.type_goto(*target, expected_ret);
            }
            TerminatorKind::UnwindResume {} => {}
            TerminatorKind::Unreachable {} => {}
            _ => unimplemented!("term={:?}", term.kind),
        }
    }

    #[tracing::instrument(skip(self))]
    fn ret_template(&mut self) -> rty::RefinedType<Var> {
        let ret_ty = self.body.local_decls[mir::RETURN_PLACE].ty;
        self.type_builder
            .for_template(&mut self.ctx)
            .with_scope(&self.env)
            .build_refined(ret_ty)
    }

    // TODO: remove this
    fn alloc_prophecies(&mut self) {
        for (stmt_idx, stmt) in self.body.basic_blocks[self.basic_block]
            .statements
            .clone()
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

/// Turns [`rty::RefinedType<Var>`] into [`rty::RefinedType<T>`].
///
/// We sometimes need to replace [`rty::RefinedTypeVar<Var>`] with [`rty::RefinedTypeVar<T>`].
/// In [`analyze::basic_block`] module, `T` is [`rty::FunctionParamIdx`]. The type we get as
/// a function result is obtained as [`rty::RefinedTypeVar<Var>`], but we need to express it using
/// only function parameters for the subtyping. [`UnbindAtoms`] holds the relation between
/// the function parameters and their representaion under the environment and
/// let the type in environment be expressed only under the function parameters using existentials.
#[derive(Debug, Clone)]
pub struct UnbindAtoms<T> {
    existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
    body: chc::Body<rty::RefinedTypeVar<Var>>,
    target_equations: Vec<(rty::RefinedTypeVar<T>, chc::Term<rty::RefinedTypeVar<Var>>)>,
}

impl<T> Default for UnbindAtoms<T> {
    fn default() -> Self {
        UnbindAtoms {
            existentials: Default::default(),
            body: Default::default(),
            target_equations: Default::default(),
        }
    }
}

impl<T> UnbindAtoms<T> {
    pub fn push(&mut self, target: rty::RefinedTypeVar<T>, var_ty: PlaceType) {
        self.body.push_conj(
            var_ty
                .formula
                .map_var(|v| v.shift_existential(self.existentials.len()).into()),
        );
        self.target_equations.push((
            target,
            var_ty
                .term
                .map_var(|v| v.shift_existential(self.existentials.len()).into()),
        ));
        self.existentials.extend(var_ty.existentials);
    }

    pub fn unbind(mut self, env: &Env, ty: rty::RefinedType<Var>) -> rty::RefinedType<T> {
        let rty::RefinedType {
            ty: src_ty,
            refinement,
        } = ty;
        let rty::Refinement { existentials, body } = refinement;

        self.body
            .push_conj(body.map_var(|v| v.shift_existential(self.existentials.len())));
        self.existentials.extend(existentials);

        let mut substs = HashMap::new();
        for (v, sort) in env.dependencies() {
            let ev = self.existentials.push(sort);
            substs.insert(v, ev);
        }

        let mut body = self.body.map_var(|v| match v {
            rty::RefinedTypeVar::Value => rty::RefinedTypeVar::Value,
            rty::RefinedTypeVar::Free(v) => rty::RefinedTypeVar::Existential(substs[&v]),
            rty::RefinedTypeVar::Existential(ev) => rty::RefinedTypeVar::Existential(ev),
        });
        body.push_conj(
            self.target_equations
                .into_iter()
                .map(|(t, term)| {
                    chc::Term::var(t).equal_to(term.map_var(|v| match v {
                        rty::RefinedTypeVar::Value => rty::RefinedTypeVar::Value,
                        rty::RefinedTypeVar::Free(v) => {
                            rty::RefinedTypeVar::Existential(substs[&v])
                        }
                        rty::RefinedTypeVar::Existential(ev) => {
                            rty::RefinedTypeVar::Existential(ev)
                        }
                    }))
                })
                .collect::<Vec<_>>(),
        );

        let refinement = rty::Refinement::new(self.existentials, body);
        // TODO: polymorphic datatypes: template needed?
        rty::RefinedType::new(src_ty.assert_closed().vacuous(), refinement)
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    #[tracing::instrument(skip(self, expected_params))]
    fn bind_locals(
        &mut self,
        expected_params: &IndexVec<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    ) {
        let mut param_terms = HashMap::<rty::FunctionParamIdx, chc::Term<PlaceTypeVar>>::new();
        let mut assumption = Assumption::default();

        let bb_ty = self.basic_block_ty(self.basic_block).clone();
        let params = &bb_ty.as_ref().params;
        assert!(params.len() >= 1);
        for (param_idx, param_rty) in params.iter_enumerated() {
            let param_ty = &param_rty.ty;
            if let Some(local) = bb_ty.local_of_param(param_idx) {
                let rty = rty::RefinedType::unrefined(param_ty.clone().subst_var(|v| {
                    param_terms[&v].clone().map_var(|v| match v {
                        PlaceTypeVar::Var(v) => v,
                        // TODO
                        _ => unimplemented!(),
                    })
                }));
                if bb_ty.mutbl_of_param(param_idx).unwrap().is_mut() || rty.ty.is_mut() {
                    self.env.mut_bind(local, rty);
                } else {
                    self.env.immut_bind(local, rty);
                }
                let param_sort = param_ty.to_sort();
                if param_sort.is_singleton() {
                    continue;
                }

                let local_ty = self.env.local_type(local);
                assumption.body.push_conj(
                    local_ty
                        .formula
                        .map_var(|v| v.shift_existential(assumption.existentials.len())),
                );
                let term = local_ty
                    .term
                    .map_var(|v| v.shift_existential(assumption.existentials.len()));
                assumption.existentials.extend(local_ty.existentials);
                param_terms.insert(param_idx, term);
            }
        }

        for (idx, param) in expected_params.iter_enumerated() {
            let rty::Refinement { existentials, body } = param.refinement.clone();
            assumption.body.push_conj(body.subst_var(|v| match v {
                rty::RefinedTypeVar::Value => param_terms[&idx].clone(),
                rty::RefinedTypeVar::Free(v) => param_terms[&v].clone(),
                rty::RefinedTypeVar::Existential(ev) => chc::Term::var(PlaceTypeVar::Existential(
                    ev + assumption.existentials.len(),
                )),
            }));
            assumption.existentials.extend(existentials);
        }

        self.env.assume(assumption);
    }

    fn unbind_atoms(&self) -> UnbindAtoms<rty::FunctionParamIdx> {
        let bb_ty = self.basic_block_ty(self.basic_block);
        let mut atoms = UnbindAtoms::default();
        if self.is_defined(mir::RETURN_PLACE) && !bb_ty.as_ref().ret.ty.to_sort().is_singleton() {
            let r_ty = self.operand_type(Operand::Move(mir::RETURN_PLACE.into()));
            atoms.push(rty::RefinedTypeVar::Value, r_ty);
        }
        for (param_idx, param_ty) in bb_ty.as_ref().params.iter_enumerated() {
            if param_ty.ty.to_sort().is_singleton() {
                continue;
            }
            if let Some(local) = bb_ty.local_of_param(param_idx) {
                let local_ty = self.env.local_type(local);
                atoms.push(rty::RefinedTypeVar::Free(param_idx), local_ty);
            }
        }
        atoms
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
        let body = Cow::Borrowed(tcx.optimized_mir(local_def_id.to_def_id()));
        let env = ctx.new_env();
        let local_decls = body.local_decls.clone();
        let prophecy_vars = Default::default();
        let type_builder = TypeBuilder::new(tcx, local_def_id.to_def_id());
        Self {
            ctx,
            tcx,
            local_def_id,
            drop_points,
            basic_block,
            body,
            type_builder,
            env,
            local_decls,
            prophecy_vars,
        }
    }

    pub fn drop_points(&mut self, drop_points: DropPoints) -> &mut Self {
        self.drop_points = drop_points;
        self
    }

    pub fn body(&mut self, body: Body<'tcx>) -> &mut Self {
        self.local_decls = body.local_decls.clone();
        self.body = Cow::Owned(body);
        self
    }

    pub fn local_decls(&mut self, local_decls: IndexVec<Local, mir::LocalDecl<'tcx>>) -> &mut Self {
        self.local_decls = local_decls;
        self
    }

    pub fn env(&mut self, env: Env) -> &mut Self {
        self.env = env;
        self
    }

    pub fn run(&mut self, expected: &BasicBlockType) {
        let span = tracing::info_span!("bb", bb = ?self.basic_block);
        let _guard = span.enter();

        let params = expected.as_ref().params.clone();
        self.bind_locals(&params);
        let unbind_atoms = self.unbind_atoms();
        self.alloc_prophecies();
        self.analyze_statements();

        let term = self.elaborated_terminator();
        self.analyze_terminator_binds(&term);
        let ret_template = self.ret_template();
        self.analyze_terminator_goto(&term, &ret_template);

        let got_ret_ty = unbind_atoms.unbind(&self.env, ret_template);
        let got_ty = rty::FunctionType::new(params, got_ret_ty).into_closed_ty();
        let clauses = self
            .env
            .relate_sub_type(&got_ty, &expected.to_function_ty().into_closed_ty());
        self.ctx.extend_clauses(clauses);
    }
}
