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
    Assumption, BasicBlockType, BasicBlockTypeParamKind, PlaceType, PlaceTypeBuilder, PlaceTypeVar,
    TempVarIdx, TypeBuilder, Var,
};
use crate::rty::{
    self, ClauseBuilderExt as _, ClauseScope as _, ShiftExistential as _, Subtyping as _,
};

mod drop_point;
mod visitor;
pub use drop_point::DropPoints;

/// Whether a basic block needs a precondition of its own, rather than
/// inheriting its predecessor's outgoing env state.
///
/// This holds for `START_BLOCK` (whose precondition comes from the function
/// signature, not a predecessor) and for every block reached by more than one
/// CFG edge — i.e. join points with multiple predecessors, or multiple edges
/// from a single predecessor (e.g. `SwitchInt` arms that share a target).
///
/// A block with a unique incoming edge can inherit that edge's env state, so it
/// needs no precondition of its own. A block that does need one currently models
/// it with a fresh predicate variable; this is also the set of CFG cutpoints, so
/// it cuts every cycle (a loop header always has in-degree >= 2).
pub fn needs_own_precondition(body: &Body<'_>, bb: BasicBlock) -> bool {
    if bb == mir::START_BLOCK {
        return true;
    }
    let preds = &body.basic_blocks.predecessors()[bb];
    if preds.len() != 1 {
        return true;
    }
    let pred = preds[0];
    let pred_term = body.basic_blocks[pred].terminator();
    pred_term.successors().filter(|s| *s == bb).count() > 1
}

/// Converts the current env state into a `Refinement<FunctionParamIdx>` to be
/// used as the inherited precondition of a successor block.
///
/// Each [`push`](PrecondCapture::push) records that a function parameter (or the
/// last param's value) equals an env-side [`PlaceType`];
/// [`push_env_state`](PrecondCapture::push_env_state) folds in the env's refined
/// vars and accumulated assumptions; [`finish`](PrecondCapture::finish)
/// existentially closes over the env-side variables and emits the refinement.
///
/// This is the focused successor of the former `UnbindAtoms`, specialized to the
/// only case that still needs it: capturing a predecessor's env into a goto
/// target's precondition.
#[derive(Default)]
struct PrecondCapture {
    existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
    body: chc::Body<rty::RefinedTypeVar<Var>>,
    target_equations: Vec<(
        rty::RefinedTypeVar<rty::FunctionParamIdx>,
        chc::Term<rty::RefinedTypeVar<Var>>,
    )>,
}

impl PrecondCapture {
    fn push(&mut self, target: rty::RefinedTypeVar<rty::FunctionParamIdx>, var_ty: PlaceType) {
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

    fn push_env_state(&mut self, env: &analyze::Env) {
        for (var, rty) in env.vars() {
            let base = self.existentials.len();
            self.existentials
                .extend(rty.refinement.existentials.iter().cloned());
            let body = rty.refinement.body.clone().map_var(|v| match v {
                rty::RefinedTypeVar::Value => rty::RefinedTypeVar::Free(var),
                rty::RefinedTypeVar::Free(v) => rty::RefinedTypeVar::Free(v),
                rty::RefinedTypeVar::Existential(ev) => rty::RefinedTypeVar::Existential(ev + base),
            });
            self.body.push_conj(body);
        }
        for assumption in env.assumptions() {
            let base = self.existentials.len();
            self.existentials
                .extend(assumption.existentials.iter().cloned());
            let body = assumption.body.clone().map_var(|v| match v {
                PlaceTypeVar::Var(v) => rty::RefinedTypeVar::Free(v),
                PlaceTypeVar::Existential(ev) => rty::RefinedTypeVar::Existential(ev + base),
            });
            self.body.push_conj(body);
        }
    }

    fn finish(mut self, env: &analyze::Env) -> rty::Refinement<rty::FunctionParamIdx> {
        let mut substs = HashMap::new();
        for (v, sort) in env.dependencies() {
            let ev = self.existentials.push(sort);
            substs.insert(v, ev);
        }

        let map = |v| match v {
            rty::RefinedTypeVar::Value => rty::RefinedTypeVar::Value,
            rty::RefinedTypeVar::Free(v) => rty::RefinedTypeVar::Existential(substs[&v]),
            rty::RefinedTypeVar::Existential(ev) => rty::RefinedTypeVar::Existential(ev),
        };
        let mut body = self.body.map_var(map);
        for (t, term) in self.target_equations {
            body.push_conj(chc::Term::var(t).equal_to(term.map_var(map)));
        }
        rty::Refinement::new(self.existentials, body)
    }
}

pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,
    drop_points: DropPoints,
    basic_block: BasicBlock,
    body: Cow<'tcx, Body<'tcx>>,

    type_builder: TypeBuilder<'tcx>,
    env: analyze::Env,
    local_decls: IndexVec<Local, mir::LocalDecl<'tcx>>,
    // TODO: remove this
    prophecy_vars: HashMap<usize, TempVarIdx>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn ctx(&self) -> &analyze::Analyzer<'tcx> {
        &*self.ctx
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

    fn rust_call_visitor<'a>(&'a mut self) -> visitor::RustCallVisitor<'a, 'tcx, 'ctx> {
        visitor::RustCallVisitor::new(self)
    }

    fn basic_block_ty_with_precondition(&self, bb: BasicBlock) -> &BasicBlockType {
        self.ctx
            .basic_block_ty_with_precondition(self.local_def_id, bb)
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
        expected_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<Var>>,
        expected_ret: rty::RefinedType<Var>,
    ) -> Vec<chc::Clause> {
        let mut clauses = Vec::new();

        tracing::debug!(
            got = %got.display(),
            expected = %crate::pretty::FunctionType::new(&expected_args, &expected_ret).display(),
            "fn_sub_type"
        );

        let mut builder = self.env.build_clause();
        let cs = self.relate_fn_param_sub_types_with_builder(
            got.params,
            expected_args,
            &mut builder,
            got.abi,
        );
        clauses.extend(cs);

        let cs = builder
            .with_value_var(&got.ret.ty)
            .add_body(got.ret.refinement)
            .head(expected_ret.refinement);
        clauses.extend(cs);

        clauses.extend(builder.relate_sub_type(&got.ret.ty, &expected_ret.ty));
        clauses
    }

    fn relate_fn_param_sub_types(
        &mut self,
        got_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
        expected_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<Var>>,
    ) -> Vec<chc::Clause> {
        let mut builder = self.env.build_clause();
        self.relate_fn_param_sub_types_with_builder(
            got_args,
            expected_args,
            &mut builder,
            rty::FunctionAbi::Rust,
        )
    }

    fn relate_fn_param_sub_types_with_builder(
        &mut self,
        got_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
        mut expected_args: IndexVec<rty::FunctionParamIdx, rty::RefinedType<Var>>,
        builder: &mut chc::ClauseBuilder,
        abi: rty::FunctionAbi,
    ) -> Vec<chc::Clause> {
        let mut clauses = Vec::new();

        match abi {
            rty::FunctionAbi::Rust => {
                if expected_args.is_empty() {
                    // elaboration: we need at least one predicate variable in parameter (see mir_function_ty_impl)
                    expected_args.push(rty::RefinedType::unrefined(rty::Type::unit()).vacuous());
                }
            }
            rty::FunctionAbi::RustCall => {
                // &Closure, { v: (own i32, own bool) | v = (<0>, <false>) }
                // =>
                // &Closure, { v: i32 | (<v>, _) = (<0>, <false>) }, { v: bool | (_, <v>) = (<0>, <false>) }

                let rty::RefinedType { ty, mut refinement } =
                    expected_args.pop().expect("rust-call last arg");
                let ty = ty.into_tuple().expect("rust-call last arg is tuple");
                let mut replacement_tuple = Vec::new(); // will be (<v>, _) or (_, <v>)
                for elem in &ty.elems {
                    let existential = refinement.existentials.push(elem.ty.to_sort());
                    replacement_tuple.push(chc::Term::var(rty::RefinedTypeVar::Existential(
                        existential,
                    )));
                }

                for (i, elem) in ty.elems.into_iter().enumerate() {
                    // all tuple elements are boxed during the translation to rty::Type
                    let mut param_ty = elem.deref();
                    param_ty
                        .refinement
                        .push_conj(refinement.clone().subst_value_var(|| {
                            let mut value_elems = replacement_tuple.clone();
                            value_elems[i] = chc::Term::var(rty::RefinedTypeVar::Value).boxed();
                            chc::Term::tuple(value_elems)
                        }));
                    expected_args.push(param_ty);
                }

                tracing::info!(
                    expected = %crate::pretty::FunctionParams::new(&expected_args).display(),
                    "rust-call expanded",
                );
            }
        }

        assert!(got_args.len() == expected_args.len());
        // TODO: check stys are equal
        for (param_idx, param_rty) in got_args.iter_enumerated() {
            let param_sort = param_rty.ty.to_sort();
            if !param_sort.is_singleton() {
                builder.add_mapped_var(param_idx, param_sort);
            }
        }
        for ((param_idx, got_ty), expected_ty) in got_args.iter_enumerated().zip(&expected_args) {
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

        clauses
    }

    fn const_bytes_ty(
        &self,
        ty: mir_ty::Ty<'tcx>,
        alloc: mir::interpret::ConstAllocation,
        range: std::ops::Range<usize>,
    ) -> PlaceType {
        let bytes = alloc
            .inner()
            .inspect_with_uninit_and_ptr_outside_interpreter(range.clone());
        let typing_env = self.body.typing_env(self.tcx);
        let layout = self.tcx.layout_of(typing_env.as_query_input(ty)).unwrap();
        let lcx = mir_ty::layout::LayoutCx::new(self.tcx, typing_env);
        match ty.kind() {
            mir_ty::TyKind::Str => {
                let content = std::str::from_utf8(bytes).unwrap();
                PlaceType::with_ty_and_term(
                    rty::Type::string(),
                    chc::Term::string(content.to_owned()),
                )
            }
            mir_ty::TyKind::Bool => {
                PlaceType::with_ty_and_term(rty::Type::bool(), chc::Term::bool(bytes[0] != 0))
            }
            mir_ty::TyKind::Int(_) => {
                // TODO: see target endianness
                let val = match bytes.len() {
                    1 => i8::from_ne_bytes(bytes.try_into().unwrap()) as i64,
                    2 => i16::from_ne_bytes(bytes.try_into().unwrap()) as i64,
                    4 => i32::from_ne_bytes(bytes.try_into().unwrap()) as i64,
                    8 => i64::from_ne_bytes(bytes.try_into().unwrap()),
                    _ => unimplemented!("const int bytes len: {}", bytes.len()),
                };
                PlaceType::with_ty_and_term(rty::Type::int(), chc::Term::int(val))
            }
            mir_ty::TyKind::Tuple(tys) => {
                let mut pts = Vec::new();
                for (i, field_ty) in tys.iter().enumerate() {
                    let field = layout.field(&lcx, i);
                    let start = range.start + layout.fields.offset(i).bytes() as usize;
                    let end = start + field.size.bytes() as usize;
                    let pt = self.const_bytes_ty(field_ty, alloc, start..end);
                    pts.push(pt.boxed());
                }
                PlaceType::tuple(pts)
            }
            mir_ty::TyKind::Adt(def, args) if def.is_struct() => {
                let mut pts = Vec::new();
                for (i, field_def) in def.all_fields().enumerate() {
                    let field = layout.field(&lcx, i);
                    let start = range.start + layout.fields.offset(i).bytes() as usize;
                    let end = start + field.size.bytes() as usize;
                    let field_ty = field_def.ty(self.tcx, args);
                    let pt = self.const_bytes_ty(field_ty, alloc, start..end);
                    pts.push(pt.boxed());
                }
                PlaceType::tuple(pts)
            }
            _ => unimplemented!("const bytes ty: {:?}", ty),
        }
    }

    fn const_value_ty(&self, val: &mir::ConstValue, ty: &mir_ty::Ty<'tcx>) -> PlaceType {
        use mir::{interpret::Scalar, ConstValue, Mutability};
        match (ty.kind(), val) {
            (
                mir_ty::TyKind::Int(_) | mir_ty::TyKind::Uint(_),
                ConstValue::Scalar(Scalar::Int(val)),
            ) => {
                let val = val.to_int(val.size());
                PlaceType::with_ty_and_term(
                    rty::Type::int(),
                    chc::Term::int(val.try_into().unwrap()),
                )
            }
            (mir_ty::TyKind::Bool, ConstValue::Scalar(Scalar::Int(val))) => {
                PlaceType::with_ty_and_term(
                    rty::Type::bool(),
                    chc::Term::bool(val.try_to_bool().unwrap()),
                )
            }
            (mir_ty::TyKind::Tuple(tys), _) if tys.is_empty() => {
                PlaceType::with_ty_and_term(rty::Type::unit(), chc::Term::tuple(vec![]))
            }
            (mir_ty::TyKind::Closure(_, args), _) if args.as_closure().upvar_tys().is_empty() => {
                PlaceType::with_ty_and_term(rty::Type::unit(), chc::Term::tuple(vec![]))
            }
            (_, ConstValue::ZeroSized) => {
                PlaceType::with_ty_and_term(rty::Type::unit(), chc::Term::tuple(vec![]))
            }
            (
                mir_ty::TyKind::Ref(_, elem, Mutability::Not),
                ConstValue::Scalar(Scalar::Ptr(ptr, _)),
            ) => {
                let (prov, offset) = ptr.prov_and_relative_offset();
                let global_alloc = self.tcx.global_alloc(prov.alloc_id());
                match global_alloc {
                    mir::interpret::GlobalAlloc::Memory(alloc) => {
                        let typing_env = self.body.typing_env(self.tcx);
                        let layout = self
                            .tcx
                            .layout_of(typing_env.as_query_input(*elem))
                            .unwrap();
                        let size = layout.size;
                        let range =
                            offset.bytes() as usize..(offset.bytes() + size.bytes()) as usize;
                        self.const_bytes_ty(*elem, alloc, range).immut()
                    }
                    _ => unimplemented!("const ptr alloc: {:?}", global_alloc),
                }
            }
            (
                mir_ty::TyKind::Ref(_, elem, Mutability::Not),
                ConstValue::Slice { alloc_id, meta },
            ) => {
                let end = (*meta).try_into().unwrap();
                let global_alloc = self.tcx.global_alloc(*alloc_id);
                let mir::interpret::GlobalAlloc::Memory(alloc) = global_alloc else {
                    unimplemented!("const slice alloc: {:?}", global_alloc);
                };
                self.const_bytes_ty(*elem, alloc, 0..end).immut()
            }
            _ => unimplemented!("const: {:?}, ty: {:?}", val, ty),
        }
    }

    fn const_ty(&self, const_: &mir::Const<'tcx>) -> PlaceType {
        match const_ {
            mir::Const::Val(val, ty) => self.const_value_ty(val, ty),
            mir::Const::Unevaluated(unevaluated, ty) => {
                // since all constants are immutable in current setup,
                // it should be okay to evaluate them here on-the-fly
                let typing_env = self.body.typing_env(self.tcx);
                let val = self
                    .tcx
                    .const_eval_resolve(typing_env, *unevaluated, rustc_span::DUMMY_SP)
                    .unwrap();
                self.const_value_ty(&val, ty)
            }
            _ => unimplemented!("const: {:?}", const_),
        }
    }

    fn operand_type(&self, mut operand: Operand<'tcx>) -> PlaceType {
        if let Operand::Copy(p) | Operand::Move(p) = &mut operand {
            *p = self.elaborate_place(p);
        }
        let ty = match &operand {
            Operand::Copy(place) | Operand::Move(place) => self.env.place_type(*place),
            Operand::Constant(operand) => self.const_ty(&operand.const_),
        };
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
                    mir::AggregateKind::Adt(did, variant_idx, args, _, _)
                        if self.tcx.def_kind(did) == DefKind::Enum =>
                    {
                        let enum_def = self.ctx.get_or_register_enum_def(did);
                        let variant_def = &enum_def.variants[variant_idx];
                        let variant_rtys = variant_def
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
                        let ty = rty::EnumType::new(enum_def.name.clone(), rty_args).into();

                        let mut builder = PlaceTypeBuilder::default();
                        let mut field_terms = Vec::new();
                        for field_ty in field_tys {
                            let (_, field_term) = builder.subsume(field_ty);
                            field_terms.push(field_term);
                        }
                        builder.build(
                            ty,
                            chc::Term::datatype_ctor(
                                enum_def.name,
                                sort_args,
                                variant_def.name.clone(),
                                field_terms,
                            ),
                        )
                    }
                    _ => PlaceType::tuple(field_tys),
                }
            }
            Rvalue::Cast(
                mir::CastKind::PointerCoercion(
                    mir_ty::adjustment::PointerCoercion::ReifyFnPointer,
                    _,
                ),
                operand,
                _ty,
            ) => {
                let func_ty = match operand.const_fn_def() {
                    Some((def_id, args)) => self.fn_def_ty(def_id, args),
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

    fn type_return(
        &mut self,
        expected_fn: &rty::FunctionType,
        outer_fn_param_vars: &HashMap<rty::FunctionParamIdx, Var>,
    ) {
        let mut builder = self.env.build_clause();
        let mut clauses = Vec::new();

        for (&param_idx, &param_var) in outer_fn_param_vars {
            let sort = expected_fn.params[param_idx].ty.to_sort();
            if sort.is_singleton() {
                continue;
            }
            builder.add_mapped_var(param_idx, sort);
            let tv_param_idx = builder.mapped_var(param_idx);
            let tv_param_var = builder.mapped_var(param_var);
            builder.add_body(chc::Term::var(tv_param_idx).equal_to(chc::Term::var(tv_param_var)));
        }

        let ret_rty = self.operand_refined_type(Operand::Move(mir::RETURN_PLACE.into()));

        let cs = builder
            .with_value_var(&expected_fn.ret.ty)
            .add_body(ret_rty.refinement)
            .head(expected_fn.ret.refinement.clone());
        clauses.extend(cs);
        clauses.extend(builder.relate_sub_type(&ret_rty.ty, &expected_fn.ret.ty));

        self.ctx.extend_clauses(clauses);
    }

    fn type_goto(
        &mut self,
        bb: BasicBlock,
        outer_fn_param_vars: &HashMap<rty::FunctionParamIdx, Var>,
    ) {
        if !needs_own_precondition(&self.body, bb) {
            self.install_inherited_bb_ty(bb, outer_fn_param_vars);
            return;
        }
        let bty = self.basic_block_ty_with_precondition(bb);
        let expected_args: IndexVec<_, _> = bty
            .as_ref()
            .params
            .iter_enumerated()
            .map(|(param_idx, rty)| {
                match bty.param_kind(param_idx) {
                    BasicBlockTypeParamKind::Local(arg_local, _) => {
                        let arg_local_ty = self.env.local_type(arg_local);
                        // TODO: should we cover "is_singleton" ness in relate_* methods or here?
                        if !rty.ty.to_sort().is_singleton() {
                            arg_local_ty.into()
                        } else {
                            rty::RefinedType::unrefined(arg_local_ty.ty)
                        }
                    }
                    BasicBlockTypeParamKind::OuterFnParam(outer_idx) => {
                        let outer_fn_param_var = outer_fn_param_vars[&outer_idx];
                        let pty = PlaceType::with_ty_and_term(
                            rty.ty.clone().assert_closed().vacuous(),
                            chc::Term::var(outer_fn_param_var),
                        );
                        pty.into()
                    }
                    BasicBlockTypeParamKind::Synthetic => {
                        rty::RefinedType::unrefined(rty.ty.clone().assert_closed().vacuous())
                    }
                }
            })
            .collect();
        let clauses = self.relate_fn_param_sub_types(bty.as_ref().params.clone(), expected_args);
        self.ctx.extend_clauses(clauses);
    }

    /// Materializes the `BasicBlockType` for a target that inherits its
    /// precondition by building its (pvar-free) layout and overwriting the last
    /// param's refinement with the current env state.
    fn install_inherited_bb_ty(
        &mut self,
        bb: BasicBlock,
        outer_fn_param_vars: &HashMap<rty::FunctionParamIdx, Var>,
    ) {
        let bty = self.ctx.basic_block_ty(self.local_def_id, bb);

        let mut capture = PrecondCapture::default();
        for (param_idx, param_rty) in bty.as_ref().params.iter_enumerated() {
            if param_rty.ty.to_sort().is_singleton() {
                continue;
            }
            let pty = match bty.param_kind(param_idx) {
                BasicBlockTypeParamKind::Local(local, _) => self.env.local_type(local),
                BasicBlockTypeParamKind::OuterFnParam(outer_idx) => {
                    let outer_var = outer_fn_param_vars[&outer_idx];
                    PlaceType::with_ty_and_term(
                        param_rty.ty.clone().assert_closed().vacuous(),
                        chc::Term::var(outer_var),
                    )
                }
                BasicBlockTypeParamKind::Synthetic => continue,
            };
            capture.push(rty::RefinedTypeVar::Free(param_idx), pty);
        }
        capture.push_env_state(&self.env);
        let precondition = capture.finish(&self.env);

        self.ctx
            .register_basic_block_precondition(self.local_def_id, bb, precondition);
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
        outer_fn_param_vars: &HashMap<rty::FunctionParamIdx, Var>,
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
                ecx.type_goto(bb, outer_fn_param_vars);
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
            ecx.type_goto(targets.otherwise(), outer_fn_param_vars);
        });
    }

    fn resolve_fn_def(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> (DefId, mir_ty::GenericArgsRef<'tcx>) {
        if self.ctx.is_fn_trait_method(def_id) {
            // When calling a closure via `Fn`/`FnMut`/`FnOnce` trait,
            // we simply replace the def_id with the closure's function def_id.
            // This skips shims, and makes self arguments mismatch. visitor::RustCallVisitor
            // adjusts the arguments accordingly.
            let mir_ty::TyKind::Closure(closure_def_id, closure_args) = args.type_at(0).kind()
            else {
                panic!("expected closure arg for fn trait");
            };
            tracing::debug!(?closure_def_id, "closure instance");
            // closure_args contains [parent_generics..., upvars, return_ty, fn_sig_binder, ...].
            // Only the parent generics are meaningful to def_ty_with_args; the rest are internal
            // closure encoding that type_builder.build() cannot handle.
            let parent_count = self.tcx.generics_of(*closure_def_id).parent_count;
            let parent_args = self.tcx.mk_args(&closure_args[..parent_count]);
            (*closure_def_id, parent_args)
        } else {
            let typing_env = self.body.typing_env(self.tcx);
            let instance =
                mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args).unwrap();
            if let Some(instance) = instance {
                (instance.def_id(), instance.args)
            } else {
                (def_id, args)
            }
        }
    }

    fn fn_def_ty(
        &mut self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> rty::Type<rty::Closed> {
        if let Some(def_ty) = self.ctx.def_ty_with_args(def_id, args) {
            return def_ty.ty;
        }

        let (resolved_def_id, resolved_args) = self.resolve_fn_def(def_id, args);
        if resolved_def_id == def_id {
            panic!(
                "unknown def (and not resolved): {:?}, args: {:?}",
                def_id, args
            );
        }
        tracing::info!(?def_id, ?resolved_def_id, ?resolved_args, "resolved");
        let Some(def_ty) = self.ctx.def_ty_with_args(resolved_def_id, resolved_args) else {
            panic!(
                "unknown def (resolved): {:?}, args: {:?}",
                resolved_def_id, resolved_args
            );
        };
        def_ty.ty
    }

    fn type_call<I>(&mut self, func: Operand<'tcx>, args: I, expected_ret: &rty::RefinedType<Var>)
    where
        I: IntoIterator<Item = Operand<'tcx>>,
    {
        // TODO: handle const_fn_def on Env side
        let func_ty = if let Some((def_id, args)) = func.const_fn_def() {
            self.fn_def_ty(def_id, args).vacuous()
        } else {
            self.operand_type(func.clone()).ty
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

    /// Schedules `local` to be implicitly dropped after this block's terminator,
    /// in addition to the liveness-derived drop points.
    fn schedule_drop_after_terminator(&mut self, local: Local) {
        self.drop_points.insert_after_terminator(local);
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

    fn immut_borrow_place(&self, referent: mir::Place<'tcx>) -> rty::RefinedType<Var> {
        let place = self.elaborate_place(&referent);
        self.env.place_type(place).immut().into()
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

    /// Whether this block's terminator is a loop-invariant marker call.
    fn terminator_is_invariant_marker(&self) -> Option<BasicBlock> {
        let term = &self.body.basic_blocks[self.basic_block].terminator().kind;
        if let TerminatorKind::Call { func, target, .. } = term {
            if let Some((def_id, _)) = func.const_fn_def() {
                if Some(def_id) == self.ctx.def_ids().invariant_marker() {
                    return Some(target.expect("invariant marker call must have a target"));
                }
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
        if let Some(target) = self.terminator_is_invariant_marker() {
            tracing::debug!(?term, "skip invariant marker");
            return mir::Terminator {
                kind: TerminatorKind::Goto { target },
                source_info: term.source_info,
            };
        }
        self.rust_call_visitor().visit_terminator(&mut term);
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
                p if p.projection.is_empty() => p.local,
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
            self.type_call(
                func.clone(),
                args.clone().iter().map(|a| a.node.clone()),
                &rty,
            );
            self.bind_local(destination, rty);
        }
    }

    #[tracing::instrument(skip(self, expected_fn, outer_fn_param_vars), fields(term = ?term.kind))]
    fn analyze_terminator_goto(
        &mut self,
        term: &mir::Terminator<'tcx>,
        expected_fn: &rty::FunctionType,
        outer_fn_param_vars: &HashMap<rty::FunctionParamIdx, Var>,
    ) {
        match &term.kind {
            TerminatorKind::Return => {
                self.type_return(expected_fn, outer_fn_param_vars);
            }
            TerminatorKind::Goto { target } => {
                self.type_goto(*target, outer_fn_param_vars);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.type_switch_int(
                    discr.clone(),
                    targets.clone(),
                    outer_fn_param_vars,
                    |a, target| {
                        for local in a.drop_points.after_terminator(&target) {
                            tracing::info!(?local, ?target, "implicitly dropped for target");
                            a.drop_local(local);
                        }
                    },
                );
            }
            TerminatorKind::Call { target, .. } => {
                if let Some(target) = target {
                    for local in self.drop_points.after_terminator(target) {
                        tracing::info!(?local, "implicitly dropped after call");
                        self.drop_local(local);
                    }
                    self.type_goto(*target, outer_fn_param_vars);
                }
            }
            TerminatorKind::Drop { target, .. } => {
                for local in self.drop_points.after_terminator(target) {
                    tracing::info!(?local, "dropped");
                    self.drop_local(local);
                }
                self.type_goto(*target, outer_fn_param_vars);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                for local in self.drop_points.after_terminator(target) {
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
                self.type_goto(*target, outer_fn_param_vars);
            }
            TerminatorKind::UnwindResume {} => {}
            TerminatorKind::Unreachable {} => {}
            _ => unimplemented!("term={:?}", term.kind),
        }
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
                if !p.projection.is_empty() {
                    unimplemented!();
                }
                // TODO: is it appropriate to use builtin_deref here... maybe we should handle dereferencing logic in `refine`
                let inner_ty = self.local_decls[p.local].ty.builtin_deref(true).unwrap();
                self.add_prophecy_var(stmt_idx, inner_ty);
            }
        }
    }

    fn register_enum_defs(&mut self) {
        for local_decl in &self.local_decls {
            use mir_ty::{TypeSuperVisitable as _, TypeVisitable as _};
            #[derive(Default)]
            struct EnumCollector {
                enums: std::collections::HashSet<DefId>,
            }
            impl<'tcx> mir_ty::TypeVisitor<mir_ty::TyCtxt<'tcx>> for EnumCollector {
                fn visit_ty(&mut self, ty: mir_ty::Ty<'tcx>) {
                    if let mir_ty::TyKind::Adt(adt_def, _) = ty.kind() {
                        if adt_def.is_enum() {
                            self.enums.insert(adt_def.did());
                        }
                    }
                    ty.super_visit_with(self);
                }
            }
            let mut visitor = EnumCollector::default();
            local_decl.ty.visit_with(&mut visitor);
            for def_id in visitor.enums {
                self.ctx.get_or_register_enum_def(def_id);
            }
        }
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    #[tracing::instrument(skip(self, expected_params))]
    fn bind_locals(
        &mut self,
        expected_params: &IndexVec<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    ) -> HashMap<rty::FunctionParamIdx, Var> {
        let mut param_terms = HashMap::<rty::FunctionParamIdx, chc::Term<PlaceTypeVar>>::new();
        let mut assumption = Assumption::default();

        let mut outer_fn_param_vars = HashMap::new();

        let bb_ty = self
            .basic_block_ty_with_precondition(self.basic_block)
            .clone();
        let params = &bb_ty.as_ref().params;
        assert!(!params.is_empty());
        for (param_idx, param_rty) in params.iter_enumerated() {
            let param_ty = &param_rty.ty;
            let param_unrefined_rty =
                rty::RefinedType::unrefined(param_ty.clone().subst_var(|v| {
                    param_terms[&v].clone().map_var(|v| match v {
                        PlaceTypeVar::Var(v) => v,
                        // TODO
                        _ => unimplemented!(),
                    })
                }));
            match bb_ty.param_kind(param_idx) {
                BasicBlockTypeParamKind::Local(local, _) => {
                    if bb_ty.mutbl_of_param(param_idx).unwrap().is_mut()
                        || param_unrefined_rty.ty.is_mut()
                    {
                        self.env.mut_bind(local, param_unrefined_rty);
                    } else {
                        self.env.immut_bind(local, param_unrefined_rty);
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
                BasicBlockTypeParamKind::OuterFnParam(outer_idx) => {
                    let var = self.env.immut_bind_tmp(param_unrefined_rty);
                    param_terms.insert(param_idx, chc::Term::var(var.into()));
                    outer_fn_param_vars.insert(outer_idx, var);
                }
                BasicBlockTypeParamKind::Synthetic => {}
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

        outer_fn_param_vars
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
        let type_builder = TypeBuilder::new(tcx, ctx.def_ids(), local_def_id.to_def_id());
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

    pub fn run(&mut self, expected: &BasicBlockType, expected_fn: &rty::FunctionType) {
        let span = tracing::info_span!("bb", bb = ?self.basic_block);
        let _guard = span.enter();
        self.register_enum_defs();

        let outer_fn_param_vars = self.bind_locals(&expected.as_ref().params);
        self.alloc_prophecies();
        self.analyze_statements();

        let term = self.elaborated_terminator();
        self.analyze_terminator_binds(&term);
        self.analyze_terminator_goto(&term, expected_fn, &outer_fn_param_vars);
    }
}
