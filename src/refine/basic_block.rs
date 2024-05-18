use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, interpret::Scalar, BasicBlock, Const, ConstValue, Local, Operand};
use rustc_middle::ty as mir_ty;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty;

use super::{Env, RefineBodyCtxt, RefineCtxt, Var};

/// `BasicBlockType` is a special case of `FunctionType` whose parameters are
/// associated with `Local`s.
#[derive(Debug, Clone)]
pub struct BasicBlockType {
    // TODO: make this completely private by exposing appropriate ctor
    pub(super) ty: rty::FunctionType,
    pub(super) locals: IndexVec<rty::FunctionParamIdx, Local>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b BasicBlockType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        let params = self.ty.params.iter().zip(&self.locals).map(|(ty, local)| {
            allocator
                .text(format!("{:?}:", local))
                .append(allocator.space())
                .append(ty.pretty(allocator))
        });
        allocator
            .intersperse(params, separator)
            .parens()
            .append(allocator.space())
            .append(allocator.text("→"))
            .append(allocator.line())
            .append(self.ty.ret.pretty(allocator))
            .group()
    }
}

impl AsRef<rty::FunctionType> for BasicBlockType {
    fn as_ref(&self) -> &rty::FunctionType {
        &self.ty
    }
}

impl BasicBlockType {
    pub fn local_of_param(&self, idx: rty::FunctionParamIdx) -> Option<Local> {
        self.locals.get(idx).copied()
    }

    pub fn to_function_ty(&self) -> rty::FunctionType {
        self.ty.clone()
    }
}

#[derive(Debug)]
pub struct RefineBasicBlockCtxt<'rcx, 'bcx> {
    bcx: &'bcx mut RefineBodyCtxt<'rcx>,
    env: Env,
}

impl<'rcx, 'bcx> RefineBasicBlockCtxt<'rcx, 'bcx> {
    pub fn new(bcx: &'bcx mut RefineBodyCtxt<'rcx>) -> Self {
        let env = Default::default();
        Self { bcx, env }
    }

    pub fn rcx(&self) -> &RefineCtxt {
        self.bcx.rcx()
    }

    pub fn rcx_mut(&mut self) -> &mut RefineCtxt {
        self.bcx.rcx_mut()
    }

    pub fn mir_refined_ty(&mut self, ty: mir_ty::Ty<'_>) -> rty::RefinedType<Var> {
        let ty = self.rcx_mut().mir_ty(ty);
        let mut builder = rty::TemplateBuilder::default();
        for (v, sort) in self.env.dependencies() {
            builder.add_dependency(v, sort);
        }
        let tmpl = builder.build(ty);
        self.rcx_mut().register_template(tmpl)
    }

    // TODO: reconsider API
    pub fn bind_locals(&mut self, ty: &BasicBlockType) -> rty::RefinedType<Var> {
        for (param_idx, param_ty) in ty.as_ref().params.iter_enumerated() {
            // TODO: reconsider clone()
            let param_ty = param_ty
                .clone()
                .map_var(|idx| Var::Local(ty.local_of_param(idx).unwrap()));
            if let Some(local) = ty.local_of_param(param_idx) {
                self.env.bind(local, param_ty);
            } else {
                let param_refinement = param_ty.to_free_refinement(|| {
                    panic!("non-local basic block function param must not use value var")
                });
                self.env.assume(param_refinement);
            }
        }
        ty.as_ref()
            .ret
            .clone()
            .map_var(|idx| Var::Local(ty.local_of_param(idx).unwrap()))
    }

    // TODO: reconsider API
    pub fn bind_params(&mut self, ty: rty::FunctionType) -> rty::RefinedType<Var> {
        for (param_idx, param_rty) in ty.params.into_iter_enumerated() {
            self.env.bind(
                super::local_of_function_param(param_idx),
                param_rty.map_var(|idx| Var::Local(super::local_of_function_param(idx))),
            );
        }
        ty.ret
            .map_var(|idx| Var::Local(super::local_of_function_param(idx)))
    }

    pub fn bind_local(&mut self, local: Local, rty: rty::RefinedType<Var>) {
        self.env.bind(local, rty);
    }

    pub fn is_known_local(&self, local: Local) -> bool {
        self.env.contains_local(local)
    }

    fn relate_sub_type(&mut self, got: &rty::Type, expected: &rty::Type) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_type");

        match (got, expected) {
            (rty::Type::Unit, rty::Type::Unit)
            | (rty::Type::Int, rty::Type::Int)
            | (rty::Type::Bool, rty::Type::Bool) => {}
            (rty::Type::Pointer(got), rty::Type::Pointer(expected))
                if got.kind == expected.kind =>
            {
                match got.kind {
                    rty::PointerKind::Own | rty::PointerKind::Ref(rty::RefKind::Immut) => {
                        self.relate_sub_type(&got.elem, &expected.elem);
                    }
                    rty::PointerKind::Ref(rty::RefKind::Mut) => {
                        self.relate_equal_type(&got.elem, &expected.elem);
                    }
                }
            }
            (rty::Type::Function(got), rty::Type::Function(expected)) => {
                // TODO: check sty and length is equal
                // TODO: add value_var dependency
                let mut builder = chc::ClauseBuilder::default();
                for (param_idx, param_rty) in got.params.iter_enumerated() {
                    if let Some(sort) = param_rty.ty.to_sort() {
                        builder.add_dependency(rty::RefinedTypeVar::Free(param_idx), sort);
                    }
                }
                for (got_ty, expected_ty) in got.params.iter().zip(expected.params.clone()) {
                    let clause = builder
                        .clone()
                        .add_body(expected_ty.refinement)
                        .build(got_ty.refinement.clone());
                    self.rcx_mut().add_clause(clause);
                }
                let clause = builder
                    .add_body(got.ret.refinement.clone())
                    .build(expected.ret.refinement.clone());
                self.rcx_mut().add_clause(clause);
            }
            _ => panic!(
                "inconsistent types: got={}, expected={}",
                got.display(),
                expected.display()
            ),
        }
    }

    fn relate_equal_type(&mut self, got: &rty::Type, expected: &rty::Type) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "equal_type");

        self.relate_sub_type(got, expected);
        self.relate_sub_type(expected, got);
    }

    fn relate_sub_refined_type(
        &mut self,
        got: &rty::RefinedType<Var>,
        expected: &rty::RefinedType<Var>,
    ) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_refined_type");

        self.relate_sub_type(&got.ty, &expected.ty);

        let mut builder = self.env.build_clause();
        if let Some(sort) = got.ty.to_sort() {
            builder.add_dependency(rty::RefinedTypeVar::<Var>::Value, sort);
        }

        let clause = builder
            .add_body(got.refinement.clone())
            .build(expected.refinement.clone());
        self.rcx_mut().add_clause(clause);
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
            if let Some(sort) = param_rty.ty.to_sort() {
                builder.add_dependency(rty::RefinedTypeVar::Free(param_idx), sort);
            }
        }
        for (got_ty, expected_ty) in got.params.iter().zip(expected_args) {
            let mut builder = builder.clone();
            if let Some(sort) = got_ty.ty.to_sort() {
                // TODO: API here is bad
                builder.add_dependency(rty::RefinedTypeVar::<Var>::Value, sort);
                builder.add_alias(
                    rty::RefinedTypeVar::<Var>::Value,
                    rty::RefinedTypeVar::<rty::FunctionParamIdx>::Value,
                );
            }
            let clause = builder
                .add_body(expected_ty.refinement)
                .build(got_ty.refinement.clone());
            self.rcx_mut().add_clause(clause);
        }
        if let Some(sort) = got.ret.ty.to_sort() {
            builder.add_dependency(rty::RefinedTypeVar::<Var>::Value, sort);
            builder.add_alias(
                rty::RefinedTypeVar::<Var>::Value,
                rty::RefinedTypeVar::<rty::FunctionParamIdx>::Value,
            );
        }
        let clause = builder
            .add_body(got.ret.refinement.clone())
            .build(expected_ret.refinement.clone());
        self.rcx_mut().add_clause(clause);
    }

    fn operand_refined_type(&self, operand: Operand<'_>) -> rty::RefinedType<Var> {
        let (sty, term) = self.env.operand_type(operand);

        // TODO: should we cover "to_sort" ness in relate_* methods or here?
        if !sty.to_sort().is_some() {
            return rty::RefinedType::unrefined(sty).vacuous();
        }

        rty::RefinedType::refined_with_term(sty, term)
    }

    pub fn type_operand(&mut self, operand: Operand, expected: &rty::RefinedType<Var>) {
        let got = self.operand_refined_type(operand);
        self.relate_sub_refined_type(&got, expected);
    }

    pub fn type_return(&mut self, expected: &rty::RefinedType<Var>) {
        // TODO: deref
        self.type_operand(Operand::Move(mir::RETURN_PLACE.into()), expected);
    }

    pub fn type_goto(&mut self, bb: BasicBlock, expected_ret: &rty::RefinedType<Var>) {
        let bty = self.bcx.basic_block_ty(bb);
        let expected_args: IndexVec<_, _> = bty
            .as_ref()
            .params
            .iter_enumerated()
            .map(|(param_idx, rty)| {
                // TODO: should we cover "to_sort" ness in relate_* methods or here?
                if rty.ty.to_sort().is_some() {
                    let arg_local = bty.local_of_param(param_idx).unwrap();
                    let (sty, term) = self.env.local_type(arg_local);
                    rty::RefinedType::refined_with_term(sty, term)
                } else {
                    rty::RefinedType::unrefined(rty.ty.clone()).vacuous()
                }
            })
            .collect();
        self.relate_fn_sub_type(bty.to_function_ty(), expected_args, expected_ret.clone());
    }

    fn with_assumptions<'a>(
        &'a mut self,
        assumptions: Vec<chc::Atom<Var>>,
    ) -> RefineBasicBlockCtxt<'rcx, 'a> {
        RefineBasicBlockCtxt {
            bcx: self.bcx,
            env: self.env.clone_with_assumptions(assumptions),
        }
    }

    fn with_assumption<'a>(
        &'a mut self,
        assumption: chc::Atom<Var>,
    ) -> RefineBasicBlockCtxt<'rcx, 'a> {
        RefineBasicBlockCtxt {
            bcx: self.bcx,
            env: self.env.clone_with_assumption(assumption),
        }
    }

    pub fn type_switch_int(
        &mut self,
        discr: Operand<'_>,
        targets: mir::SwitchTargets,
        expected_ret: &rty::RefinedType<Var>,
    ) {
        let (_, discr_term) = self.env.operand_type(discr);
        let mut negations = Vec::new();
        for (val, bb) in targets.iter() {
            let val: i64 = val.try_into().unwrap();
            let mut ecx = self.with_assumption(discr_term.clone().equal_to(chc::Term::int(val)));
            ecx.type_goto(bb, expected_ret);
            negations.push(discr_term.clone().not_equal_to(chc::Term::int(val)));
        }
        let mut ecx = self.with_assumptions(negations);
        ecx.type_goto(targets.otherwise(), expected_ret);
    }

    pub fn type_call<'tcx, I>(
        &mut self,
        func: Operand<'tcx>,
        args: I,
        expected_ret: &rty::RefinedType<Var>,
    ) where
        I: IntoIterator<Item = Operand<'tcx>>,
    {
        let def_id = match func.const_fn_def() {
            Some((def_id, gs)) if gs.is_empty() => def_id,
            _ => unimplemented!(),
        };
        let func_ty = self.rcx().def_ty(def_id).expect("unknown def");
        let expected_args: IndexVec<_, _> = args
            .into_iter()
            .map(|op| self.operand_refined_type(op))
            .collect();
        if let rty::Type::Function(func_ty) = func_ty.ty.clone() {
            self.relate_fn_sub_type(func_ty, expected_args, expected_ret.clone());
        } else {
            panic!("unexpected def type: {:?}", func_ty);
        }
    }

    pub fn type_panic(&mut self) {
        let clause = self
            .env
            .build_clause()
            .build(chc::Atom::<rty::Closed>::bottom());
        self.rcx_mut().add_clause(clause);
    }
}
