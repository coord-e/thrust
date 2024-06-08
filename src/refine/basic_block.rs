use std::collections::{HashMap, HashSet};

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Const, ConstValue, Local, Operand, Rvalue};
use rustc_middle::ty as mir_ty;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty::{self, ClauseBuilderExt as _};

use super::{Env, RefineBodyCtxt, RefineCtxt, TempVarIdx, Var};

/// `BasicBlockType` is a special case of `FunctionType` whose parameters are
/// associated with `Local`s.
#[derive(Debug, Clone)]
pub struct BasicBlockType {
    // TODO: make this completely private by exposing appropriate ctor
    pub(super) ty: rty::FunctionType,
    pub(super) locals: IndexVec<rty::FunctionParamIdx, (Local, mir_ty::Mutability)>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b BasicBlockType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        let params = self
            .ty
            .params
            .iter()
            .zip(&self.locals)
            .map(|(ty, (local, mutbl))| {
                allocator
                    .text(format!("{}{:?}:", mutbl.prefix_str(), local))
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
        self.locals.get(idx).map(|(local, _)| *local)
    }

    pub fn mutbl_of_param(&self, idx: rty::FunctionParamIdx) -> Option<mir_ty::Mutability> {
        self.locals.get(idx).map(|(_, mutbl)| *mutbl)
    }

    pub fn to_function_ty(&self) -> rty::FunctionType {
        self.ty.clone()
    }
}

#[derive(Debug)]
pub struct RefineBasicBlockCtxt<'rcx, 'bcx> {
    bcx: &'bcx mut RefineBodyCtxt<'rcx>,
    env: Env,
    // statement index -> TempVarIdx in env
    prophecy_vars: HashMap<usize, TempVarIdx>,
    // locals which are treated as `own` due to mutability
    mut_locals: HashSet<Local>,
}

impl<'rcx, 'bcx> RefineBasicBlockCtxt<'rcx, 'bcx> {
    pub fn new(bcx: &'bcx mut RefineBodyCtxt<'rcx>) -> Self {
        let env = Default::default();
        let prophecy_vars = Default::default();
        let mut_locals = Default::default();
        Self {
            bcx,
            env,
            prophecy_vars,
            mut_locals,
        }
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
                if ty.mutbl_of_param(param_idx).unwrap().is_mut() {
                    self.mut_locals.insert(local);
                }
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

    // TODO: reconsider API
    pub fn bind_params(&mut self, ty: rty::FunctionType) -> rty::RefinedType<Var> {
        let subst_var_fn = |env: &Env, idx| {
            // TODO: this would be broken when we turned args mutually-referenced...
            let (_, term) = env.local_type(super::local_of_function_param(idx));
            term
        };
        for (param_idx, param_rty) in ty.params.into_iter_enumerated() {
            self.env.bind(
                super::local_of_function_param(param_idx),
                param_rty.subst_var(|idx| subst_var_fn(&self.env, idx)),
            );
        }
        ty.ret.subst_var(|idx| subst_var_fn(&self.env, idx))
    }

    pub fn bind_local(&mut self, local: Local, rty: rty::RefinedType<Var>, mutbl: mir::Mutability) {
        // elaboration:
        let elaborated_rty = if mutbl.is_mut() {
            self.mut_locals.insert(local);
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
                        builder.add_mapped_var(param_idx, sort);
                    }
                }
                for (got_ty, expected_ty) in got.params.iter().zip(expected.params.clone()) {
                    let clause = builder
                        .clone()
                        .with_value_var(&got_ty.ty)
                        .add_body(expected_ty.refinement)
                        .head(got_ty.refinement.clone());
                    self.rcx_mut().add_clause(clause);
                }
                let clause = builder
                    .with_value_var(&got.ret.ty)
                    .add_body(got.ret.refinement.clone())
                    .head(expected.ret.refinement.clone());
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

        let clause = self
            .env
            .build_clause()
            .with_value_var(&got.ty)
            .add_body(got.refinement.clone())
            .head(expected.refinement.clone());
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
                builder.add_mapped_var(param_idx, sort);
            }
        }
        for ((param_idx, got_ty), expected_ty) in got.params.iter_enumerated().zip(&expected_args) {
            // TODO we can use relate_sub_refined_type here when we implemenented builder-aware relate_*
            let clause = builder
                .clone()
                .with_value_var(&got_ty.ty)
                .add_body(expected_ty.refinement.clone())
                .head(got_ty.refinement.clone());
            self.rcx_mut().add_clause(clause);
            builder
                .with_mapped_value_var(param_idx)
                .add_body(expected_ty.refinement.clone());
        }

        let clause = builder
            .with_value_var(&got.ret.ty)
            .add_body(got.ret.refinement)
            .head(expected_ret.refinement);
        self.rcx_mut().add_clause(clause);
    }

    fn operand_type(&self, operand: Operand<'_>) -> (rty::Type, chc::Term<Var>) {
        let (sty, term) = self.env.operand_type(operand.clone());
        tracing::debug!(operand = ?operand, locals = ?self.mut_locals, "operand_type");
        if matches!(operand, Operand::Copy(p) | Operand::Move(p) if self.mut_locals.contains(&p.local))
        {
            (sty.deref(), term.box_current())
        } else {
            (sty, term)
        }
    }

    fn rvalue_type(&mut self, rvalue: Rvalue<'_>) -> (rty::Type, chc::Term<Var>) {
        match rvalue {
            Rvalue::Use(operand) => self.operand_type(operand),
            Rvalue::BinaryOp(op, operands) => {
                let (lhs, rhs) = *operands;
                let (lhs_ty, lhs_term) = self.operand_type(lhs);
                let (rhs_ty, rhs_term) = self.operand_type(rhs);
                // NOTE: BinOp::Offset accepts operands with different types
                //       but we don't support it here
                self.relate_equal_type(&lhs_ty, &rhs_ty);
                match (&lhs_ty, op) {
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
                }
            }
            _ => unimplemented!("rvalue={:?}", rvalue),
        }
    }

    fn rvalue_refined_type(&mut self, rvalue: Rvalue<'_>) -> rty::RefinedType<Var> {
        let (sty, term) = self.rvalue_type(rvalue);

        // TODO: should we cover "to_sort" ness in relate_* methods or here?
        if !sty.to_sort().is_some() {
            return rty::RefinedType::unrefined(sty).vacuous();
        }

        rty::RefinedType::refined_with_term(sty, term)
    }

    pub fn type_rvalue(&mut self, rvalue: Rvalue<'_>, expected: &rty::RefinedType<Var>) {
        let got = self.rvalue_refined_type(rvalue);
        self.relate_sub_refined_type(&got, expected);
    }

    pub fn operand_refined_type(&mut self, operand: Operand<'_>) -> rty::RefinedType<Var> {
        self.rvalue_refined_type(Rvalue::Use(operand))
    }

    pub fn type_operand(&mut self, operand: Operand<'_>, expected: &rty::RefinedType<Var>) {
        self.type_rvalue(Rvalue::Use(operand), expected);
    }

    pub fn type_return(&mut self, expected: &rty::RefinedType<Var>) {
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

    pub fn type_switch_int<F>(
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
            ecx.type_goto(targets.otherwise(), expected_ret);
        });
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
            Some((def_id, args)) => {
                if !args.is_empty() {
                    tracing::warn!(?args, ?def_id, "generic args ignored");
                }
                def_id
            }
            _ => unimplemented!(),
        };
        let func_ty = self.rcx().def_ty(def_id).expect("unknown def").ty.clone();
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

    // TODO: move most of this to Env
    pub fn assign_to_local<'tcx>(&mut self, local: Local, rvalue: Rvalue<'tcx>) {
        let (_local_ty, local_term) = self.env.local_type(local);
        let (_rvalue_ty, rvalue_term) = self.rvalue_type(rvalue);
        self.env
            .assume(local_term.mut_final().equal_to(rvalue_term));
    }

    pub fn drop_local(&mut self, local: Local) {
        let (ty, term) = self.env.local_type(local);
        if ty.is_mut() {
            self.env
                .assume(term.clone().mut_final().equal_to(term.mut_current()));
        }
    }

    pub fn add_prophecy_var(&mut self, statement_index: usize, ty: mir_ty::Ty<'_>) {
        let ty = self.rcx_mut().mir_ty(ty);
        let temp_var = self.env.push_temp_var(ty);
        self.prophecy_vars.insert(statement_index, temp_var);
        tracing::debug!(stmt_idx = %statement_index, temp_var = ?temp_var, "add_prophecy_var");
    }

    pub fn borrow_local(&mut self, statement_index: usize, local: Local) -> rty::RefinedType<Var> {
        let temp_var = self.prophecy_vars[&statement_index];
        let (ty, term) = self.env.borrow_local(local, temp_var);
        rty::RefinedType::refined_with_term(ty, term)
    }

    pub fn borrow_local_(&mut self, local: Local, ty: mir_ty::Ty<'_>) -> rty::RefinedType<Var> {
        let ty = self.rcx_mut().mir_ty(ty);
        let temp_var = self.env.push_temp_var(ty);
        let (ty, term) = self.env.borrow_local(local, temp_var);
        rty::RefinedType::refined_with_term(ty, term)
    }
}
