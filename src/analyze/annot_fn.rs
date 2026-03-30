use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_hir::{def_id::LocalDefId, HirId};
use rustc_index::IndexVec;
use rustc_middle::ty::{self as mir_ty, TyCtxt};

use crate::analyze::did_cache::DefIdCache;
use crate::annot::AnnotFormula;
use crate::chc;
use crate::rty;

#[derive(Debug, Clone)]
pub struct FormulaFn<'tcx> {
    params: IndexVec<rty::FunctionParamIdx, mir_ty::Ty<'tcx>>,
    formula: chc::Formula<rty::FunctionParamIdx>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b FormulaFn<'_>
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator
            .intersperse(
                self.params.iter_enumerated().map(|(idx, ty)| {
                    idx.pretty(allocator)
                        .append(": ")
                        .append(allocator.as_string(ty))
                }),
                ", ",
            )
            .enclose("|", "|")
            .group()
            .append(self.formula.pretty(allocator))
            .group()
    }
}

impl<'tcx> FormulaFn<'tcx> {
    pub fn to_require_annot(&self) -> AnnotFormula<rty::FunctionParamIdx> {
        AnnotFormula::Formula(self.formula.clone())
    }

    pub fn to_ensure_annot(&self) -> AnnotFormula<rty::RefinedTypeVar<rty::FunctionParamIdx>> {
        AnnotFormula::Formula(self.formula.clone().map_var(|v| {
            if v.as_usize() == 0 {
                rty::RefinedTypeVar::Value
            } else {
                rty::RefinedTypeVar::Free(rty::FunctionParamIdx::from(v.as_usize() - 1))
            }
        }))
    }
}

#[derive(Debug, Clone, Copy)]
enum AmbiguousBinOp {
    Eq,
    Ne,
    Ge,
    Le,
    Gt,
    Lt,
}

#[derive(Debug, Clone)]
enum FormulaOrTerm<T> {
    Formula(chc::Formula<T>),
    Term(chc::Term<T>),
    BinOp(chc::Term<T>, AmbiguousBinOp, chc::Term<T>),
    Not(Box<FormulaOrTerm<T>>),
    Literal(bool),
}

impl<T> FormulaOrTerm<T> {
    fn into_formula(self) -> Option<chc::Formula<T>> {
        let fo = match self {
            FormulaOrTerm::Formula(fo) => fo,
            FormulaOrTerm::Term { .. } => return None,
            FormulaOrTerm::BinOp(lhs, binop, rhs) => {
                let pred = match binop {
                    AmbiguousBinOp::Eq => chc::KnownPred::EQUAL,
                    AmbiguousBinOp::Ne => chc::KnownPred::NOT_EQUAL,
                    AmbiguousBinOp::Ge => chc::KnownPred::GREATER_THAN_OR_EQUAL,
                    AmbiguousBinOp::Le => chc::KnownPred::LESS_THAN_OR_EQUAL,
                    AmbiguousBinOp::Gt => chc::KnownPred::GREATER_THAN,
                    AmbiguousBinOp::Lt => chc::KnownPred::LESS_THAN,
                };
                chc::Formula::Atom(chc::Atom::new(pred.into(), vec![lhs, rhs]))
            }
            FormulaOrTerm::Not(formula_or_term) => formula_or_term.into_formula()?.not(),
            FormulaOrTerm::Literal(b) => {
                if b {
                    chc::Formula::top()
                } else {
                    chc::Formula::bottom()
                }
            }
        };
        Some(fo)
    }

    fn into_term(self) -> Option<chc::Term<T>> {
        let t = match self {
            FormulaOrTerm::Formula { .. } => return None,
            FormulaOrTerm::Term(t) => t,
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Eq, rhs) => lhs.eq(rhs),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Ne, rhs) => lhs.ne(rhs),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Ge, rhs) => lhs.ge(rhs),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Le, rhs) => lhs.le(rhs),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Gt, rhs) => lhs.gt(rhs),
            FormulaOrTerm::BinOp(lhs, AmbiguousBinOp::Lt, rhs) => lhs.lt(rhs),
            FormulaOrTerm::Not(formula_or_term) => formula_or_term.into_term()?.not(),
            FormulaOrTerm::Literal(b) => chc::Term::bool(b),
        };
        Some(t)
    }
}

pub struct AnnotFnTranslator<'tcx> {
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,

    typeck: &'tcx mir_ty::TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,

    def_ids: DefIdCache<'tcx>,
    env: HashMap<HirId, chc::Term<rty::FunctionParamIdx>>,
}

impl<'tcx> AnnotFnTranslator<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_ids: DefIdCache<'tcx>, local_def_id: LocalDefId) -> Self {
        let map = tcx.hir();
        let body_id = map.body_owned_by(local_def_id);
        let body = map.body(body_id);

        let typeck = tcx.typeck(local_def_id);
        let mut translator = Self {
            tcx,
            local_def_id,
            typeck,
            body,
            def_ids,
            env: HashMap::default(),
        };
        translator.build_env_from_params();
        translator
    }

    fn build_env_from_params(&mut self) {
        for (idx, param) in self.body.params.iter().enumerate() {
            let param_idx = rty::FunctionParamIdx::from(idx);
            let term = chc::Term::var(param_idx);
            self.build_env_from_pat(term, param.pat);
        }
    }

    fn build_env_from_pat(
        &mut self,
        param: chc::Term<rty::FunctionParamIdx>,
        pat: &'tcx rustc_hir::Pat<'tcx>,
    ) {
        use rustc_hir::PatKind;

        match pat.kind {
            PatKind::Binding(_, hir_id, _, None) => {
                self.env.insert(hir_id, param);
            }
            PatKind::TupleStruct(_, subpats, _) | PatKind::Tuple(subpats, _) => {
                for (idx, subpat) in subpats.iter().enumerate() {
                    let field_term = param.clone().tuple_proj(idx);
                    self.build_env_from_pat(field_term, subpat);
                }
            }
            _ => unimplemented!("unsupported pattern in formula: {:?}", pat),
        }
    }

    pub fn to_formula_fn(&self) -> FormulaFn<'tcx> {
        let formula = self.to_formula(self.body.value);
        let params = self
            .tcx
            .fn_sig(self.local_def_id.to_def_id())
            .instantiate_identity()
            .skip_binder()
            .inputs()
            .to_vec();
        FormulaFn {
            params: IndexVec::from_raw(params),
            formula,
        }
    }

    fn to_formula(&self, hir: &'tcx rustc_hir::Expr<'tcx>) -> chc::Formula<rty::FunctionParamIdx> {
        self.to_formula_or_term(hir)
            .into_formula()
            .expect("expected a formula")
    }

    fn to_term(&self, hir: &'tcx rustc_hir::Expr<'tcx>) -> chc::Term<rty::FunctionParamIdx> {
        self.to_formula_or_term(hir)
            .into_term()
            .expect("expected a term")
    }

    fn to_formula_or_term(
        &self,
        hir: &'tcx rustc_hir::Expr<'tcx>,
    ) -> FormulaOrTerm<rty::FunctionParamIdx> {
        use rustc_hir::ExprKind;

        match hir.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                match op.node {
                    rustc_hir::BinOpKind::Or => {
                        let lhs = self.to_formula(lhs);
                        let rhs = self.to_formula(rhs);
                        return FormulaOrTerm::Formula(lhs.or(rhs));
                    }
                    rustc_hir::BinOpKind::And => {
                        let lhs = self.to_formula(lhs);
                        let rhs = self.to_formula(rhs);
                        return FormulaOrTerm::Formula(lhs.and(rhs));
                    }
                    rustc_hir::BinOpKind::Add => {
                        let lhs = self.to_term(lhs);
                        let rhs = self.to_term(rhs);
                        return FormulaOrTerm::Term(lhs.add(rhs));
                    }
                    rustc_hir::BinOpKind::Sub => {
                        let lhs = self.to_term(lhs);
                        let rhs = self.to_term(rhs);
                        return FormulaOrTerm::Term(lhs.sub(rhs));
                    }
                    rustc_hir::BinOpKind::Mul => {
                        let lhs = self.to_term(lhs);
                        let rhs = self.to_term(rhs);
                        return FormulaOrTerm::Term(lhs.mul(rhs));
                    }
                    _ => {}
                }

                let binop = match op.node {
                    rustc_hir::BinOpKind::Eq => AmbiguousBinOp::Eq,
                    rustc_hir::BinOpKind::Ne => AmbiguousBinOp::Ne,
                    rustc_hir::BinOpKind::Ge => AmbiguousBinOp::Ge,
                    rustc_hir::BinOpKind::Le => AmbiguousBinOp::Le,
                    rustc_hir::BinOpKind::Gt => AmbiguousBinOp::Gt,
                    rustc_hir::BinOpKind::Lt => AmbiguousBinOp::Lt,
                    _ => unimplemented!("unsupported binary operator in formula: {:?}", op),
                };
                let lhs = self.to_formula_or_term(lhs);
                let rhs = self.to_formula_or_term(rhs);
                FormulaOrTerm::BinOp(lhs.into_term().unwrap(), binop, rhs.into_term().unwrap())
            }
            ExprKind::Unary(op, operand) => match op {
                rustc_hir::UnOp::Neg => {
                    let operand = self.to_term(operand);
                    FormulaOrTerm::Term(operand.neg())
                }
                rustc_hir::UnOp::Not => {
                    FormulaOrTerm::Not(Box::new(self.to_formula_or_term(operand)))
                }
                rustc_hir::UnOp::Deref => {
                    let operand_ty = self.typeck.expr_ty(operand);
                    let adt = operand_ty
                        .ty_adt_def()
                        .expect("deref operand must be a model type");
                    let term = self.to_term(operand);
                    if Some(adt.did()) == self.def_ids.mut_model() {
                        FormulaOrTerm::Term(term.mut_current())
                    } else if Some(adt.did()) == self.def_ids.box_model() {
                        FormulaOrTerm::Term(term.box_current())
                    } else {
                        unimplemented!(
                            "unsupported deref operand type in formula: {:?}",
                            operand_ty
                        )
                    }
                }
            },
            ExprKind::Lit(lit) => match lit.node {
                rustc_ast::LitKind::Int(i, _) => {
                    let n = i64::try_from(i.get())
                        .expect("integer literal out of i64 range in formula");
                    FormulaOrTerm::Term(chc::Term::int(n))
                }
                rustc_ast::LitKind::Bool(b) => FormulaOrTerm::Literal(b),
                _ => unimplemented!("unsupported literal in formula: {:?}", lit),
            },
            ExprKind::Path(qpath) => {
                if let rustc_hir::def::Res::Local(hir_id) =
                    self.typeck.qpath_res(&qpath, hir.hir_id)
                {
                    FormulaOrTerm::Term(
                        self.env
                            .get(&hir_id)
                            .expect("unbound variable in formula")
                            .clone(),
                    )
                } else {
                    unimplemented!("unsupported path in formula: {:?}", qpath);
                }
            }
            ExprKind::Tup(exprs) => {
                let terms = exprs.iter().map(|e| self.to_term(e)).collect();
                FormulaOrTerm::Term(chc::Term::tuple(terms))
            }
            ExprKind::Field(expr, field) => {
                let index = field
                    .name
                    .as_str()
                    .parse::<usize>()
                    .expect("tuple field index must be a non-negative integer");
                let term = self.to_term(expr);
                FormulaOrTerm::Term(term.tuple_proj(index))
            }
            ExprKind::Call(func_expr, args) => {
                if let ExprKind::Path(qpath) = &func_expr.kind {
                    let res = self.typeck.qpath_res(qpath, func_expr.hir_id);
                    if let rustc_hir::def::Res::Def(_, def_id) = res {
                        if Some(def_id) == self.def_ids.mut_model_new() {
                            assert_eq!(args.len(), 2, "Mut::new takes exactly 2 arguments");
                            let t1 = self.to_term(&args[0]);
                            let t2 = self.to_term(&args[1]);
                            return FormulaOrTerm::Term(chc::Term::mut_(t1, t2));
                        }
                        if Some(def_id) == self.def_ids.box_model_new() {
                            assert_eq!(args.len(), 1, "Box::new takes exactly 1 argument");
                            let t = self.to_term(&args[0]);
                            return FormulaOrTerm::Term(chc::Term::box_(t));
                        }
                    }
                }
                unimplemented!("unsupported call in formula: {:?}", func_expr)
            }
            ExprKind::Block(block, _) => {
                if block.stmts.is_empty() {
                    self.to_formula_or_term(block.expr.expect("expected an expression in block"))
                } else {
                    unimplemented!("unsupported block in formula: {:?}", block);
                }
            }
            _ => unimplemented!("unsupported expression in formula: {:?}", hir),
        }
    }
}
