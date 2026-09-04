//! Translation of subtyping relations into CHC constraints.

use rustc_index::IndexVec;

use crate::chc;
use crate::pretty::PrettyDisplayExt;

use super::{ClauseBuilderExt as _, FunctionParamIdx, PointerKind, RefKind, RefinedType, Type};

/// A scope for building clauses.
///
/// The construction of CHC clauses requires knowledge of the current
/// environment to determine variable sorts and include necessary premises.
/// This trait abstracts the preparation of a [`chc::ClauseBuilder`] to allow an
/// environment defined outside of this module (in Thrust, [`crate::refine::Env`])
/// to build a [`chc::ClauseBuilder`] equipped with in-scope variables and assumptions.
pub trait ClauseScope {
    fn build_clause(&self) -> chc::ClauseBuilder;
}

impl<T> ClauseScope for &T
where
    T: ClauseScope,
{
    fn build_clause(&self) -> chc::ClauseBuilder {
        T::build_clause(self)
    }
}

impl ClauseScope for chc::ClauseBuilder {
    fn build_clause(&self) -> chc::ClauseBuilder {
        self.clone()
    }
}

/// Produces CHC constraints for subtyping relations.
pub trait Subtyping {
    #[must_use]
    fn relate_sub_type<T: chc::Var, U: chc::Var>(
        &self,
        got: &Type<T>,
        expected: &Type<U>,
    ) -> Vec<chc::Clause>;

    #[must_use]
    fn relate_sub_refined_type<T: chc::Var, U: chc::Var>(
        &self,
        got: &RefinedType<T>,
        expected: &RefinedType<U>,
    ) -> Vec<chc::Clause>;
}

impl<C> Subtyping for C
where
    C: ClauseScope,
{
    fn relate_sub_type<T, U>(&self, got: &Type<T>, expected: &Type<U>) -> Vec<chc::Clause>
    where
        T: chc::Var,
        U: chc::Var,
    {
        relate_type(self, got, expected, Relation::Sub)
    }

    fn relate_sub_refined_type<T, U>(
        &self,
        got: &RefinedType<T>,
        expected: &RefinedType<U>,
    ) -> Vec<chc::Clause>
    where
        T: chc::Var,
        U: chc::Var,
    {
        relate_refined_type(self, got, expected, Relation::Sub)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Relation {
    Sub,
    Equal,
}

#[must_use]
fn relate_type<C, T, U>(
    scope: &C,
    got: &Type<T>,
    expected: &Type<U>,
    relation: Relation,
) -> Vec<chc::Clause>
where
    C: ClauseScope,
    T: chc::Var,
    U: chc::Var,
{
    tracing::debug!(got = %got.display(), expected = %expected.display(), ?relation, "relate_type");

    let mut clauses = Vec::new();
    match (got, expected) {
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Never, Type::Never) => {}
        (Type::Enum(got), Type::Enum(expected)) if got.symbol() == expected.symbol() => {
            for (got_ty, expected_ty) in got.args.iter().zip(expected.args.iter()) {
                let cs = relate_refined_type(scope, got_ty, expected_ty, relation);
                clauses.extend(cs);
            }
        }
        (Type::Tuple(got), Type::Tuple(expected)) if got.elems.len() == expected.elems.len() => {
            for (got_ty, expected_ty) in got.elems.iter().zip(expected.elems.iter()) {
                let cs = relate_refined_type(scope, got_ty, expected_ty, relation);
                clauses.extend(cs);
            }
        }
        (Type::Pointer(got), Type::Pointer(expected)) if got.kind == expected.kind => {
            let elem_relation = match got.kind {
                PointerKind::Ref(RefKind::Immut) => relation,
                PointerKind::Own | PointerKind::Ref(RefKind::Mut) => Relation::Equal,
            };
            let cs = relate_refined_type(scope, &got.elem, &expected.elem, elem_relation);
            clauses.extend(cs);
        }
        (Type::Function(got), Type::Function(expected))
            if got.params.len() == expected.params.len() =>
        {
            let mut builder = chc::ClauseBuilder::default();
            for (param_idx, param_rty) in got.params.iter_enumerated() {
                let param_sort = param_rty.ty.to_sort();
                if !param_sort.is_singleton() {
                    builder.add_mapped_var(param_idx, param_sort);
                }
            }
            for (got_ty, expected_ty) in got.params.iter().zip(expected.params.iter()) {
                let cs = relate_refined_type(&builder, expected_ty, got_ty, relation);
                clauses.extend(cs);
            }
            let cs = relate_refined_type(&builder, &got.ret, &expected.ret, relation);
            clauses.extend(cs);
        }
        (Type::Array(got), Type::Array(expected)) => {
            let cs1 = relate_refined_type(scope, &got.index, &expected.index, relation);
            clauses.extend(cs1);
            let cs2 = relate_refined_type(scope, &got.elem, &expected.elem, relation);
            clauses.extend(cs2);
        }
        (Type::Param(got), Type::Param(expected))
            if got.forall_sort_idx == expected.forall_sort_idx => {}
        (Type::Alias(got), Type::Alias(expected))
            if got.forall_sort_index() == expected.forall_sort_index() => {}
        _ => panic!(
            "inconsistent types: got={}, expected={}",
            got.display(),
            expected.display()
        ),
    }
    clauses
}

#[must_use]
fn relate_refined_type<C, T, U>(
    scope: &C,
    got: &RefinedType<T>,
    expected: &RefinedType<U>,
    relation: Relation,
) -> Vec<chc::Clause>
where
    C: ClauseScope,
    T: chc::Var,
    U: chc::Var,
{
    tracing::debug!(got = %got.display(), expected = %expected.display(), ?relation, "relate_refined_type");

    let mut clauses = relate_type(scope, &got.ty, &expected.ty, relation);

    let cs = scope
        .build_clause()
        .with_value_var(&got.ty)
        .add_body(got.refinement.clone())
        .head(expected.refinement.clone());
    clauses.extend(cs);

    if relation == Relation::Equal {
        let cs = scope
            .build_clause()
            .with_value_var(&expected.ty)
            .add_body(expected.refinement.clone())
            .head(got.refinement.clone());
        clauses.extend(cs);
    }

    clauses
}

#[must_use]
pub fn relate_sub_param_types(
    got: &IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
    expected: &IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
) -> Vec<chc::Clause> {
    assert_eq!(got.len(), expected.len());

    let mut clauses = Vec::new();
    let mut builder = chc::ClauseBuilder::default();

    for (param_idx, param_rty) in got.iter_enumerated() {
        let param_sort = param_rty.ty.to_sort();
        if !param_sort.is_singleton() {
            builder.add_mapped_var(param_idx, param_sort);
        }
    }

    for (got_ty, expected_ty) in got.iter().zip(expected.iter()) {
        let cs = builder.relate_sub_refined_type(expected_ty, got_ty);
        clauses.extend(cs);
    }

    clauses
}
