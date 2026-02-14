//! Translation of subtyping relations into CHC constraints.

use crate::chc;
use crate::pretty::PrettyDisplayExt;

use super::{ClauseBuilderExt as _, Closed, PointerKind, RefKind, RefinedType, Type};

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

    #[must_use]
    fn relate_equal_refined_type<T: chc::Var, U: chc::Var>(
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
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_type");

        let mut clauses = Vec::new();
        match (got, expected) {
            (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::String, Type::String)
            | (Type::Never, Type::Never) => {}
            (Type::Enum(got), Type::Enum(expected)) if got.symbol() == expected.symbol() => {
                for (got_ty, expected_ty) in got.args.iter().zip(expected.args.iter()) {
                    let cs = self.relate_sub_refined_type(got_ty, expected_ty);
                    clauses.extend(cs);
                }
            }
            (Type::Tuple(got), Type::Tuple(expected))
                if got.elems.len() == expected.elems.len() =>
            {
                for (got_ty, expected_ty) in got.elems.iter().zip(expected.elems.iter()) {
                    let cs = self.relate_sub_refined_type(got_ty, expected_ty);
                    clauses.extend(cs);
                }
            }
            (Type::Pointer(got), Type::Pointer(expected)) if got.kind == expected.kind => {
                match got.kind {
                    PointerKind::Ref(RefKind::Immut) => {
                        let cs = self.relate_sub_refined_type(&got.elem, &expected.elem);
                        clauses.extend(cs);
                    }
                    PointerKind::Own | PointerKind::Ref(RefKind::Mut) => {
                        let cs = self.relate_equal_refined_type(&got.elem, &expected.elem);
                        clauses.extend(cs);
                    }
                }
            }
            (Type::Function(got), Type::Function(expected)) => {
                // TODO: check length is equal
                let mut builder = chc::ClauseBuilder::default();
                for (param_idx, param_rty) in got.params.iter_enumerated() {
                    let param_sort = param_rty.ty.to_sort();
                    if !param_sort.is_singleton() {
                        builder.add_mapped_var(param_idx, param_sort);
                    }
                }
                for (got_ty, expected_ty) in got.params.iter().zip(expected.params.iter()) {
                    let cs = builder.relate_sub_refined_type(expected_ty, got_ty);
                    clauses.extend(cs);
                }
                let cs = builder.relate_sub_refined_type(&got.ret, &expected.ret);
                clauses.extend(cs);
            }
            (Type::Array(got), Type::Array(expected)) => {
                let cs1 = self.relate_sub_refined_type(&got.index, &expected.index);
                clauses.extend(cs1);
                let cs2 = self.relate_sub_refined_type(&got.elem, &expected.elem);
                clauses.extend(cs2);
            }
            _ => panic!(
                "inconsistent types: got={}, expected={}",
                got.display(),
                expected.display()
            ),
        }
        clauses
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
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_refined_type");

        let mut clauses = self.relate_sub_type(&got.ty, &expected.ty);

        let cs = self
            .build_clause()
            .with_value_var(&got.ty)
            .add_body(got.refinement.clone())
            .head(expected.refinement.clone());
        clauses.extend(cs);
        clauses
    }

    fn relate_equal_refined_type<T, U>(
        &self,
        got: &RefinedType<T>,
        expected: &RefinedType<U>,
    ) -> Vec<chc::Clause>
    where
        T: chc::Var,
        U: chc::Var,
    {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "equal_refined_type");

        let mut clauses = self.relate_sub_refined_type(got, expected);
        clauses.extend(self.relate_sub_refined_type(expected, got));
        clauses
    }
}

#[must_use]
pub fn relate_sub_closed_type(got: &Type<Closed>, expected: &Type<Closed>) -> Vec<chc::Clause> {
    tracing::debug!(got = %got.display(), expected = %expected.display(), "relate_sub_closed_type");
    chc::ClauseBuilder::default().relate_sub_type(got, expected)
}
