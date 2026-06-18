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
                for ((param_idx, got_ty), expected_ty) in
                    got.params.iter_enumerated().zip(expected.params.iter())
                {
                    let cs = builder.relate_sub_refined_type(expected_ty, got_ty);
                    clauses.extend(cs);
                    // Assume the (caller-provided) parameter precondition before relating
                    // the return, mirroring `relate_fn_sub_type` in `analyze::basic_block`.
                    // Without this, a dependent return refinement that is only valid given
                    // the parameter preconditions cannot be discharged (issue #128).
                    builder
                        .with_mapped_value_var(param_idx)
                        .add_body(expected_ty.refinement.clone());
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

    for ((param_idx, got_ty), expected_ty) in got.iter_enumerated().zip(expected.iter()) {
        let cs = builder.relate_sub_refined_type(expected_ty, got_ty);
        clauses.extend(cs);
        // Accumulate each (caller-provided) parameter precondition so that a later
        // parameter whose refinement depends on an earlier one is related under that
        // earlier parameter's assumption (issue #128).
        builder
            .with_mapped_value_var(param_idx)
            .add_body(expected_ty.refinement.clone());
    }

    clauses
}
#[cfg(test)]
mod tests {
    use rustc_index::IndexVec;

    use crate::chc;
    use crate::rty::{
        Closed, FunctionParamIdx, FunctionType, RefinedType, RefinedTypeVar, Refinement, Type,
    };

    use super::{relate_sub_param_types, Subtyping};

    type Fv = RefinedTypeVar<FunctionParamIdx>;

    fn value() -> chc::Term<Fv> {
        chc::Term::var(RefinedTypeVar::Value)
    }

    fn param(i: usize) -> chc::Term<Fv> {
        chc::Term::var(RefinedTypeVar::Free(FunctionParamIdx::from_usize(i)))
    }

    fn refinement(atom: chc::Atom<Fv>) -> Refinement<FunctionParamIdx> {
        Refinement::new(IndexVec::new(), chc::Body::from(atom))
    }

    /// `ν > 0`
    fn positive() -> Refinement<FunctionParamIdx> {
        refinement(chc::Atom::new(
            chc::KnownPred::GREATER_THAN.into(),
            vec![value(), chc::Term::int(0)],
        ))
    }

    /// `ν == <param i>`
    fn equals_param(i: usize) -> Refinement<FunctionParamIdx> {
        refinement(value().equal_to(param(i)))
    }

    fn int_param(refinement: Refinement<FunctionParamIdx>) -> RefinedType<FunctionParamIdx> {
        RefinedType::new(Type::int(), refinement)
    }

    /// `fn(x: { ν: i32 | param_ref }) -> { ν: i32 | ret_ref }`
    fn unary_fn(
        param_ref: Refinement<FunctionParamIdx>,
        ret_ref: Refinement<FunctionParamIdx>,
    ) -> Type<Closed> {
        let mut params = IndexVec::new();
        params.push(int_param(param_ref));
        Type::function(FunctionType::new(params, int_param(ret_ref)))
    }

    fn is_sat(clauses: Vec<chc::Clause>) -> bool {
        let mut system = chc::System::default();
        for clause in clauses {
            system.push_clause(clause);
        }
        // Uses the configured solver (Z3 by default); the obligations here are
        // pure first-order constraints with no predicate variables.
        system.solve().is_ok()
    }

    /// Regression test for issue #128.
    ///
    /// Relating the function subtyping
    ///
    /// ```text
    /// got      = fn(x: { ν: i32 | ν > 0 }) -> { ν: i32 | ν == x }
    /// expected = fn(x: { ν: i32 | ν > 0 }) -> { ν: i32 | ν > 0 }
    /// ```
    ///
    /// is valid: the covariant return obligation `ν == x ⟹ ν > 0` only holds
    /// because the parameter precondition guarantees `x > 0`. The `Type::Function`
    /// arm of `relate_sub_type` used to prove the return obligation without
    /// assuming the parameters' preconditions, leaving `x` unconstrained, so it
    /// wrongly rejected this subtyping as `Unsat`.
    #[test]
    fn function_subtyping_assumes_parameter_precondition() {
        let got = unary_fn(positive(), equals_param(0));
        let expected = unary_fn(positive(), positive());

        let clauses = chc::ClauseBuilder::default().relate_sub_type(&got, &expected);
        assert!(
            is_sat(clauses),
            "a valid dependent function subtyping was rejected (issue #128)"
        );
    }

    /// Control case: when the return refinement genuinely does *not* follow from
    /// the parameter precondition, the subtyping must still be rejected. Guards
    /// against the fix degenerating into assuming too much.
    #[test]
    fn function_subtyping_rejects_underivable_return() {
        // got returns `ν == x` for an unconstrained `x`; expected demands `ν > 0`,
        // which does not follow without a parameter precondition.
        let got = unary_fn(Refinement::top(), equals_param(0));
        let expected = unary_fn(Refinement::top(), positive());

        let clauses = chc::ClauseBuilder::default().relate_sub_type(&got, &expected);
        assert!(
            !is_sat(clauses),
            "an invalid function subtyping was wrongly accepted"
        );
    }

    /// Regression test for the related defect in `relate_sub_param_types`
    /// (issue #128, "Related" section): a dependent parameter refinement
    /// (parameter `j` mentioning parameter `i`) must be related under
    /// parameter `i`'s precondition.
    ///
    /// `relate_sub_param_types` relates the parameters *contravariantly*
    /// (`expected <: got`), so for each parameter it emits
    /// `expected.refinement ⟹ got.refinement`. With
    ///
    /// ```text
    /// got      = (x: { ν | ν > 0 }, y: { ν | ν > 0 })
    /// expected = (x: { ν | ν > 0 }, y: { ν | ν == x })
    /// ```
    ///
    /// the obligation on `y` is `ν == x ⟹ ν > 0`, which is only dischargeable
    /// because `expected.x` guarantees `x > 0`.
    #[test]
    fn param_subtyping_assumes_earlier_parameter_precondition() {
        let mut got = IndexVec::new();
        got.push(int_param(positive()));
        got.push(int_param(positive()));
        let mut expected = IndexVec::new();
        expected.push(int_param(positive()));
        expected.push(int_param(equals_param(0)));

        let clauses = relate_sub_param_types(&got, &expected);
        assert!(
            is_sat(clauses),
            "a valid dependent parameter subtyping was rejected (issue #128)"
        );
    }
}
