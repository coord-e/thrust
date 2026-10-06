use super::*;
use crate::rty::{Closed, PointerType, RefinedTypeVar, Refinement, TupleType};

fn value() -> chc::Term<RefinedTypeVar<Closed>> {
    chc::Term::var(RefinedTypeVar::Value)
}

fn nonnegative(term: chc::Term<RefinedTypeVar<Closed>>) -> Refinement {
    term.ge(chc::Term::int(0))
        .equal_to(chc::Term::bool(true))
        .into()
}

fn tuple(first: RefinedType, second: RefinedType) -> RefinedType {
    RefinedType::unrefined(Type::Tuple(TupleType {
        elems: vec![first, second],
    }))
}

fn check_subtype(got: &RefinedType, expected: &RefinedType) -> Result<(), chc::CheckSatError> {
    let mut system = chc::System::default();
    for clause in chc::ClauseBuilder::default().relate_sub_refined_type(got, expected) {
        system.push_clause(clause);
    }
    system.solve()
}

#[test]
fn tuple_refinement_positions_are_equivalent() {
    let int = RefinedType::unrefined(Type::Int);
    let nested = tuple(
        RefinedType::new(Type::Int, nonnegative(value())),
        int.clone(),
    );
    let mut outer = tuple(int.clone(), int);
    outer.refinement = nonnegative(value().tuple_proj(0));

    check_subtype(&outer, &nested).unwrap();
    check_subtype(&nested, &outer).unwrap();
}

#[test]
fn tuple_relations_can_prove_element_refinements() {
    let int = RefinedType::unrefined(Type::Int);
    let nested = tuple(
        int.clone(),
        RefinedType::new(Type::Int, nonnegative(value())),
    );
    let mut outer = tuple(int.clone(), int);
    outer.refinement = nonnegative(value().tuple_proj(0));
    outer.refinement.push_conj(
        value()
            .tuple_proj(1)
            .ge(value().tuple_proj(0))
            .equal_to(chc::Term::bool(true))
            .into(),
    );

    check_subtype(&outer, &nested).unwrap();
    assert!(matches!(
        check_subtype(&nested, &outer),
        Err(chc::CheckSatError::Unsat)
    ));
}

#[test]
fn nested_tuples_preserve_projection_paths() {
    let int = RefinedType::unrefined(Type::Int);
    let nested = tuple(
        tuple(
            int.clone(),
            RefinedType::new(Type::Int, nonnegative(value())),
        ),
        int.clone(),
    );
    let mut outer = tuple(tuple(int.clone(), int.clone()), int);
    outer.refinement = nonnegative(value().tuple_proj(0).tuple_proj(1));

    check_subtype(&outer, &nested).unwrap();
    check_subtype(&nested, &outer).unwrap();
    outer.refinement = nonnegative(value().tuple_proj(1));
    assert!(matches!(
        check_subtype(&outer, &nested),
        Err(chc::CheckSatError::Unsat)
    ));
}

#[test]
fn mutable_pointee_refinements_are_facts_about_both_values() {
    let pointer = RefinedType::unrefined(Type::Pointer(PointerType {
        kind: PointerKind::Ref(RefKind::Mut),
        elem: Box::new(RefinedType::new(Type::Int, nonnegative(value()))),
    }));
    let mut refined = pointer.clone();
    refined.refinement = nonnegative(value().mut_current());
    refined
        .refinement
        .push_conj(nonnegative(value().mut_final()));

    check_subtype(&pointer, &refined).unwrap();
    check_subtype(&refined, &pointer).unwrap();
}

#[test]
fn pointer_invariants_cannot_be_replaced_by_outer_refinements() {
    for kind in [PointerKind::Own, PointerKind::Ref(RefKind::Mut)] {
        let nested = RefinedType::unrefined(Type::Pointer(PointerType {
            kind,
            elem: Box::new(RefinedType::new(Type::Int, nonnegative(value()))),
        }));
        let outer = RefinedType::new(
            Type::Pointer(PointerType::new(kind, Type::Int)),
            nested.formula(),
        );

        assert!(matches!(
            check_subtype(&nested, &outer),
            Err(chc::CheckSatError::Unsat)
        ));
        assert!(matches!(
            check_subtype(&outer, &nested),
            Err(chc::CheckSatError::Unsat)
        ));
    }
}
