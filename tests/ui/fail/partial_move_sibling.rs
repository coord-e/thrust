//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Soundness guard for the case where the moved-out part is used *and* the
// still-owned sibling is reborrowed: dropping `s` while excepting the moved-out
// `s.0` must not resolve `s.0`'s prophecy a second time (it is resolved via
// `x`). Otherwise the constraints go contradictory and this false assertion
// would verify vacuously.
fn main() {
    let mut a = 1_i64;
    let mut b = 2_i64;
    let s = ((&mut a,), (&mut b,));
    let x = s.0;
    *x.0 = 10;
    *(s.1).0 = 20;
    assert!(a == 999); // false at runtime: a == 10
}
