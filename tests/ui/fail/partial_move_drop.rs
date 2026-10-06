//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Regression test for #121: a local that is partially moved must not have a
// dropping assumption emitted for the moved-out portion. Here `(&mut a,)` is
// moved out of `s` into `b`; dropping `s` wholesale used to resolve the
// moved-out `&mut a` prophecy a second time, making the constraints
// contradictory so that this false assertion was wrongly accepted.
fn main() {
    let mut a = 1_i64;
    let s = ((&mut a,),);
    let b = s.0; // partial move: `(&mut a,)` moves out of `s`
    *b.0 = 2;
    assert!(a == 1); // false at runtime: a == 2
}
