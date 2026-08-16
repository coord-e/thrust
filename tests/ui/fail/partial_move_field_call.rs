//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Regression test for #122: a `&mut`-bearing field moved out of an aggregate
// into a call must not be re-dropped when the parent is dropped wholesale.
// `w.0` (an owned `(&mut i32,)`) is moved into `bump`; dropping `w` afterwards
// used to resolve the moved-out `&mut` prophecy a second time, so this false
// assertion was wrongly accepted.
fn bump(p: (&mut i64,)) {
    *p.0 += 1;
}

fn apply(w: ((&mut i64,),)) {
    bump(w.0); // moves owned field `(&mut i64,)` out of `w` into the call
}

fn main() {
    let mut x = 1_i64;
    let w = ((&mut x,),);
    apply(w);
    assert!(x == 999); // false at runtime: x == 2
}
