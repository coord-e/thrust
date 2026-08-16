//@check-pass
//@compile-flags: -C debug-assertions=off

// Companion to the #122 regression test: the moved-out `&mut` prophecy is
// resolved exactly once (inside `bump`), so the true post-condition holds.
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
    assert!(x == 2);
}
