//@check-pass
//@compile-flags: -C debug-assertions=off

// Companion to the #121 regression test: the moved-out `&mut a` prophecy is
// still resolved exactly once (through `b`), so the true post-condition holds.
// This guards against over-suppressing the drop.
fn main() {
    let mut a = 1_i64;
    let s = ((&mut a,),);
    let b = s.0; // partial move: `(&mut a,)` moves out of `s`
    *b.0 = 2;
    assert!(a == 2);
}
