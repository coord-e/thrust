//@check-pass
//@compile-flags: -C debug-assertions=off

// A partially-moved local with a still-owned sibling. `s.0` moves into `x` (its
// `&mut a` resolved through `x`); `s.1` stays owned by `s` and is mutated in
// place. Dropping `s` skips the moved-out `s.0` but must still resolve the
// sibling `s.1`'s `&mut b` prophecy exactly once, so both post-conditions hold.
fn main() {
    let mut a = 1_i64;
    let mut b = 2_i64;
    let s = ((&mut a,), (&mut b,));
    let x = s.0; // partial move: s.0 moves out, s.1 still owned
    *x.0 = 10;
    *(s.1).0 = 20;
    assert!(a == 10);
    assert!(b == 20);
}
