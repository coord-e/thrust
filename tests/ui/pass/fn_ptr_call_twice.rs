//@check-pass
//@compile-flags: -C debug-assertions=off

fn incr(m: &mut i64) {
    *m += 1;
}

// A call ends its basic block, so the second call sees `f` re-entering the block
// it lives in. The callee's specification must survive that boundary; without it
// the second call's effect on `x` is unconstrained.
fn main() {
    let f: fn(&mut i64) = incr;
    let mut x = 0;
    f(&mut x);
    f(&mut x);
    assert!(x == 2);
}
