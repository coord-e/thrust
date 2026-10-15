//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn incr(m: &mut i64) {
    *m += 1;
}

// A call ends its basic block, so the second call sees `f` re-entering the block
// it lives in. The specification the caller supplied for `f` must survive that
// boundary; without it the second call's effect on `x` is unconstrained.
fn app(f: fn(&mut i64), mut x: i64) -> i64 {
    f(&mut x);
    f(&mut x);
    x
}

fn main() {
    let i = rand();
    let x = app(incr, i);
    assert!(x == i + 2);
}
