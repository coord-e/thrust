//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// Solved via CoAR/PCSat: z3/Spacer hangs on this recursive &mut CHC on every
// version (the inlined call-destination encoding is a Spacer blind spot). The
// fail twin stays on z3 since refutation is fast.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn sum(a: &mut i64, i: i64) {
    if i == 0 {
        return;
    }
    *a += 1;
    sum(a, i - 1);
}

fn main() {
    let x = rand();
    let mut y = 0;
    sum(&mut y, x);
    assert!(y == x);
}
