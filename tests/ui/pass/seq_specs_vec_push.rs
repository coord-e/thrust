//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Arbitrary-length Vec: read back the last pushed value. The Vec's length is
// unconstrained on entry, and the spec relates the new length to the old.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.1 == v.1 + 1 && result.0[v.1] == x)]
fn snoc(mut v: Vec<i64>, x: i64) -> Vec<i64> {
    v.push(x);
    v
}

fn main() {
    let mut v: Vec<i64> = Vec::new();
    v.push(7);
    let _ = snoc(v, 8);
}
