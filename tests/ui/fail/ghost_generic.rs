//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::Ghost;

#[thrust_macros::requires(g == v)]
fn expect_same<T>(g: Ghost<T>, v: T) {
    let _ = g;
}

#[thrust_macros::context]
fn record<T: Copy>(a: T, b: T) {
    let g = thrust_macros::ghost!(|b: T| -> T { b });
    expect_same(g, a);
}

fn main() {
    record(3_i64, 5_i64);
}
