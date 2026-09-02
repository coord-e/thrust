//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
// `-1` violates the declared precondition `x > 0`. Were the precondition inferred
// instead, it would be weak enough to admit the call.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let f = thrust_macros::closure!(
        requires(x > 0),
        |x: i32| -> i32 { x + 1 },
    );
    let r = apply(-1, f);
    assert!(r == 0);
}
