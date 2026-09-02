//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
// The declared postcondition `result > x` is weaker than what the body computes, and
// the caller sees only the declared one.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result > x),
        |x: i32| -> i32 { x + 1 },
    );
    let r = apply(3, f);
    assert!(r > 3);
}
