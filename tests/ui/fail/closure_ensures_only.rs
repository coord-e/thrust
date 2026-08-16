//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
// The declared postcondition `result > x` hides the body's exact result, so `r == 4`
// is not provable. Were the postcondition inferred instead, it would be exact and the
// assertion would hold.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let f = thrust_macros::closure!(
        ensures(result > x),
        |x: i32| -> i32 { x + 1 },
    );
    let r = apply(3, f);
    assert!(r == 4);
}
