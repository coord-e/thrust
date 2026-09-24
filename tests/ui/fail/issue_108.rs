//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
fn apply<T, F: FnOnce(T) -> T>(x: T, f: F) -> T {
    f(x)
}
fn call_apply<T>(x: T) -> T {
    apply(x, |y| y)
}
fn main() {
    let r = call_apply(3);
    assert!(r == 4);
}
