//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
fn apply<F>(mut f: F) -> i32
where
    F: FnMut(i32) -> i32,
{
    f(1) + f(2)
}

fn main() {
    let x = 1;
    let closure = |y: i32| x + y;
    let result = apply(closure);
    assert!(result == 1);
}
