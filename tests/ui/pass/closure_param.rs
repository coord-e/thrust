//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
fn take_fn<T, F: Fn(i32) -> T>(f: F) -> T {
    f(41)
}

fn main() {
    let y = take_fn(|x| {
        assert!(x == 41);
        x + 1
    });
    assert!(y == 42);
}
