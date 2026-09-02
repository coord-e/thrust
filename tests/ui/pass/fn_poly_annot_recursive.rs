//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == value)]
fn repeat<T>(n: i32, value: T) -> T {
    if n == 0 {
        value
    } else {
        repeat(n - 1, value)
    }
}

fn main() {
    let result = repeat(5, 42);
    assert!(result == 42);
}
