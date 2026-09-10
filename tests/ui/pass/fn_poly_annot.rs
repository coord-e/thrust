//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x.0)]
fn left<T, U>(x: (T, U)) -> T {
    x.0
}

fn main() {
    assert!(left((42, 0)) == 42);
}
