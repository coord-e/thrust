//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn left<T, U>(x: (T, U)) -> T {
    x.0
}

fn main() {
    assert!(left((42, 0)) == 42);
}
