//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
//@check-pass

enum X<T> {
    None1,
    None2,
    Some(T),
}

fn main() {
    let mut opt: X<i32> = X::None1;
    opt = X::None2;
    assert!(matches!(opt, X::None2));
}
