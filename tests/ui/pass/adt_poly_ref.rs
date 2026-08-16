//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

enum X<'a, T> {
    A(&'a T),
}

fn main() {
    let i = 42;
    let x = X::A(&i);
    match x {
        X::A(i) => assert!(*i == 42),
    }
}
