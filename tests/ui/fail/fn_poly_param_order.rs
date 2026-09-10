//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn select<T, U, V>(a: T, b: U, c: V, which: i32) -> T {
    if which == 0 {
        a
    } else {
        a
    }
}

fn rotate<A, B, C>(triple: (A, B, C)) -> (B, C, A) {
    (triple.1, triple.2, triple.0)
}

fn main() {
    let x = rotate((1, true, 42));
    assert!(x.0 == false);
}
