//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn first<T, U>(pair: (T, U)) -> T {
    pair.0
}

fn main() {
    let x = first((42, true));
    let y = first((true, 100));
    
    assert!(x == 42);
    assert!(y == false);
}
