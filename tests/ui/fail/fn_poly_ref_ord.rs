//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn lt<T>(x: &T, y: &T) -> bool where T: Ord {
    x < y
}

fn main() {
    assert!(lt(&1, &0));
}
