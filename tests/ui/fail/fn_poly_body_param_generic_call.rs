//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// A generic function whose signature does not mention its type parameter keeps a
// concrete contract, so a caller that is itself generic still learns its result.

fn five<T>() -> i64 {
    5
}

#[thrust::callable]
fn check<T>() {
    assert!(five::<T>() == 6);
}

fn main() {}
