//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// An annotated generic function contributes its contract at a call site whose type
// arguments are still type parameters, where an inferred contract would not.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 5)]
fn five<T>(_t: T) -> i64 {
    5
}

#[thrust::callable]
fn check<T>(t: T) {
    assert!(five(t) == 6);
}

fn main() {}
