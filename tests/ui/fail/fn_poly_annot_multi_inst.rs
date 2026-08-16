//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id<T>(x: T) -> T {
    x
}

fn main() {
    let a = id(42);
    assert!(a == 42);
    
    let b = id(true);
    assert!(b == false);
}
