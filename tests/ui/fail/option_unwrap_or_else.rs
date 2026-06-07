//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::callable]
fn check(o: Option<i32>, d: i32) {
    let none = o.is_none();
    let r = o.unwrap_or_else(|| d);
    if none {
        // r == d in the None case, so this assertion does not hold
        assert!(r == d + 1);
    }
}

fn main() {}
