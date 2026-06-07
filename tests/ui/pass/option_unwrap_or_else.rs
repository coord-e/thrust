//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::callable]
fn check(o: Option<i32>, d: i32) {
    let none = o.is_none();
    let r = o.unwrap_or_else(|| d);
    if none {
        assert!(r == d);
    }
}

fn main() {}
