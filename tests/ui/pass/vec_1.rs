//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let mut v = Vec::new();
    v.push(0);
    assert!(v.len() == 1);
    assert!(v[0] == 0);
}
