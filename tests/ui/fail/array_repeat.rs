//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let arr = [7i32; 4];
    let s: &[i32] = &arr;
    assert!(s.len() == 4);
    assert!(s[3] == 8);
}
