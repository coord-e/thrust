//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn main() {
    let mut v = Vec::new();
    v.push(0);
    v[0] += 1;
    assert!(v.pop().unwrap() == 1);
    assert!(v.pop().unwrap() == 1);
}
