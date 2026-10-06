//@error-in-other-file: Unsat
//@compile-flags: -C overflow-checks=on
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn incr(s: &mut [i64], i: usize) {
    s[i] += 1;
}

fn main() {
    let mut a = [1, 2];
    incr(&mut a, 1);
    let s: &[i64] = &a;
    assert!(s[1] == 2);
}
