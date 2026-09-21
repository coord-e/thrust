//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C opt-level=2
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::callable]
fn check(v: &mut [i32], i: usize) {
    if i < v.len() {
        v[i] = 7;
        assert!(v[i] == 8);
    }
}

fn main() {}
