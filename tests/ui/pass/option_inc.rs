//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn maybe_inc(x: i32, do_it: bool) -> Option<i32> {
    if do_it {
        Some(x + 1)
    } else {
        None
    }
}

fn main() {
    let res = maybe_inc(10, true);
    if let Some(v) = res {
        assert!(v == 11);
    }
}
