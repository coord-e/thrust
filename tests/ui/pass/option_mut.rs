//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn main() {
    let mut m: Option<i32> = Some(1);
    if let Some(i) = &mut m {
        *i += 2;
    }
    assert!(matches!(m, Some(3)));
}
