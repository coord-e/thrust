//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn main() {
    let mut opt = Some(5);
    while let Some(x) = opt {
        if x > 0 {
            opt = Some(x - 1);
        } else {
            opt = None;
        }
    }
    assert!(matches!(opt, None));
}
