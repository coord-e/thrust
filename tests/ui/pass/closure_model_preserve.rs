//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
#[thrust_macros::ensures(result == f)]
fn call<F: FnMut() -> i32>(mut f: F) -> F {
    f();
    f
}

fn main() {
    let x = 2;
    let mut f = call(|| {
        x
    });
    assert!(f() == 2);
}
