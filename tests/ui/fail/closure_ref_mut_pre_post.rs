//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn call<F: Fn() -> i64>(f: &mut F) -> i64 {
    f()
}

fn main() {
    let k: i64 = 1;
    let mut f = || -> i64 { k };
    let r = call(&mut f);
    // `f` returns `k`, which is 1
    assert!(r == 2);
}
