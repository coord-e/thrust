//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
use thrust_models::{exists, model::Mut};

#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(exists(|g| thrust_macros::post!(Mut::new(f, g)(), result)))]
fn call<F: FnMut() -> i64>(mut f: F) -> i64 {
    f()
}

fn main() {
    let mut cnt: i64 = 0;
    let f = || -> i64 {
        cnt += 1;
        cnt
    };
    let r = call(f);
    // `f` increments `cnt` once, so `r == 1`
    assert!(r == 2);
}
