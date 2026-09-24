//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::{
    exists,
    model::{Int, Mut},
};

#[thrust_macros::ensures(exists(|g, h, i: Int|
  thrust_macros::post!(Mut::new(f, g)(), i)
  && thrust_macros::post!(Mut::new(g, h)(), result)
))]
fn call_twice<F: FnMut() -> i64>(mut f: F) -> i64 {
    f();
    f()
}

fn main() {
    let mut cnt: i64 = 0;
    let f = move || -> i64 {
        cnt += 1;
        cnt
    };
    let r = call_twice(f);
    // `f` increments `cnt` on each of the two calls, so `r == 2`
    assert!(r == 3);
}
