//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{
    exists,
    model::{Int, Mut},
};

// Naming the closure by value leaves its environment as the call found it, which cannot
// carry the environment from one call to the next. `Mut::new` builds the receiver instead,
// naming the environment between the two calls.
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
    assert!(r == 2);
}
