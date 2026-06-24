//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{exists, model::{Mut, Int}};

#[thrust_macros::ensures(exists(|g, i: Int|
  thrust_macros::post!(Mut::new(*f, g)(), i)
  && thrust_macros::post!(Mut::new(g, !f)(), result)
))]
fn call_twice<F: FnMut() -> i32>(f: &mut F) -> i32 {
    f();
    f()
}

fn main() {
    let mut x = 1;
    let mut f = move || {
        x += 1;
        x
    };
    let r = call_twice(&mut f);
    assert!(r == 3);
}
