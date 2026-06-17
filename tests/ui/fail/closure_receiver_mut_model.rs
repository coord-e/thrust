//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=180

use thrust_models::model::{Closure, Mut};

//#[thrust_macros::requires(thrust_models::exists(
//    |mid: Closure<F>| thrust_macros::post!(Mut::new(*f, mid)(1), 2)
//        && thrust_macros::post!(Mut::new(mid, !f)(1), 3),
//))]
//fn apply<F: FnMut(i32) -> i32>(f: &mut F) {
//    assert!(f(1) == 2);
//    assert!(f(1) == 3);
//}
//
//fn main() {
//    let x = 1;
//    let mut f = move |y| x + y;
//    apply(&mut f);
//}
fn main() {}
