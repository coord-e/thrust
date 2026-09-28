//@check-pass
//@compile-flags: -C debug-assertions=off

use thrust_models::forall;

#[thrust_macros::requires(forall(|v1: i32| v1 != x || v1 > 0))]
fn f(x: i32) {
    assert!(x > 0);
}

fn main() {
    let a = 1;
    let b = a + 1;
    f(b);
}
