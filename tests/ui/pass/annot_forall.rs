//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;

#[thrust_macros::requires(-1000 <= x && x <= 1000)]
#[thrust_macros::ensures(result > x && forall(|y: i32| y <= x || result <= y))]
fn succ(x: i32) -> i32 {
    x + 1
}

fn main() {}
