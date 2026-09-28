//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;

#[thrust_macros::requires(i32::MIN <= x && x < i32::MAX)]
#[thrust_macros::ensures(result > x && forall(|y: i32| y <= x || result < y))]
fn succ(x: i32) -> i32 {
    x + 1
}

fn main() {}
