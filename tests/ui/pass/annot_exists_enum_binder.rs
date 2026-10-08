//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

pub enum X {
    A(i64),
    B(bool),
}

impl thrust_models::Model for X {
    type Ty = X;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|x: X| result >= 0))]
fn f() -> i64 {
    1
}

fn main() {}
