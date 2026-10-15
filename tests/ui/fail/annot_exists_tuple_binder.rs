//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|p: (i64, bool)| result < 0))]
fn f() -> i64 {
    1
}

fn main() {}
