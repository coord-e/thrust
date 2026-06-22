//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    // wrong: swap order
    result.1 == Seq::<Int>::singleton(x).concat(Seq::<Int>::singleton(y)).len()
        && result.0[0] == Seq::<Int>::singleton(y).concat(Seq::<Int>::singleton(x))[0]
        && result.0[1] == Seq::<Int>::singleton(y).concat(Seq::<Int>::singleton(x))[1]
)]
fn pair(x: i64, y: i64) -> Vec<i64> {
    let mut v = Vec::new();
    v.push(x);
    v.push(y);
    v
}

fn main() {}
