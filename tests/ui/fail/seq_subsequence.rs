//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(x != y)]
#[thrust_macros::ensures(Seq::singleton(x).push(y).subsequence(1, 2)[0] == x)]
fn subsequence_index(x: Int, y: Int) {
    let _ = (x, y);
}

fn main() {}
