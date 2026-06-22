//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    // wrong: singleton(x).subsequence(0, 1) is singleton(x), not empty
    Seq::singleton(x).subsequence(0, 1) == Seq::<Int>::empty()
)]
fn subseq_eq_singleton(x: Int) -> () {
    let _ = x;
}

fn main() {}
