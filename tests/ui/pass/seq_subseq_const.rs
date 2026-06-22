//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Whole-Seq equality; no `select` on the subsequence result, so commit 4's
// peephole does not fire — pcsat discharges this by unfolding
// `seq_subseq_arr_int`'s definition for the constant `r - l`.

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    Seq::singleton(x).subsequence(0, 1) == Seq::singleton(x)
)]
fn subseq_eq_singleton(x: Int) -> () {
    let _ = x;
}

fn main() {}
