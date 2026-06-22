//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Whole-Seq equality; no `select` on the concat result, so commit 4's
// peephole does not fire — pcsat discharges this by unfolding
// `seq_concat_arr_<T>`'s definition for the constant `tn`.

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    Seq::singleton(x).concat(Seq::empty()) == Seq::singleton(x)
        && Seq::empty().concat(Seq::singleton(x)) == Seq::singleton(x)
)]
fn concat_eq_singleton(x: Int) -> () {
    let _ = x;
}

fn main() {}
