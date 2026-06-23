//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

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
