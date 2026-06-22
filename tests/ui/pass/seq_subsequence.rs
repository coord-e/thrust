//@check-pass
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(s.subsequence(l, r).len() == r - l)]
fn subsequence_length(s: Seq<Int>, l: Int, r: Int) -> () {
    let _ = s;
    let _ = l;
    let _ = r;
}

fn main() {}
