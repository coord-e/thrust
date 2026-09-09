//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off


use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(x != y)]
#[thrust_macros::ensures(Seq::singleton(x).push(y).subsequence(1, 2)[0] == x)]
fn subsequence_index(x: Int, y: Int) {}

fn main() {}
