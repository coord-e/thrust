//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(x != y)]
#[thrust_macros::ensures(Seq::singleton(x).concat(Seq::singleton(y))[1] == x)]
fn concat_index(x: Int, y: Int) {}

fn main() {}
