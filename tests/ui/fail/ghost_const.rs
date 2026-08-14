//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::requires(s.len() == 0)]
fn expect_empty(s: Ghost<Seq<Int>>) {
    let _ = s;
}

fn main() {
    let s = thrust_macros::ghost!(|| -> Seq<Int> { Seq::singleton(Seq::<Int>::empty().len()) });
    expect_empty(s);
}
