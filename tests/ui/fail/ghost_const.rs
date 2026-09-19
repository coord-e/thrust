//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Seq, UInt};
use thrust_models::Ghost;

#[thrust_macros::requires(s.len() == 0)]
fn expect_empty(s: Ghost<Seq<UInt>>) {
    let _ = s;
}

fn main() {
    let s = thrust_macros::ghost!(|| -> Seq<UInt> { Seq::singleton(Seq::<UInt>::empty().len()) });
    expect_empty(s);
}
