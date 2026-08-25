//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::requires(s.len() == 1)]
fn expect_len_one(s: Ghost<Seq<Int>>) {
    let _ = s;
}

fn main() {
    let x: i64 = 3;
    let s = thrust_macros::ghost!(|x: i64| -> Seq<Int> { Seq::singleton(x).push(x) });
    expect_len_one(s);
}
