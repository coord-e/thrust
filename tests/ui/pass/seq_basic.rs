//@check-pass
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    Seq::<Int>::empty().len() == 0
        && Seq::singleton(x).len() == 1
        && Seq::singleton(x)[0] == x
        && s.push(x).len() == s.len() + 1
        && s.push(x)[s.len()] == x
)]
fn seq_basic(s: Seq<Int>, x: Int) -> () {
    let _ = s;
    let _ = x;
}

fn main() {}
