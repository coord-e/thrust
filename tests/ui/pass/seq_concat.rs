//@check-pass
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(s.concat(t).len() == s.len() + t.len())]
fn concat_lengths_add(s: Seq<Int>, t: Seq<Int>) -> () {
    let _ = s;
    let _ = t;
}

fn main() {}
