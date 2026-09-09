//@check-pass
//@compile-flags: -C debug-assertions=off

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(0 <= s.len() && 0 <= t.len() && 0 <= i && i < s.len() + t.len())]
#[thrust_macros::ensures(
    s.concat(t).len() == s.len() + t.len()
        && (i >= s.len() || s.concat(t)[i] == s[i])
        && (i < s.len() || s.concat(t)[i] == t[i - s.len()])
)]
fn concat_index(s: Seq<Int>, t: Seq<Int>, i: Int) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    Seq::singleton(x).concat(Seq::singleton(y)) == Seq::singleton(x).push(y)
        && Seq::singleton(x).concat(Seq::singleton(y)).concat(Seq::singleton(z))[2] == z
)]
fn concat_normalized(x: Int, y: Int, z: Int) {}

fn main() {}
