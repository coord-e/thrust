//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(0 <= start && start <= end && end <= s.len() && 0 <= i && i < end - start)]
#[thrust_macros::ensures(
    s.subsequence(start, end).len() == end - start
        && s.subsequence(start, end)[i] == s[start + i]
)]
fn subsequence_index(s: Seq<Int>, start: Int, end: Int, i: Int) {
    let _ = (s, start, end, i);
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    Seq::singleton(x).push(y).subsequence(1, 2) == Seq::singleton(y)
        && Seq::singleton(x).subsequence(0, 0) == Seq::<Int>::empty()
        && Seq::singleton(x).push(y).subsequence(0, 2).subsequence(1, 2)[0] == y
)]
fn subsequence_normalized(x: Int, y: Int) {
    let _ = (x, y);
}

fn main() {}
