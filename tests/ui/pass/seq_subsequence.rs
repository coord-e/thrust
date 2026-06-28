//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(0 <= start && start <= end && end <= s.len())]
#[thrust_macros::ensures(
    s.subsequence(start, end).len() == end - start
        && ((start < end) ==> (s.subsequence(start, end)[0] == s[start]))
        && ((start < end) ==> (
            s.subsequence(start, end).concat(s.subsequence(start, end))[end - start] == s[start]
        ))
)]
fn seq_subsequence(s: Seq<Int>, start: Int, end: Int) {
    let _ = (s, start, end);
}

fn main() {}
