//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(0 <= l && l <= r && r <= s.len() && 0 <= i && i < r - l)]
#[thrust_macros::ensures(s.subsequence(l, r)[i] == s[i])]
fn subseq_index(s: Seq<Int>, l: Int, r: Int, i: Int) -> () {
    let _ = s;
    let _ = l;
    let _ = r;
    let _ = i;
}

fn main() {}
