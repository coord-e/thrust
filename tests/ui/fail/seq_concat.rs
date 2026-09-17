//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(s.concat(t).len() == s.len() + t.len() + 1)]
fn concat_lengths_add(s: Seq<Int>, t: Seq<Int>) -> () {
    let _ = s;
    let _ = t;
}

fn main() {}
