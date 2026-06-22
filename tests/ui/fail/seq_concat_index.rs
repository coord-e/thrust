//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(0 <= i && i < s.len())]
#[thrust_macros::ensures(s.concat(t)[i] == t[i])]
fn concat_index_left(s: Seq<Int>, t: Seq<Int>, i: Int) -> () {
    let _ = s;
    let _ = t;
    let _ = i;
}

fn main() {}
