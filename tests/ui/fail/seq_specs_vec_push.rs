//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(true)]
// wrong: result.0[v.1] should be x, not x + 1
#[thrust_macros::ensures(result.1 == v.1 + 1 && result.0[v.1] == x + 1)]
fn snoc(mut v: Vec<i64>, x: i64) -> Vec<i64> {
    v.push(x);
    v
}

fn main() {}
