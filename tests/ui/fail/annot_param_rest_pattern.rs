//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == d)]
fn last((_a, .., _c, d): (i64, i64, i64, i64)) -> i64 {
    _c
}

fn main() {
    last((1, 2, 3, 4));
}
