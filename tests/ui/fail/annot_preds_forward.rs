//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust_macros::predicate]
fn positive(x: i64) -> bool {
    nonnegative(x) && nonzero(x)
}

#[thrust_macros::predicate]
fn nonnegative(x: i64) -> bool {
    !negative(x)
}

#[thrust_macros::predicate]
fn nonzero(x: i64) -> bool {
    x != 0
}

#[thrust_macros::predicate]
fn negative(x: i64) -> bool {
    x < 0
}

#[thrust_macros::requires(positive(x))]
#[thrust_macros::ensures(result > 1)]
fn identity(x: i64) -> i64 {
    x
}

fn main() {
    identity(1);
}
