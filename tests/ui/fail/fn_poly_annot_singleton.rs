//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(x == x && result == 1)]
fn unit_value<T: PartialEq>(x: T) -> i64 {
    0
}

fn main() {
    assert!(unit_value(()) == 0);
}
