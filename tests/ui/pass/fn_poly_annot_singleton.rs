//@check-pass
//@compile-flags: -C debug-assertions=off

#[allow(unused_variables)]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(x == x && result == 0)]
fn unit_value<T: PartialEq>(x: T) -> i64 {
    0
}

fn main() {
    assert!(unit_value(()) == 0);
}
