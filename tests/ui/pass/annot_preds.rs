//@check-pass
//@compile-flags: -Adead_code

#[thrust_macros::predicate]
fn is_double(x: i64, doubled_x: i64) -> bool {
    x * 2 == doubled_x
}

#[thrust_macros::requires(i64::MIN <= x + x && x + x <= i64::MAX)]
#[thrust_macros::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 6);
}
