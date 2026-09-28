//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

struct Holder<T> {
    value: T,
}

#[thrust_macros::context]
impl<T> Holder<T> {
    #[thrust_macros::predicate]
    fn positive(value: T, x: i64) -> bool {
        Self::nonnegative(value, x) && x != 0
    }

    #[thrust_macros::predicate]
    fn nonnegative(value: T, x: i64) -> bool {
        x >= 0
    }
}

#[thrust_macros::requires(Holder::<i64>::positive(x, x))]
#[thrust_macros::ensures(result > 0)]
fn positive_int(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(Holder::<bool>::positive(flag, x))]
#[thrust_macros::ensures(result > 0)]
fn positive_bool(flag: bool, x: i64) -> i64 {
    x
}

fn main() {
    assert!(positive_int(1) > 0);
    assert!(positive_bool(true, 1) > 0);
}
