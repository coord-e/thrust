//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust_macros::context]
trait Positive {
    #[thrust_macros::predicate]
    fn positive(self, x: i64) -> bool {
        x > 0
    }
}

impl Positive for i64 {}
impl Positive for bool {}

#[thrust_macros::requires(<i64 as Positive>::positive(x, x))]
#[thrust_macros::ensures(result > 1)]
fn positive_int(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(<bool as Positive>::positive(flag, x))]
#[thrust_macros::ensures(result > 1)]
fn positive_bool(flag: bool, x: i64) -> i64 {
    x
}

fn main() {
    assert!(positive_int(1) > 0);
    assert!(positive_bool(true, 1) > 0);
}
