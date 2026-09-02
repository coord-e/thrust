//@check-pass
//@compile-flags: -C debug-assertions=off

mod math {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result >= a && result >= b)]
    pub fn max(a: i64, b: i64) -> i64 {
        if a >= b {
            a
        } else {
            b
        }
    }
}

fn main() {
    assert!(math::max(1, 2) >= 2);
}
