#[thrust_macros::ensures(result >= a)]
pub fn max(a: i64, b: i64) -> i64 {
    if a >= b {
        a
    } else {
        b
    }
}
