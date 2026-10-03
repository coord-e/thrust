//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust_macros::predicate]
fn is_sum_to(n: i64, sum: i64) -> bool {
    (n <= 0 && sum == 0) || (n > 0 && is_sum_to(n - 1, sum - n))
}

#[thrust_macros::requires(n == 3)]
#[thrust_macros::ensures(is_sum_to(n, result))]
fn sum_to(n: i64) -> i64 {
    6
}

fn main() {
    sum_to(3);
}
