//@check-pass

#[thrust_macros::requires(x == i64::MAX)]
fn only_max(x: i64) -> i64 {
    x
}

fn main() {
    let _ = only_max(9223372036854775807);
}
