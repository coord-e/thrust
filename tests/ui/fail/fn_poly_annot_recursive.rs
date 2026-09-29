//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_UNSOUNDLY_DISABLE_INTEGER_WRAPPING=1

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == value)]
fn repeat<T>(n: i32, value: T) -> T {
    if n == 0 {
        value
    } else {
        repeat(n - 1, value)
    }
}

fn main() {
    let result = repeat(-1, 42);
    assert!(result == 42);
}
