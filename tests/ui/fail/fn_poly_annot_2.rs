//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_UNSOUNDLY_DISABLE_INTEGER_WRAPPING=1

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id<T>(x: i32, _t: T) -> i32 {
    x + 1
}

fn main() {
    let _ = id(0, true);
}
