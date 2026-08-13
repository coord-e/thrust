//@check-pass
//@compile-flags: -C debug-assertions=off

// A capture named in `requires`, where the environment leads the companion's
// parameters instead of following `result` as it does for `ensures`.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let n = 5;
    let f = thrust_macros::closure!(
        captures(n: i32),
        requires(x > n),
        ensures(result == x + n),
        |x: i32| -> i32 { x + n },
    );
    let r = apply(7, f);
    assert!(r == 12);
}
