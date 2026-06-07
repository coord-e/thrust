//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<T, F: FnOnce(T) -> T>(x: T, f: F) -> T {
    f(x)
}

fn call_apply<T>(x: T) -> T {
    apply(x, |y| y)
}

fn main() {
    let r = call_apply(3);
    assert!(r == 3);
}
