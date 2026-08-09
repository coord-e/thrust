//@check-pass
//@compile-flags: -C debug-assertions=off

// The closure captures `b` before `n`, since that is the order its body first uses
// them, while `captures` lists `n` first. Matching the two up by name is what makes
// `n` resolve to the second captured value rather than the first.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let n = 5;
    let b = true;
    let f = thrust_macros::closure!(
        captures(n: i32, b: bool),
        ensures(result == x + n),
        move |x: i32| -> i32 { if b { x + n } else { x } },
    );
    let r = apply(3, f);
    assert!(r == 8);
}
