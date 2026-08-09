//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `captures` lists `n` first while the closure captures `b` first; `n` still carries
// its own value, 5, so `r` is 8.
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
    assert!(r == 9);
}
