//@check-pass
//@compile-flags: -C debug-assertions=off

// Passed straight to `apply` to keep the closure `FnOnce`: binding it to a `let` first
// makes it `FnMut`, and `pre!`/`post!` hand a `FnMut` closure an environment stripped
// of its `Mut`.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let mut acc = 0;
    let r = apply(
        3,
        thrust_macros::closure!(
            captures(acc: &mut i32),
            ensures(result == x + 1 && !acc == *acc + 1),
            |x: i32| -> i32 { acc += 1; x + acc },
        ),
    );
    assert!(r == 4);
}
