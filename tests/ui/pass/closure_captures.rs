//@check-pass
//@compile-flags: -C debug-assertions=off

// A closure specification naming a captured variable. `n` is captured by reference,
// which the specification reads through: the clause names the variable, not the borrow.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let n = 5;
    let f = thrust_macros::closure!(
        captures(n: i32),
        ensures(result == x + n),
        |x: i32| -> i32 { x + n },
    );
    let r = apply(3, f);
    assert!(r == 8);
}
