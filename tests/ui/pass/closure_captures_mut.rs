//@check-pass
//@compile-flags: -C debug-assertions=off

// A capture taken by mutable borrow is named as the `&mut` it is, so that the clause
// can say both what it was on entry (`*acc`) and what it becomes (`!acc`).
//
// The closure is passed straight to `apply`: binding it to a `let` first would have it
// called through `&mut`, which a specification cannot name its captures through yet.
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
