//@check-pass
//@compile-flags: -C debug-assertions=off

// A closure that declares only `requires`; its postcondition stays inferred as a
// predicate variable, so the caller still learns the body's exact result.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let f = thrust_macros::closure!(
        requires(x > 0),
        |x: i32| -> i32 { x + 1 },
    );
    let r = apply(3, f);
    assert!(r == 4);
}
