//@check-pass
//@compile-flags: -C debug-assertions=off

// A closure whose pre-/post-condition is given explicitly via `closure!` rather
// than inferred as predicate variables. The caller relies on the fixed spec.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x + 1),
        |x: i32| -> i32 { x + 1 },
    );
    let r = apply(3, f);
    assert!(r == 4);
}
