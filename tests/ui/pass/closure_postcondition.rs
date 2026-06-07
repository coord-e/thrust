//@check-pass
//@compile-flags: -C debug-assertions=off

// A higher-order function whose specification refers to the pre-/post-conditions
// of its closure argument.
#[thrust_macros::requires(thrust_models::model::closure_precondition(&(f), (x,)))]
#[thrust_macros::ensures(thrust_models::model::closure_postcondition(&(f), (x,), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

fn main() {
    let r = apply(3, |y| y + 1);
    assert!(r == 4);
}
