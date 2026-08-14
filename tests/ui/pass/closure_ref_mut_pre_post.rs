//@check-pass
//@compile-flags: -C debug-assertions=off

// The higher-order function names the closure through a `&mut` in `pre!`/`post!`, while a
// closure that only reads its captures receives its upvars as they are.
#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn call<F: Fn() -> i64>(f: &mut F) -> i64 {
    f()
}

fn main() {
    let k: i64 = 1;
    let mut f = || -> i64 { k };
    let r = call(&mut f);
    assert!(r == 1);
}
