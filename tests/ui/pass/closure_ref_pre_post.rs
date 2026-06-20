//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply_ref<F: Fn(i32) -> i32>(x: i32, f: &F) -> i32 {
    f(x)
}

fn main() {
    let f = |x| x + 1;
    let r = apply_ref(3, &f);
    assert!(r == 4);
}
