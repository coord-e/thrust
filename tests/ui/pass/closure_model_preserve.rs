//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::ensures(result == f)]
fn call<F: FnMut() -> i32>(mut f: F) -> F {
    f();
    f
}

fn main() {
    let x = 2;
    let mut f = call(|| {
        x
    });
    assert!(f() == 2);
}
