//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::ensures(result == f)]
fn call<F: FnMut() -> i32>(mut f: F) -> F {
    f();
    f
}

fn main() {
    let mut x = 1;
    let mut f = call(|| {
        let y = x;
        x += 1;
        y
    });
    assert!(f() == 2);
}
