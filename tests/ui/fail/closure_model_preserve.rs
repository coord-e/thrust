//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::ensures(result == f)]
fn call<F: FnMut()>(mut f: F) -> F {
    f();
    f
}

fn main() {
    let mut x = 1;
    call(|| {
        x += 1;
    });
}
