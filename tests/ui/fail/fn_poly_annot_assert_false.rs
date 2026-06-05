//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id<T>(x: T) -> T {
    assert!(false);
    x
}

fn main() {
    let a = id(42);
    assert!(a == 42);
}
