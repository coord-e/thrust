//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn apply<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(1)
}

fn main() {
    let x = 1;
    let closure = |y: i32| x + y;
    let result = apply(closure);
    assert!(result == 1);
}
