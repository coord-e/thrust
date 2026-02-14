//@check-pass
//@compile-flags: -C debug-assertions=off

fn apply<F>(mut f: F) -> i32
where
    F: FnMut(i32) -> i32,
{
    f(1) + f(2)
}

fn main() {
    let x = 1;
    let closure = |y: i32| x + y;
    let result = apply(closure);
    assert!(result == 5);
}
