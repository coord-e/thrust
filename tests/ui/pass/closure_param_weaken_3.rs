//@check-pass
//@compile-flags: -C debug-assertions=off

fn apply<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(1)
}

fn main() {
    let mut x = 1;
    let closure = |y: i32| {
        x += 1;
        y + x
    };
    let result = apply(closure);
    assert!(result == 3 && x == 2);
}
