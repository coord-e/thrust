//@check-pass
//@compile-flags: -C debug-assertions=off

fn take_fn<T, F: Fn(i32) -> T>(f: F) -> T {
    f(41)
}

fn main() {
    let y = take_fn(|x| {
        assert!(x == 41);
        x + 1
    });
    assert!(y == 42);
}
