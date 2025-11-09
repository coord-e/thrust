//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn repeat<T>(n: i32, value: T) -> T {
    if n <= 1 {
        value
    } else {
        repeat(n - 1, repeat(1, value))
    }
}

fn identity_loop<T>(depth: i32, x: T) -> T {
    if depth == 0 {
        x
    } else {
        identity_loop(depth - 1, identity_loop(0, x))
    }
}

fn main() {
    assert!(repeat(5, 42) == 43);
}
