//@check-pass
//@compile-flags: -C debug-assertions=off

struct S<F> {
    f: F,
}

fn main() {
    let s = S {
        f: |x: i32| x + 1,
    };
    let x = (s.f)(1);
    assert!(x == 2);
}
