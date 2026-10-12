//@check-pass
//@compile-flags: -C debug-assertions=off

struct S {
    a: i64,
}

impl thrust_models::Model for S {
    type Ty = Self;
}

fn id(x: i64) -> i64 {
    x
}

fn f(mut s: S) -> i64 {
    let t = s;
    s = S { a: id(t.a + 1) };
    if id(0) == 0 {}
    s.a
}

fn main() {
    assert!(f(S { a: 0 }) == 1);
}
