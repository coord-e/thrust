//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1

struct S {
    b: Box<i64>,
}

fn main() {
    let mut s = S { b: Box::new(1) };
    *s.b += 1;
    assert!(*s.b == 2);
}
