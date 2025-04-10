//@check-pass
//@compile-flags: -C debug-assertions=off

pub enum X {
    A(i64),
    B(bool),
}

fn main() {
    let x = X::B(true);
    assert!(matches!(x, X::B(b)));
}
