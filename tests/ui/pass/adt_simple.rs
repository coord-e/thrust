//@check-pass
//@compile-flags: -C debug-assertions=off

pub enum X {
    A(i64),
    B(bool),
}

fn main() {
    let x = X::A(1);
    assert!(matches!(x, X::A(i) if i == 1));
}
