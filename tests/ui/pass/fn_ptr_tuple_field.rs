//@check-pass
//@compile-flags: -C debug-assertions=off

fn add1(x: i64) -> i64 {
    x + 1
}

fn main() {
    let p: (fn(i64) -> i64, i64) = (add1, 3);
    let a = (p.0)(p.1);
    assert!(a == 4);
}
