//@check-pass
//@compile-flags: -C debug-assertions=off

fn add1(x: i64) -> i64 {
    x + 1
}

// The specification has to reach a function type nested inside another type, not
// just one a local holds directly.
fn main() {
    let p: (fn(i64) -> i64,) = (add1,);
    let a = (p.0)(0);
    let b = (p.0)(a);
    assert!(b == 2);
}
