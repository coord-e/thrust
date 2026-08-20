//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn add1(x: i64) -> i64 {
    x + 1
}

// `add1` is applied twice, so the result is 2 rather than 1.
fn main() {
    let p: (fn(i64) -> i64,) = (add1,);
    let a = (p.0)(0);
    let b = (p.0)(a);
    assert!(b == 1);
}
