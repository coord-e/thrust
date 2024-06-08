//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn add(x: i64, y: i64) -> i64 {
    x + y
}

fn main() {
    let x = 1;
    let y = 2;
    assert!(add(x, y) == 2);
}
