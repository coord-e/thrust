//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn neg(x: i32) -> i32 {
    -x
}

fn main() {
    assert!(neg(-2147483648) == 2147483647);
}
