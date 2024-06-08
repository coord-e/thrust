//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut x = 1_i64;
    x += 1;
    x += 1;
    assert!(x == 1);
}
