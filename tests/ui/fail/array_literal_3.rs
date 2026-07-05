//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut arr = [1i32, 2, 3];
    let s: &mut [i32] = &mut arr;
    s[0] = 42;
    assert!(s[0] == 1); // old value → Unsat
}
