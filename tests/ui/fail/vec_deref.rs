//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut v: Vec<i32> = Vec::new();
    Vec::push(&mut v, 10);
    Vec::push(&mut v, 20);
    let s: &[i32] = &v;
    assert!(s[0] == 99); // wrong value → Unsat
}
