//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut v = Vec::new();
    v.push(0);
    assert!(v.len() == 0);
}
