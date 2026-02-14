//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut v = Vec::new();
    v.push(0);
    v.push(1);
    v.push(2);
    assert!(v.len() == 3);
    v.truncate(1);
    assert!(v[0] == 0);
    v.clear();
    assert!(v.len() == 0);
}
