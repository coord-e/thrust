//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut v = Vec::new();
    v.push(0);
    v[0] += 1;
    v.push(1);
    assert!(v.pop().unwrap() == 1);
    assert!(v.pop().unwrap() == 1);
}
