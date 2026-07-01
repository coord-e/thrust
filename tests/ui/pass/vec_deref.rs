//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut v: Vec<i32> = Vec::new();
    Vec::push(&mut v, 10);
    Vec::push(&mut v, 20);
    let s: &[i32] = &v;
    assert!(s.len() == 2);
    assert!(s[0] == 10);
    assert!(s[1] == 20);
}
