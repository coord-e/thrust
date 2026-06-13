//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let arr = [1i32, 2, 3];
    let s: &[i32] = &arr;
    let v = s[0];
    assert!(v == 1);
}
