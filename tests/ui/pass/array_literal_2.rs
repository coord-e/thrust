//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let arr = [0i32, 0, 0, 0];
    let s: &[i32] = &arr;
    let _ = s[3];
}
