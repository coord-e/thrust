//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut x = 1i32;
    let mut y = 2i32;
    let arr: [&mut i32; 2] = [&mut x, &mut y];
    let vx = *arr[0];
    assert!(vx == 99);
}
