//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let x: u8 = 255;
    assert!(x > 200);
}
