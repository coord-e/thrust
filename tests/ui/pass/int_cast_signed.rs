//@check-pass
//@compile-flags: -C debug-assertions=off

fn to_i32(x: u32) -> i32 {
    x as i32
}

fn main() {
    assert!(to_i32(4294967295) == -1);
}
