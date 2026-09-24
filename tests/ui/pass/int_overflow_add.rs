//@check-pass
//@compile-flags: -C debug-assertions=off

fn succ_widened(x: u32) -> u64 {
    (x + 1) as u64
}

fn main() {
    assert!(succ_widened(4294967295) == 0);
}
