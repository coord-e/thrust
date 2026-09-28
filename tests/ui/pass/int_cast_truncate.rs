//@check-pass
//@compile-flags: -C debug-assertions=off

fn truncate(x: u64) -> u32 {
    x as u32
}

fn main() {
    assert!(truncate(4294967301) == 5);
}
