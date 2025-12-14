//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let incr = |x| {
        x + 1
    };
    assert!(incr(1) == 2);
}
