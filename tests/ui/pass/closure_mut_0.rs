//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut x = 1;
    let mut incr = || {
        x += 1;
    };
    incr();
    assert!(x == 2);
}
