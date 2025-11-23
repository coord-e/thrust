//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut x = 1;
    let mut incr = |by: i32| {
        x += by;
    };
    incr(5);
    incr(5);
    assert!(x == 10);
}
