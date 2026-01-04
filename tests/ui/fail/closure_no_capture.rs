//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let incr = |x| {
        x + 1
    };
    assert!(incr(2) == 2);
}
