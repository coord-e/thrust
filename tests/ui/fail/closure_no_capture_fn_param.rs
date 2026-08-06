//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::callable]
fn check(v: i32) {
    let incr = |x| {
        x + 1
    };
    assert!(incr(v) == v);
}

fn main() {}
