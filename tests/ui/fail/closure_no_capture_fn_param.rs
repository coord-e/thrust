//@error-in-other-file: Unsat

#[thrust::callable]
#[thrust_macros::requires(-1000 <= v && v <= 1000)]
fn check(v: i32) {
    let incr = |x| {
        x + 1
    };
    assert!(incr(v) == v);
}

fn main() {}
