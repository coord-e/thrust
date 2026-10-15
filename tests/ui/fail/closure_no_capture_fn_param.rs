//@error-in-other-file: Unsat

#[thrust::callable]
#[thrust_macros::requires(i32::MIN <= v && v < i32::MAX)]
fn check(v: i32) {
    let incr = |x| {
        x + 1
    };
    assert!(incr(v) == v);
}

fn main() {}
