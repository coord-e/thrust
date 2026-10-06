//@check-pass

#[thrust::callable]
#[thrust_macros::requires(i32::MIN <= v && v < i32::MAX)]
fn check(v: i32) {
    let incr = |x| {
        x + 1
    };
    assert!(incr(v) == v + 1);
}

fn main() {}
