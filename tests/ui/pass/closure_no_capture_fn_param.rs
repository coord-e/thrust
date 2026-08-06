//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::callable]
fn check(v: i32) {
    let incr = |x| {
        x + 1
    };
    assert!(incr(v) == v + 1);
}

fn main() {}
