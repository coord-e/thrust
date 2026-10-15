//@check-pass
//@compile-flags: -C debug-assertions=off

fn add1(x: i64) -> i64 {
    x + 1
}

// The cast that produces `f` and the call of `f` sit in different basic blocks.
// The callee's specification must survive that boundary; without it the call's
// result is unconstrained.
#[thrust::callable]
fn check(c: bool) {
    let f: fn(i64) -> i64 = add1;
    if c {
        let a = f(0);
        assert!(a == 1);
    }
}

fn main() {}
