//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn add1(x: i64) -> i64 {
    x + 1
}

// `add1(0)` is 1 rather than 0.
#[thrust::callable]
fn check(c: bool) {
    let f: fn(i64) -> i64 = add1;
    if c {
        let a = f(0);
        assert!(a == 0);
    }
}

fn main() {}
