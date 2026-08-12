//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `i32::MIN.abs()` overflows and wraps back to `i32::MIN` with the overflow
// checks off, so `abs` must not be callable on an argument that may be
// `i32::MIN`.
#[thrust::callable]
fn check(x: i32) {
    if x == i32::MIN {
        let y = x.abs();
        assert!(y >= 0);
    }
}

fn main() {}
