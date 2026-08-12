//@check-pass
//@compile-flags: -C debug-assertions=off

// `abs` keeps its postcondition on arguments that are known not to be
// `i32::MIN`, the one input where it overflows.
#[thrust::callable]
fn check(x: i32) {
    if x > 0 {
        let y = x.abs();
        assert!(y == x);
    }
    if x > i32::MIN {
        let z = x.abs();
        assert!(z >= 0);
    }
}

fn main() {}
