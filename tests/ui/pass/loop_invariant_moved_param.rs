//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A loop invariant may refer to a function parameter even when it is no longer a live local at
// the loop header: `init` is consumed into `acc` before the loop, so it is dead there, but its
// entry value is still available as the basic block's outer-fn-param.

#[thrust_macros::invariant_context]
fn run(init: i64) -> i64 {
    let mut acc = init;
    let mut i = 0;
    while i < 3 {
        thrust_macros::invariant!(|acc: i64, i: i64, init: i64| i >= 0 && acc >= init);
        acc += 1;
        i += 1;
    }
    acc
}

fn main() {
    let _ = run(7);
}
