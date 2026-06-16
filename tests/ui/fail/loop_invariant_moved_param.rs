//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Same shape as the `pass` counterpart (the invariant still refers to the moved parameter `init`),
// but `acc >= init + 1` does not hold on entry (`acc == init`), so the invariant is not inductive
// and verification fails with `Unsat`.

#[thrust_macros::invariant_context]
fn run(init: i64) -> i64 {
    let mut acc = init;
    let mut i = 0;
    while i < 3 {
        thrust_macros::invariant!(|acc: i64, i: i64, init: i64| i >= 0 && acc >= init + 1);
        acc += 1;
        i += 1;
    }
    acc
}

fn main() {
    let _ = run(7);
}
