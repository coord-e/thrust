//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Same shape as the pass counterpart (the invariant still compares the closures' environments via
// `closure_env`), but `f` and `g` are the same closure, so claiming their environments *differ* is
// false on entry and verification fails with `Unsat`.

#[thrust_macros::invariant_context]
fn run<F: FnMut(i64) -> i64 + Copy>(f: F, g: F) {
    let mut i = 0;
    while i < 3 {
        thrust_macros::invariant!(
            |f: F, g: F, i: i64| i >= 0 && !(thrust_models::closure_env(f) == thrust_models::closure_env(g))
        );
        i += 1;
    }
}

fn main() {
    let k = 7;
    let c = |x| x + k;
    run(c, c);
}
