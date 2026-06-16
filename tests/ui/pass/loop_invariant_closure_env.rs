//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A loop invariant may compare two closures' captured environments via `closure_env`. Here `f` and
// `g` are passed the same closure `|x| x + k` (which captures `k`), so their environments are
// equal, and the loop never re-binds them, so the equality is preserved.

#[thrust_macros::invariant_context]
fn run<F: FnMut(i64) -> i64 + Copy>(f: F, g: F) {
    let mut i = 0;
    while i < 3 {
        thrust_macros::invariant!(
            |f: F, g: F, i: i64| i >= 0 && thrust_models::closure_env(f) == thrust_models::closure_env(g)
        );
        i += 1;
    }
}

fn main() {
    let k = 7;
    let c = |x| x + k;
    run(c, c);
}
