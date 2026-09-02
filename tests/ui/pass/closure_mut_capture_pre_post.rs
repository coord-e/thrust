//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
// A closure that mutates a capture receives its upvars behind a `Mut`, while the
// higher-order function names the closure by value in `pre!`/`post!`.
#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(thrust_macros::post!(f(), result))]
fn call<F: FnMut() -> i64>(mut f: F) -> i64 {
    f()
}

fn main() {
    let mut cnt: i64 = 0;
    let f = || -> i64 {
        cnt += 1;
        cnt
    };
    let r = call(f);
    assert!(r == 1);
}
