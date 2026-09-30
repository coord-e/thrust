//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

fn main() {
    // `Option::map`'s spec also binds `i` around `pre!(f(i))`.
    let half = thrust_macros::closure!(
        requires(exists(|i: i64| x == i + i)),
        |x: i64| -> i64 {
            assert!(x != 3);
            x
        },
    );
    let _ = Some(4).map(half);
}
