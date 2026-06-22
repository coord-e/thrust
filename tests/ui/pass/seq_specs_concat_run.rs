//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq};

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.1 == Seq::<Int>::singleton(x).concat(Seq::<Int>::singleton(y)).len()
        && result.0[0] == Seq::<Int>::singleton(x).concat(Seq::<Int>::singleton(y))[0]
        && result.0[1] == Seq::<Int>::singleton(x).concat(Seq::<Int>::singleton(y))[1]
)]
fn pair(x: i64, y: i64) -> Vec<i64> {
    let mut v = Vec::new();
    v.push(x);
    v.push(y);
    v
}

fn main() {
    let v = pair(7, 8);
    assert!(v.len() == 2);
    assert!(v[0] == 7);
    assert!(v[1] == 8);
}
