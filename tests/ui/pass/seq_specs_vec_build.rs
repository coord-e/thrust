//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::Seq;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.length == Seq::empty().push(10).push(20).push(30).len()
        && result.array[0] == Seq::empty().push(10).push(20).push(30)[0]
        && result.array[1] == Seq::empty().push(10).push(20).push(30)[1]
        && result.array[2] == Seq::empty().push(10).push(20).push(30)[2]
)]
fn build_three() -> Vec<i64> {
    let mut v = Vec::new();
    v.push(10);
    v.push(20);
    v.push(30);
    v
}

fn main() {
    let v = build_three();
    assert!(v.len() == 3);
    assert!(v[0] == 10);
    assert!(v[1] == 20);
    assert!(v[2] == 30);
}
