//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_UNSOUNDLY_DISABLE_INTEGER_WRAPPING=1

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut x = 1_i64;
  let mut y = 1_i64;
  while rand() == 0 {
    thrust_macros::invariant!(|x: i64| x >= 1);
    let t1 = x;
    let t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  assert!(y >= 1);
}
