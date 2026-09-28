//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut x = 1_i64;
  let mut y = 1_i64;
  while x < 1000 && y < 1000 && rand() == 0 {
    let t1 = x;
    let t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  assert!(y >= 1);
}
