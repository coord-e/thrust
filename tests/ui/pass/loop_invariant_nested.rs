//@check-pass

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

const HALF_MAX: i64 = i64::MAX / 2;

fn main() {
  let mut x = 1_i64;
  while x <= HALF_MAX && rand() == 0 {
    let mut y = 1_i64;
    while y <= HALF_MAX - x && rand() == 0 {
      thrust_macros::invariant!(|x: i64, y: i64| x >= 1 && x <= HALF_MAX && y >= 1 && y <= HALF_MAX);
      y = x + y;
    }
    x = x + y;
  }
  assert!(x >= 1);
}
