//@check-pass

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut x = 1_i64;
  while x < 1000 && rand() == 0 {
    let mut y = 1_i64;
    while y < 1000 && rand() == 0 {
      thrust_macros::invariant!(|x: i64, y: i64| x >= 1 && x < 1000 && y >= 1 && y < 2000);
      y = x + y;
    }
    x = x + y;
  }
  assert!(x >= 1);
}
