//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::requires(true)]
#[thrust::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut x = 1_i64;
  let mut y = 1_i64;
  while rand() == 0 {
    let t1 = x;
    let t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  assert!(y >= 1);
}
