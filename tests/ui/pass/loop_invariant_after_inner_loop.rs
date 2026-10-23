//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut total = 0_i64;
  let mut i = 0_i64;
  while rand() == 0 {
    let mut j = 0_i64;
    while j < 3 {
      total += 1;
      j += 1;
    }
    i += 1;
    thrust_macros::invariant!(|total: i64, i: i64| total == 3 * i);
  }
  assert!(total == 3 * i);
}
