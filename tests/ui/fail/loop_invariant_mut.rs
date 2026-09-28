//@error-in-other-file: Unsat

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut x = 5_i64;
  let p = &mut x;
  while *p < 1000 && rand() == 0 {
    thrust_macros::invariant!(|p: &mut i64| *p >= 1);
    *p = *p - 1;
  }
  assert!(*p >= 1);
}
