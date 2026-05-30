//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
  let mut x = 5_i64;
  let p = &mut x;
  while rand() == 0 {
    thrust_macros::invariant!(|p: &mut i64| *p >= 1);
    *p = *p - 1;
  }
  assert!(*p >= 1);
}
