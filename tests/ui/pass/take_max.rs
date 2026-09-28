//@check-pass

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(-1000 <= result && result <= 1000)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn take_max<'a>(ma: &'a mut i64, mb: &'a mut i64) -> &'a mut i64 {
  if *ma >= *mb {
    ma
  } else {
    mb
  }
}

fn main() {
  let mut a = rand();
  let mut b = rand();
  let mc = take_max(&mut a, &mut b);
  *mc += 1;
  assert!(a != b);
}
