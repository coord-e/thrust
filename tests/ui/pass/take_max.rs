//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::requires(true)]
#[thrust::ensures(true)]
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
