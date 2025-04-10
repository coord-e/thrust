//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> i32 { unimplemented!() }

fn split<'a>((a, b): &'a mut (i32, i32)) -> (&'a mut i32, &'a mut i32) {
    (a, b)
}

fn main() {
  let mut p = (1, 1);
  let (a, b) = split(&mut p);
  *a += 1;
  assert!(p.0 == 1);
}
