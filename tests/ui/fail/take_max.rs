//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(refa)]

#[refa::requires(true)]
#[refa::ensures(true)]
fn rand() -> i64 { 0 }

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
  assert!(a == b);
}
