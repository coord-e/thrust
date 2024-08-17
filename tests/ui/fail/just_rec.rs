//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(thrust)]

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> i32 { unimplemented!() }

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand_bool() -> bool { unimplemented!() }

fn just_rec(ma: &mut i32) {
  if rand_bool() {
    return;
  }
  let mut b = rand();
  just_rec(&mut b);
}
fn main() {
  let mut a = rand();
  let a0 = a;
  just_rec(&mut a);
  assert!(a0 > a);
}
