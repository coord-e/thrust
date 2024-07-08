//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(thrust)]

#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> i64 { 1 }

fn main() {
  let mut x = 1_i64;
  let mut y = 1_i64;
  while rand() == 0 {
    let t1 = x;
    let t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  assert!(y >= 2);
}
