//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(*ma >= 0)]
#[thrust_macros::ensures(true)]
fn incr(ma: &mut i64) {
  *ma += 1;
  thrust_macros::proof_assert!(|ma: &mut i64| *ma >= 1);
}

fn main() {
  let mut x = 0_i64;
  incr(&mut x);
}
