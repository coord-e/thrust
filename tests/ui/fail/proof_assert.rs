//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64) -> i64 {
  let m = n + 1;
  thrust_macros::proof_assert!(|m: i64| m >= 2);
  m
}

fn main() {
  f(0);
}
