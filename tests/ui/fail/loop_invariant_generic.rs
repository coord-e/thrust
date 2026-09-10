//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

#[thrust_macros::context]
fn keep<T: Copy + PartialEq>(v: T) {
  let mut x = v;
  while rand() == 0 {
    thrust_macros::invariant!(|v: T| v == v);
    x = v;
  }
  assert!(x == v);
}

fn main() {
  keep(0_i64);
  keep(true);
}
