//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

#[thrust_macros::invariant_context]
fn keep<T: Copy + PartialEq>(v: T) {
  let mut x = v;
  while rand() == 0 {
    thrust_macros::invariant!(|v: thrust_models::FnParam<T>| v.is_not_changed());
    x = v;
  }
  assert!(x == v);
}

fn main() {
  keep(0_i64);
  keep(true);
}
