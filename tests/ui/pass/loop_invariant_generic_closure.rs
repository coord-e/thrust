//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

// A closure-typed generic param must not be given a `Model` bound: the
// invariant only constrains the `Model`-typed `T`, and `keep` must still be
// callable with a real closure.
#[thrust_macros::invariant_context]
fn keep<F: Fn(i64) -> i64, T: Copy + PartialEq>(f: F, v: T) {
  let _ = f;
  let mut x = v;
  while rand() == 0 {
    thrust_macros::invariant!(|x: T, v: T| x == v);
    x = v;
  }
  assert!(x == v);
}

fn main() {
  keep(|x| x + 1, 0_i64);
  keep(|x| x, true);
}
