//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::invariant_context]
fn keep<T: Copy + PartialEq>(v: T) -> T {
  let x = v;
  thrust_macros::proof_assert!(|x: T, v: T| x == v);
  x
}

fn main() {
  keep(0_i64);
  keep(true);
}
