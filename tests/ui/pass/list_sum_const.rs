//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=3
//@rustc-env: REFA_SOLVER_TIMEOUT_SECS=60

#![feature(register_tool)]
#![register_tool(thrust)]

enum List {
  Cons(i32, Box<List>),
  Nil,
}

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> i32 { unimplemented!() }

fn sum(la: &List) -> i32 {
  match la {
    List::Cons(x, lb) => sum(lb) + *x,
    List::Nil => 0,
  }
}

fn main() {
  let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
  assert!(sum(&list) == 3);
}
