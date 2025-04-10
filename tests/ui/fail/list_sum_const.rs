//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C opt-level=3
//@rustc-env: THRUST_SOLVER_TIMEOUT_SECS=120

enum List {
  Cons(i32, Box<List>),
  Nil,
}

fn sum(la: &List) -> i32 {
  match la {
    List::Cons(x, lb) => sum(lb) + *x,
    List::Nil => 0,
  }
}

fn main() {
  let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
  assert!(sum(&list) == 2);
}
