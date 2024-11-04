//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=3
//@rustc-env: REFA_SOLVER_TIMEOUT_SECS=120

enum List {
  Cons(i32, Box<List>),
  Nil,
}

fn length(la: &List) -> i32 {
  match la {
    List::Cons(_, lb) => length(lb) + 1,
    List::Nil => 0,
  }
}

fn main() {
  let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
  assert!(length(&list) == 2);
}
