//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

struct Counter;

impl Counter {
  fn run(&self) {
    let mut x = 1_i64;
    while rand() == 0 {
      thrust_macros::invariant!(|x: i64| x >= 1);
      x = x + 1;
    }
    assert!(x >= 1);
  }
}

fn main() {
  Counter.run();
}
