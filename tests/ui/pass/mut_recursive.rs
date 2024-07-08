//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: REFA_SOLVER_TIMEOUT_SECS=60

#![feature(register_tool)]
#![register_tool(thrust)]

#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> i64 { 0 }

fn sum(a: &mut i64, i: i64) {
    if i == 0 {
        return;
    }
    *a += 1;
    sum(a, i - 1);
}

fn main() {
    let x = rand();
    let mut y = 0;
    sum(&mut y, x);
    assert!(y == x);
}
