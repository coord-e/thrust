//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_UNSOUNDLY_DISABLE_INTEGER_WRAPPING=1

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn sum(i: i64) -> i64 {
    if i == 0 {
        0
    } else {
        sum(i - 1) + 1
    }
}

fn main() {
    let x = rand();
    let y = sum(x);
    assert!(y == x + 1);
}
