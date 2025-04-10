//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::requires(true)]
#[thrust::ensures(true)]
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
