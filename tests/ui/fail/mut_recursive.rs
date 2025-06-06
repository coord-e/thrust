//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::requires(true)]
#[thrust::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

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
    assert!(y == x + 1);
}
