//@error-in-other-file: Unsat

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(-1000 <= result && result <= 1000)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn incr(m: &mut i64) {
    *m += 1;
}

fn app(f: fn(&mut i64), mut x: i64) -> i64 {
    f(&mut x);
    x
}

fn main() {
    let i = rand();
    let x = app(incr, i);
    assert!(x == i);
}
