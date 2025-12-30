//@error-in-other-file: Unsat

#[thrust::requires(true)]
#[thrust::ensures(x == <*x, y>)]
fn f(x: &mut i64, y: i64) {
    *x = y;
}

fn main() {
    let mut a = 1;
    f(&mut a, 2);
    assert!(a == 1);
}
