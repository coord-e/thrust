//@error-in-other-file: Unsat

#[thrust::requires(true)]
#[thrust::ensures(result != x.0)]
fn left<T, U>(x: (T, U)) -> T {
    x.0
}

fn main() {
    assert!(left((42, 0)) == 42);
}
