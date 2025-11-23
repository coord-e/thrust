//@check-pass

#[thrust::requires(true)]
#[thrust::ensures(result == x)]
fn id<T>(x: T) -> T {
    x
}

#[thrust::requires(true)]
#[thrust::ensures(result == x)]
fn apply_twice<T>(x: T) -> T {
    id(id(x))
}

fn main() {
    assert!(apply_twice(42) == 42);
}
