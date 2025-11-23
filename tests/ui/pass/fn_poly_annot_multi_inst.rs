//@check-pass

#[thrust::requires(true)]
#[thrust::ensures(result == x)]
fn id<T>(x: T) -> T {
    x
}

fn main() {
    let a = id(42);
    assert!(a == 42);
    
    let b = id(true);
    assert!(b == true);
    
    let c = id((1, 2));
    assert!(c.0 == 1);
}
