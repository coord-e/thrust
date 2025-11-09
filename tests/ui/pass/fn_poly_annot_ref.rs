//@check-pass

#[thrust::requires(true)]
#[thrust::ensures(result == x)]
fn id_ref<T>(x: &T) -> &T {
    x
}

fn main() {
    let val = 42;
    let r = id_ref(&val);
    assert!(*r == 42);
}
