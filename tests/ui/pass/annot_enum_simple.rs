//@check-pass

pub enum X {
    A(i64),
    B(bool),
}

#[thrust::requires(x == X::A(1))]
#[thrust::ensures(true)]
fn test(x: X) {
    if let X::A(i) = x {
        assert!(i == 1);
    } else {
        loop {}
    }
}

fn main() {
    test(X::A(1));
}
