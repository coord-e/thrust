//@error-in-other-file: Unsat

pub enum X<T> {
    A(T),
    B(T),
}

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand<T>() -> X<T> { unimplemented!() }

fn is_a<T>(x: &X<T>) -> bool {
    match x {
        X::A(_) => true,
        X::B(_) => false,
    }
}

fn inv<T>(x: X<T>) -> X<T> {
    match x {
        X::A(i) => X::B(i),
        X::B(i) => X::A(i),
    }
}

fn rand_a<T>() -> X<T> {
    let x = rand();
    if !is_a(&x) { loop {} }
    x
}

#[thrust::callable]
fn check<T>() {
    let x = rand_a::<T>();
    assert!(is_a(&inv(x)));
}

fn main() {}
