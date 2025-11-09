//@check-pass

fn id<T>(x: T) -> T {
    x
}

fn apply_twice<T>(x: T) -> T {
    id(id(x))
}

fn apply_thrice<T>(x: T) -> T {
    id(apply_twice(x))
}

fn main() {
    assert!(apply_thrice(42) == 42);
    assert!(apply_twice(true) == true);
}
