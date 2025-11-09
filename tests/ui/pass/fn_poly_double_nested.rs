//@check-pass

fn id<T>(x: T) -> T {
    x
}

fn apply_twice<T>(x: T) -> T {
    id(id(x))
}

fn apply_thrice<T>(x: T) -> T {
    apply_twice(id(x))
}

fn apply_four<T>(x: T) -> T {
    apply_twice(apply_twice(x))
}

fn main() {
    assert!(apply_four(42) == 42);
    assert!(apply_thrice(true) == true);
}
