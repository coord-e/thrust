//@check-pass

fn first<T, U>(pair: (T, U)) -> T {
    pair.0
}

fn main() {
    let x = first((42, true));
    let y = first((true, 100));
    let z = first(((1, 2), 3));
    
    assert!(x == 42);
    assert!(y == true);
    assert!(z.0 == 1);
}
