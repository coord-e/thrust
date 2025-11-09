//@error-in-other-file: Unsat

fn first<T, U>(pair: (T, U)) -> T {
    pair.0
}

fn main() {
    let x = first((42, true));
    let y = first((true, 100));
    
    assert!(x == 42);
    assert!(y == false);
}
