//@error-in-other-file: Unsat

fn lt<T>(x: &T, y: &T) -> bool where T: Ord {
    x < y
}

fn main() {
    assert!(lt(&1, &0));
}
