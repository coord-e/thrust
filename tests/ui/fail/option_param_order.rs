//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn get_or(o: Option<i64>, d: i64) -> i64 {
    match o {
        Some(x) => x,
        None => d,
    }
}

fn main() {
    assert!(get_or(Some(1), 9) == 1);
    // `get_or` returns the default in the `None` case, so this assertion does not hold
    assert!(get_or(None, 9) == 1);
}
