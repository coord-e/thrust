//@check-pass
//@compile-flags: -C debug-assertions=off

fn get_or(o: Option<i64>, d: i64) -> i64 {
    match o {
        Some(x) => x,
        None => d,
    }
}

fn main() {
    assert!(get_or(Some(1), 9) == 1);
    assert!(get_or(None, 9) == 9);
}
