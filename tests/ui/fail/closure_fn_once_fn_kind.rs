//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn call_once<F: FnOnce() -> i64>(f: F) -> i64 {
    f()
}

fn main() {
    let mut x = 1;
    let r = &mut x;
    *r = 5;
    let c = move || *r;
    call_once(c);
    assert!(x == 6);
}
