//@error-in-other-file: Unsat

fn next<F>(f: &mut F) where F: Fn() {
    f();
}

fn main() {
    let mut f = || { assert!(false); };
    next(&mut f);
}
