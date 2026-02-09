//@check-pass

fn next<F>(f: &mut F) where F: Fn() {
    f();
}

fn main() {
    let mut f = || { assert!(true); };
    next(&mut f);
}
