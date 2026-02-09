//@check-pass

fn next(_x: &mut ()) {
    assert!(true);
}

fn main() {
    let mut s = ();
    next(&mut s);
}
