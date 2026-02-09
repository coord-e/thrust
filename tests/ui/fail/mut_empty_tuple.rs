//@error-in-other-file: Unsat

fn next(_x: &mut ()) {
    assert!(false);
}

fn main() {
    let mut s = ();
    next(&mut s);
}
