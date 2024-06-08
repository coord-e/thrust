//@error-in-other-file: Unsat

fn set(m: &mut i64) {
    *m = 1;
}

fn main() {
    let mut x = 0_i64;
    let m = &mut x;
    set(m);
    set(m);
    assert!(x == 0);
}
