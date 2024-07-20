//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut x = Box::new(1_i64);
    let m: &mut i64 = &mut *x;
    *m = 2;
    assert!(*x == 1);
}
