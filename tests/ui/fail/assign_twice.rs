//@error-in-other-file: Unsat

fn main() {
    let mut x = 0_i64;
    let m = &mut x;
    *m = 1;
    *m = 2;
    assert!(x == 1);
}
