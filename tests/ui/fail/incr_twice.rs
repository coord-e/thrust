//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn incr(m: &mut i64, x: i64) {
    let v = *m;
    *m = v + x;
}

fn main() {
    let mut x = 0_i64;
    let m = &mut x;
    incr(m, 1);
    incr(m, 2);
    assert!(x == 2);
}
