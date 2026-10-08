//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn incr(m: &mut i64) {
    *m += 1;
}

// `x` is incremented twice, so it is 2 rather than 1 here.
fn main() {
    let f: fn(&mut i64) = incr;
    let mut x = 0;
    f(&mut x);
    f(&mut x);
    assert!(x == 1);
}
