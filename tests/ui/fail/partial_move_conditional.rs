//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn check(take: bool) {
    let mut a = 1_i64;
    let mut b = 2_i64;
    let s = ((&mut a,), (&mut b,));
    if take {
        let t = s.0;
        *t.0 = 10;
    }
    *s.1.0 = 20;
    assert!(a + 100 == if take { 10 } else { 1 });
    assert!(b == 20);
}

fn main() {
    check(false);
    check(true);
}
