//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut a = 1_i64;
    let mut b = 2_i64;
    {
        let s = (Box::new(((&mut a,), (&mut b,))),);
        let t = s.0.0;
        *t.0 = 10;
        *s.0.1.0 = 20;
    }
    assert!(a + 100 == 10);
    assert!(b == 20);
}
