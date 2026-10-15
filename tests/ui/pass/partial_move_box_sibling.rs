//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut a = 1_i64;
    let mut b = 2_i64;
    {
        let s = Box::new(((&mut a,), (&mut b,)));
        let t = s.0;
        *t.0 = 10;
        *s.1.0 = 20;
    }
    assert!(a == 10);
    assert!(b == 20);
}
