//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut a = 1_i64;
    let mut b = 2_i64;
    let mut s = ((&mut a,),);
    let t = s.0;
    *t.0 = 10;
    s.0 = (&mut b,);
    assert!(a == 10);
    assert!(b == 2);
}
