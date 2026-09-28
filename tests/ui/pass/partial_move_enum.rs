//@check-pass
//@compile-flags: -C debug-assertions=off

enum Pair<'a> {
    Two((&'a mut i64,), (&'a mut i64,)),
}

fn main() {
    let mut a = 1_i64;
    let mut b = 3_i64;
    let s = Pair::Two((&mut a,), (&mut b,));
    let Pair::Two(t, ref u) = s;
    *t.0 = 2;
    assert!(*u.0 == 3);
    assert!(a == 2);
}
