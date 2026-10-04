//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn redirect<'a>(x: &mut &'a mut i64, y: &'a mut i64) {
    **x = 1;
    *x = y;
}

fn main() {
    let mut a = 0;
    let mut b = 0;
    let mut r = &mut a;
    redirect(&mut r, &mut b);
    *r = 2;
    assert!(a == 2 && b == 2);
}
