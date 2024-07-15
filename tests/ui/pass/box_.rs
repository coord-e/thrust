//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut x = Box::new(1_i64);
    let m: &mut i64 = &mut *x;
    *m = 2;
    assert!(*x == 2);
    let m: &mut Box<i64> = &mut x;
    *m = Box::new(3);
    assert!(*x == 3);
}
