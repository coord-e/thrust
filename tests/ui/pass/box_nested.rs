//@check-pass
//@compile-flags: -C debug-assertions=off

fn incr(x: &mut i64) {
    *x += 1;
}

fn main() {
    let mut x = Box::new(Box::new(1));
    let m = &mut **x;
    incr(m);
    assert!(**x == 2);
}
