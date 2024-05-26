//@check-pass

fn swap(x: &mut i64, y: &mut i64) {
    let v = *x;
    *x = *y;
    *y = v;
}

fn main() {
    let mut a = 1;
    let mut b = 3;
    swap(&mut a, &mut b);
    assert!(a == 3);
    assert!(b == 1);
}
