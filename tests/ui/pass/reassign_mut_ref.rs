//@check-pass

fn main() {
    let mut a = 1_i64;
    let mut b = 2_i64;
    let mut r = &mut a;
    *r = 10;
    r = &mut b;
    *r = 20;
    assert!(a == 10);
    assert!(b == 20);
}
