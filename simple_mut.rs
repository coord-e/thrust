fn main() {
    let mut a = 1_i64;
    let m = &mut a;
    *m = 2;
    assert!(a == 2);
}
