//@check-pass

fn id<'a>(m: &'a mut i64) -> &'a mut i64 {
    m
}

fn main() {
    let mut x = 1_i64;
    let m = id(&mut x);
    *m = 2;
    assert!(x == 2);
}
