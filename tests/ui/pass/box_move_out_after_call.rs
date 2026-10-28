//@check-pass
//@compile-flags: -C debug-assertions=off

fn add(bb: Box<Box<i64>>, x: i64) -> i64 {
    let c = Box::new(x);
    let inner = *bb;
    *inner + *c
}

fn main() {
    assert!(add(Box::new(Box::new(1)), 2) == 3);
}
