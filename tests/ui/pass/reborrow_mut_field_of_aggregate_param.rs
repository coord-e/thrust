//@check-pass

// Regression test for #125: reborrowing a `&mut` field out of an aggregate
// parameter used to panic with "deref unbound var".

fn bump(r: &mut i64) {
    *r = 1;
}

fn f(w: (&mut i64,)) {
    bump(w.0);
}

fn main() {
    let mut x = 0_i64;
    f((&mut x,));
    assert!(x == 1);
}
