//@check-pass

// Regression test for #125: reborrowing a `&mut`-typed field out of an
// aggregate (tuple/struct) parameter used to panic with "deref unbound var"
// because the aggregate parameter was bound without flow bindings.

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
