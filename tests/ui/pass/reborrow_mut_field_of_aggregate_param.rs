//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// Regression test for #125: reborrowing a `&mut`-typed field out of an
// aggregate (tuple/struct) parameter used to panic with "deref unbound var"
// because the aggregate parameter was bound without flow bindings.

fn bump(r: &mut i64) {
    *r = 1;
}

// tuple parameter
fn f(w: (&mut i64,)) {
    bump(w.0);
}

struct Wrap<'a> {
    r: &'a mut i64,
}

// struct parameter
fn g(w: Wrap) {
    bump(w.r);
}

fn main() {}
