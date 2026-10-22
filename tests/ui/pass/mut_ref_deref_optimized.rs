//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1

fn bump(w: &mut &mut i64) {
    **w += 3;
}

fn main() {
    let mut a = 0;
    let mut r = &mut a;
    bump(&mut r);
    assert!(a == 3);
}
