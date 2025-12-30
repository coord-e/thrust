//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut m: Option<i32> = Some(1);
    if let Some(i) = &mut m {
        *i += 2;
    }
    assert!(matches!(m, Some(3)));
}
