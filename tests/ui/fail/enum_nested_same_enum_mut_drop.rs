//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut slot: Option<i64> = None;
    let o: Option<&mut Option<i64>> = Some(&mut slot);
    if let Some(s) = o {
        *s = Some(3);
    }
    match slot {
        Some(y) => assert!(y == 4),
        None => assert!(false),
    }
}
