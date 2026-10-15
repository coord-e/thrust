//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut a = 1_i64;
    let s = Box::new(((&mut a,),));
    let t = s.0;
    *t.0 = 2;
    assert!(a + 100 == 2);
}
