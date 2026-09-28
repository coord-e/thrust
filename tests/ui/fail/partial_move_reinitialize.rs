//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut a = 1_i64;
    let mut s = ((&mut a,),);
    let t = s.0;
    *t.0 = 10;
    s.0 = t;
    assert!(a + 100 == 10);
}
