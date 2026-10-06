//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn wrap(a: &mut i64) -> ((&mut i64,),) {
    ((a,),)
}

fn main() {
    let mut a = 1_i64;
    let mut i = 0_i64;
    let mut s: ((&mut i64,),);
    while i < 2 {
        thrust_macros::invariant!(|i: i64| i >= 0 && i <= 2);
        s = wrap(&mut a);
        let t = s.0;
        *t.0 = 10;
        i += 1;
    }
    assert!(i == 3);
}
