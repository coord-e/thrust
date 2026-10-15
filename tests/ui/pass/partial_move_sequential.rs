//@check-pass
//@compile-flags: -C debug-assertions=off

fn check(take: bool) {
    let mut a0 = 0_i64;
    let s0 = ((&mut a0,),);
    if take {
        let t = s0.0;
        *t.0 = 1;
    }
    assert!(a0 == if take { 1 } else { 0 });
    let mut a1 = 0_i64;
    let s1 = ((&mut a1,),);
    if take {
        let t = s1.0;
        *t.0 = 1;
    }
    assert!(a1 == if take { 1 } else { 0 });
    let mut a2 = 0_i64;
    let s2 = ((&mut a2,),);
    if take {
        let t = s2.0;
        *t.0 = 1;
    }
    assert!(a2 == if take { 1 } else { 0 });
    let mut a3 = 0_i64;
    let s3 = ((&mut a3,),);
    if take {
        let t = s3.0;
        *t.0 = 1;
    }
    assert!(a3 == if take { 1 } else { 0 });
    let mut a4 = 0_i64;
    let s4 = ((&mut a4,),);
    if take {
        let t = s4.0;
        *t.0 = 1;
    }
    assert!(a4 == if take { 1 } else { 0 });
    let mut a5 = 0_i64;
    let s5 = ((&mut a5,),);
    if take {
        let t = s5.0;
        *t.0 = 1;
    }
    assert!(a5 == if take { 1 } else { 0 });
    let mut a6 = 0_i64;
    let s6 = ((&mut a6,),);
    if take {
        let t = s6.0;
        *t.0 = 1;
    }
    assert!(a6 == if take { 1 } else { 0 });
    let mut a7 = 0_i64;
    let s7 = ((&mut a7,),);
    if take {
        let t = s7.0;
        *t.0 = 1;
    }
    assert!(a7 == if take { 1 } else { 0 });
}
fn main() {
    check(true);
}
