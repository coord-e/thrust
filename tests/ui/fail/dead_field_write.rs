//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::callable]
fn retarget(c: bool) {
    let mut a = 1_i64;
    let mut b = 2_i64;
    let mut s = (&mut a, 0_i64);
    *s.0 = 5;
    if c {
        s.0 = &mut b;
    }
    assert!(a == 5 && b == 3);
}

fn main() {}
