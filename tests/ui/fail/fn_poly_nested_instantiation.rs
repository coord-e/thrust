//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

trait K {
    fn k(&self) -> i32;
}

impl K for i32 {
    fn k(&self) -> i32 {
        1
    }
}

impl K for i64 {
    fn k(&self) -> i32 {
        2
    }
}

fn g<T: K + Copy>(t: T, n: i32) -> i32 {
    let a = t.k();
    let r = if n > 0 { g(0_i64, 0) } else { 0 };
    r + a
}

fn main() {
    assert!(g(0_i32, 1) == 4);
}
