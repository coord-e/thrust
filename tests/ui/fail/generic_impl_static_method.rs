//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

trait K {
    fn k() -> i64;
}

impl K for i32 {
    fn k() -> i64 {
        0
    }
}

impl K for i64 {
    fn k() -> i64 {
        1
    }
}

struct W<T>(T);

impl<T: K> W<T> {
    fn kk() -> i64 {
        T::k()
    }
}

fn main() {
    assert!(W::<i64>::kk() == 0);
}
