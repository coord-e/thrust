//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

trait Tr {
    fn m(&self) -> i64 {
        2
    }
}

struct A;

impl Tr for A {
    #[thrust::callable]
    fn m(&self) -> i64 {
        1
    }
}

fn main() {
    assert!(A.m() == 2);
}
