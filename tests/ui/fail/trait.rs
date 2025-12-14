//@error-in-other-file: Unsat

trait BoolLike {
    fn truthy(&self) -> bool;
}

impl BoolLike for bool {
    fn truthy(&self) -> bool {
        *self
    }
}

impl BoolLike for i32 {
    fn truthy(&self) -> bool {
        *self != 0
    }
}

fn main() {
    assert!(1_i32.truthy());
    assert!(false.truthy());
}
