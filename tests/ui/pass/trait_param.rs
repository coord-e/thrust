//@check-pass
//@compile-flags: -C debug-assertions=off

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

fn falsy<T: BoolLike>(value: T) -> bool {
    !value.truthy()
}

fn main() {
    assert!(falsy(0_i32));
}
