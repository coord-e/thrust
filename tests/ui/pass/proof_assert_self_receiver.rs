//@check-pass
//@compile-flags: -C debug-assertions=off

#[derive(PartialEq, Clone, Copy)]
struct Counter {
    value: i64,
}

impl thrust_models::Model for Counter {
    type Ty = Counter;
}

#[thrust_macros::context]
impl Counter {
    #[thrust_macros::invariant_context]
    fn bump(&mut self) -> i64 {
        let init = *self;
        self.value += 1;
        thrust_macros::proof_assert!(|init: Self, self: &mut Self| init.value < (*self).value);
        init.value
    }
}

fn main() {
    let mut c = Counter { value: 3 };
    c.bump();
}
