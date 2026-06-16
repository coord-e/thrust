//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool { unimplemented!() }

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
    fn run(&mut self) -> i64 {
        let init = *self;
        while rand() {
            thrust_macros::invariant!(|init: Self, self: &mut Self| init.value <= (*self).value);
            self.value -= 1;
        }
        init.value
    }
}

fn main() {
    let mut c = Counter { value: 3 };
    c.run();
}
