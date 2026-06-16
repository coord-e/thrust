//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A loop invariant refers to the receiver by listing it explicitly as a `self` parameter. It is
// renamed to a `self_` parameter and bound to the receiver's entry value. Here `snapshot` is taken
// before the loop and the invariant asserts it stays equal to the (immutable) receiver.

#[derive(PartialEq, Clone, Copy)]
struct Counter {
    limit: i64,
}

impl thrust_models::Model for Counter {
    type Ty = Counter;
}

#[thrust_macros::context]
impl Counter {
    #[thrust_macros::invariant_context]
    fn scan(&self) -> i64 {
        let snapshot = *self;
        let mut steps = 0;
        while snapshot == *self && steps < 10 {
            thrust_macros::invariant!(
                |snapshot: Self, steps: i64, self: &Self| steps >= 0 && snapshot == *self
            );
            steps += 1;
        }
        steps
    }
}

fn main() {
    let c = Counter { limit: 3 };
    let _ = c.scan();
}
