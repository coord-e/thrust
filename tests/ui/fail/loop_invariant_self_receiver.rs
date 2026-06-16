//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Same shape as the pass counterpart (the invariant still refers to the receiver via the explicit
// `self` parameter and `snapshot == *self`), but `steps >= 1` does not hold on entry
// (`steps == 0`), so the invariant is not inductive and verification fails with `Unsat`.

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
                |snapshot: Self, steps: i64, self: &Self| steps >= 1 && snapshot == *self
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
