//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 {
    unimplemented!()
}

#[thrust_macros::context]
trait Gauge {
    #[thrust_macros::predicate]
    fn invariant(x: i32) -> bool;

    fn update(&mut self) -> i32;

    #[thrust_macros::invariant_context]
    fn run(&mut self) -> i32 {
        let mut state = 0;
        while rand() == 0 {
            state = self.update();
            thrust_macros::invariant!(|state: i32| Self::invariant(state));
        }
        state
    }
}

#[derive(PartialEq)]
struct Counter {
    value: i32,
}

impl thrust_models::Model for Counter {
    type Ty = Counter;
}

#[thrust_macros::context]
impl Gauge for Counter {
    #[thrust_macros::predicate]
    fn invariant(x: i32) -> bool {
        "(>= x 0)"; true
    }

    fn update(&mut self) -> i32 {
        if self.value < 0 {
            self.value *= -1;
        } else {
            self.value -= 1;
        }
        self.value
    }
}

fn main() {
    let mut c = Counter { value: 0 };
    assert!(c.run() >= 0);
}
