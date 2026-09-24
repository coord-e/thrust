//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

struct C {
    n: usize,
}

impl thrust_models::Model for C {
    type Ty = C;
}

#[thrust_macros::context]
impl C {
    #[thrust_macros::ensures(result == true ==> (*self).n != 0 && (!self).n == (*self).n - 1)]
    #[thrust_macros::ensures(result == false ==> (*self).n == 0 && (!self).n == 0)]
    fn dec(&mut self) -> bool {
        if self.n != 0 {
            self.n -= 1;
            true
        } else {
            true
        }
    }
}

fn main() {
    let mut c = C { n: 1 };
    assert!(c.dec());
    assert!(!c.dec());
}
