//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;

struct Fz {
    iter: Option<i64>,
}

impl thrust_models::Model for Fz {
    type Ty = Fz;
}

#[thrust_macros::context]
impl Fz {
    #[thrust_macros::ensures((*self).iter == None ==> (!self).iter == None)]
    #[thrust_macros::ensures(forall(|v| (*self).iter == Some(v) ==> (!self).iter == Some(v + 1)))]
    fn inc(&mut self) {
        match &mut self.iter {
            None => {}
            Some(x) => {
                *x += 1;
            }
        }
    }
}

fn main() {}
