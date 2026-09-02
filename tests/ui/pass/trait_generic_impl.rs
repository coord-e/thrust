//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result > 0)]
    fn m(&self) -> i32;
}

struct W<T>(T);

impl<T> thrust_models::Model for W<T>
where
    T: thrust_models::Model,
{
    type Ty = Self;
}

impl<T> Tr for W<T> {
    fn m(&self) -> i32 {
        1
    }
}

fn main() {
    let w = W(0i32);
    assert!(w.m() > 0);
}
