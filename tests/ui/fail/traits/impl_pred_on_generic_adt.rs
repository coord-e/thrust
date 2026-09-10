//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::Model;

#[thrust_macros::context]
trait Foo {
    #[thrust_macros::predicate]
    fn valid(self, x: i64) -> bool;
}

#[derive(PartialEq)]
struct Bar<T>(T);

impl<T> Model for Bar<T> {
    type Ty = Bar<T>;
}

#[thrust_macros::context]
impl<T> Foo for Bar<T>
where
    T: Foo + Model + PartialEq,
    <T as Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn valid(self, x: i64) -> bool {
        "(> x 0)"; true
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(<Bar<T> as Foo>::valid(result, v))]
fn keep<T>(b: Bar<T>, v: i64) -> Bar<T>
where
    T: Foo + Model + PartialEq,
    <T as Model>::Ty: PartialEq,
{
    b
}

fn main() {}
