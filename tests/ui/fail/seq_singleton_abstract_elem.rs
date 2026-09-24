//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::Seq;
use thrust_models::Model;

// The `pass` twin with the index moved past the end of the singleton, where the array holds the
// unobservable padding rather than `x`.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|s: Seq<<T as Model>::Ty>|
    s == Seq::singleton(x) ==> s.len() == 1 && s[1] == x))]
fn singleton_at_abstract_elem<T: Model>(x: <T as Model>::Ty) -> ()
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
    let _ = x;
}

fn main() {}
