//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::Seq;
use thrust_models::Model;

// A `Seq` literal whose element sort is a type parameter. The empty array it is built from needs
// a padding value of that abstract sort, and the query has to name one without asking the solver
// to invent it. The padding is unobservable below the length, which the `fail` twin pins.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|s: Seq<<T as Model>::Ty>|
    s == Seq::singleton(x) ==> s.len() == 1 && s[0] == x))]
fn singleton_at_abstract_elem<T: Model>(x: <T as Model>::Ty) -> ()
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
    let _ = x;
}

fn main() {}
