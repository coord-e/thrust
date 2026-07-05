//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::requires(
    opt == None || thrust_models::exists(|i| opt == Some(i) && thrust_macros::pre!(f(i)))
)]
#[thrust_macros::ensures(
    (opt == None && result == None)
    || thrust_models::exists(|i| thrust_models::exists(|j|
        opt == Some(i) && thrust_macros::post!(f(i), j) && result == Some(j)))
)]
fn map<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    T: thrust_models::Model, T::Ty: PartialEq,
    U: thrust_models::Model, U::Ty: PartialEq,
    F: FnOnce(T) -> U,
{
    match opt {
        Some(i) => Some(f(i)),
        None => None,
    }
}

fn main() {}
