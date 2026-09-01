//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
extern crate thrust_macros;
use thrust_macros::{context, requires, ensures, predicate};
use thrust_models::{exists, forall, Model};

#[context]
trait Account {
    #[ensures(Self::is_balance(*self, result))]
    fn balance(&self) -> u32;
    #[requires(exists(|x| Self::is_balance(*self, x)))]
    #[ensures(forall(|x| Self::is_balance(*self, x) ==> Self::is_balance(!self, x + amount)))]
    fn deposit(&mut self, amount: u32);
    #[requires(exists(|x| Self::is_balance(*self, x) && x >= amount))]
    #[ensures(forall(|x| Self::is_balance(*self, x) ==> Self::is_balance(!self, x - amount)))]
    fn withdraw(&mut self, amount: u32);
    #[predicate]
    fn is_balance(self, balance: u32) -> bool;
}

#[requires(exists(|from| A::is_balance(*a, from) && from >= 10))]
#[ensures(forall(|from| A::is_balance(*a, from) ==> exists(|to| A::is_balance(!a, to) && to == from)))]
fn withdraw_deposit<A: Account>(a: &mut A)
where
    A: Model,
    <A as Model>::Ty: Model
{
    a.withdraw(10);
    a.deposit(10);
}

fn main() {}
