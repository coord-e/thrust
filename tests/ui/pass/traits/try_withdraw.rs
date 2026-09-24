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

#[requires(exists(|from| A::is_balance(*a, from)))]
#[ensures(forall(|from| A::is_balance(*a, from) ==> exists(|to| A::is_balance(!a, to) && to + result == from)))]
fn try_withdraw<A: Account>(a: &mut A, amount: u32) -> u32
where
    A: Model,
    <A as Model>::Ty: Model
{
    if a.balance() < amount {
        return 0;
    }
    a.withdraw(amount);
    return amount;
}

fn main() {}
