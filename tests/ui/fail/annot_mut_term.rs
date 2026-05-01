//@error-in-other-file: Unsat

use thrust_models::model::Mut;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(x == Mut::new(*x, y))]
fn f(x: &mut i64, y: i64) {
    *x = y;
}

fn main() {
    let mut a = 1;
    f(&mut a, 2);
    assert!(a == 1);
}
