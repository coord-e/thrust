//@error-in-other-file: Unsat

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 5)]
fn five() -> i64 {
    4
}

fn main() {
    assert!(five() == 5);
}
