//@error-in-other-file: Unsat

pub enum Pair<T> {
    Mk(T, T),
}

impl<T> thrust_models::Model for Pair<T> {
    type Ty = Self;
}

#[thrust_macros::sig(fn(p: Pair<{ v: i32 | v > 0 }>) -> { r: i32 | r > 100 })]
fn second(p: Pair<i32>) -> i32 {
    match p {
        Pair::Mk(_, b) => b,
    }
}

fn main() {}
