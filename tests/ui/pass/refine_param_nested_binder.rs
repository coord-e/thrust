//@check-pass

pub enum Pair<T> {
    Mk(T, T),
}

impl<T> thrust_models::Model for Pair<T> {
    type Ty = Self;
}

#[thrust_macros::param(p: { q: Pair<{ v: i32 | v > 0 }> | true })]
#[thrust_macros::ret({ r: i32 | r > 0 })]
fn first(p: Pair<i32>) -> i32 {
    match p {
        Pair::Mk(a, _) => a,
    }
}

fn main() {}
