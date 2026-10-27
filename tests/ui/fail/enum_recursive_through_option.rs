//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

enum Chain {
    Link(i64, Option<Box<Chain>>),
}

impl thrust_models::Model for Chain {
    type Ty = Self;
}

fn sum(c: &Chain) -> i64 {
    match c {
        Chain::Link(v, None) => *v,
        Chain::Link(v, Some(next)) => *v + sum(next),
    }
}

fn main() {
    let c = Chain::Link(1, Some(Box::new(Chain::Link(2, None))));
    assert!(sum(&c) == 4);
}
