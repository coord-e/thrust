//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::sig(fn(x: int) -> {r: Box<int> | r == <x>})]
fn box_create(x: i64) -> Box<i64> {
    Box::new(x)
}

#[thrust_macros::requires(b == thrust_models::model::Box::new(v))]
fn box_consume(b: Box<i64>, v: i64) {
    assert!(*b == v);
}

fn main() {
    let b = box_create(42);
    box_consume(b, 10);
}
