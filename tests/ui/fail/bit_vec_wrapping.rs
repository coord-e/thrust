//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

use thrust_models::model::BitVec;

#[derive(Clone, Copy)]
struct WrappingI32(i32);

impl thrust_models::Model for WrappingI32 {
    type Ty = BitVec<32, true>;
}

#[thrust::trusted]
#[thrust_macros::ensures(result.to_int() == x)]
fn wrap(x: i32) -> WrappingI32 {
    WrappingI32(x)
}

#[thrust::trusted]
#[thrust_macros::ensures(result == x + y)]
fn add(x: WrappingI32, y: WrappingI32) -> WrappingI32 {
    WrappingI32(x.0.wrapping_add(y.0))
}

#[thrust::trusted]
#[thrust_macros::ensures(result == (x < y))]
fn lt(x: WrappingI32, y: WrappingI32) -> bool {
    x.0 < y.0
}

fn main() {
    let max = wrap(i32::MAX);
    let one = wrap(1);
    let sum = add(max, one);
    assert!(!lt(sum, max));
}
