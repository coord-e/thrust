//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

use thrust_models::model::BitVec;

struct BitSet64 {
    bits: u64,
}

impl thrust_models::Model for BitSet64 {
    type Ty = BitVec<64, false>;
}

#[thrust_macros::context]
impl BitSet64 {
    #[thrust::trusted]
    #[thrust_macros::ensures(result == BitVec::from_int(0))]
    fn new() -> Self {
        BitSet64 { bits: 0 }
    }

    #[thrust::trusted]
    #[thrust_macros::requires(i < 64)]
    #[thrust_macros::ensures(!self == *self | (BitVec::from_int(1) << BitVec::from_int(i)))]
    fn insert(&mut self, i: usize) {
        self.bits |= 1 << i;
    }

    #[thrust::trusted]
    #[thrust_macros::requires(i < 64)]
    #[thrust_macros::ensures(
        result == ((*self >> BitVec::from_int(i)) & BitVec::from_int(1) == BitVec::from_int(1))
    )]
    fn contains(&self, i: usize) -> bool {
        self.bits & (1 << i) != 0
    }
}

fn main() {
    let mut set = BitSet64::new();
    set.insert(3);
    set.insert(5);
    assert!(set.contains(3));
    assert!(set.contains(4));
}
