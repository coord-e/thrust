//@check-pass
//@compile-flags: -C debug-assertions=off

trait Idx {
    fn new(idx: usize) -> Self;
    fn index(self) -> usize;
}

impl Idx for u32 {
    fn new(idx: usize) -> u32 {
        idx as u32
    }

    fn index(self) -> usize {
        self as usize
    }
}

fn main() {
    let i = <u32 as Idx>::new(3);
    assert!(i.index() as u128 == 3);
}
