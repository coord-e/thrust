//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

trait Countable {
    #[thrust_macros::predicate]
    fn is_positive(self) -> bool;
}

fn main() {}
