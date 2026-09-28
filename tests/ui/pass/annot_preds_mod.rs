//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

mod spec {
    #[thrust_macros::predicate]
    pub fn positive(x: i64) -> bool {
        x > 0
    }
}

#[thrust_macros::requires(spec::positive(x))]
#[thrust_macros::ensures(result > 0)]
fn id(x: i64) -> i64 {
    x
}

fn main() {
    assert!(id(1) > 0);
}
