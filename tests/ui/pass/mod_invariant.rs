//@check-pass
//@compile-flags: -C debug-assertions=off

mod counter {
    pub fn count_to(n: i64) -> i64 {
        let mut i = 0_i64;
        while i < n {
            thrust_macros::invariant!(|i: i64| i >= 0);
            i += 1;
        }
        i
    }
}

fn main() {
    assert!(counter::count_to(3) >= 0);
}
