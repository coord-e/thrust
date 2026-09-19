//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::ensures(result == 0)]
fn count_down(mut n: u32) -> u32 {
    while n > 0 {
        n -= 1;
    }
    n
}

fn main() {}
