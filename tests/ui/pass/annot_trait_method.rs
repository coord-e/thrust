//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

trait Scalable {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn scale(x: i32) -> i32;
}

fn main() {}
