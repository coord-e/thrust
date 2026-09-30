//@check-pass
//@compile-flags: -C overflow-checks=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i32 { unimplemented!() }

fn main() {
    let x = rand();
    if x == -2147483648 {
        assert!(-x == x);
    }
}
