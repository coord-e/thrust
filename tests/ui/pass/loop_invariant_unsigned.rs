//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool { unimplemented!() }

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand_u32() -> u32 { unimplemented!() }

fn carry_nonnegative(mut x: u32) -> u32 {
    while rand() {
        thrust_macros::invariant!(|x: u32| x >= 0);
        x = rand_u32();
    }
    x
}

fn main() {
    let _ = carry_nonnegative(rand_u32());
}
