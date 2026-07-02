//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool { unimplemented!() }

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand_u32() -> u32 { unimplemented!() }

fn carry_positive(mut x: u32) -> u32 {
    while rand() {
        thrust_macros::invariant!(|x: u32| x >= 1);
        x = x + 1;
    }
    x
}

fn main() {
    let _ = carry_positive(rand_u32());
}
