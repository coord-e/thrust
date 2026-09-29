//@error-in-other-file: Unsat
//@compile-flags: -C overflow-checks=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> u32 { unimplemented!() }

fn main() {
    let x = rand();
    if x == 4294967295 {
        assert!(x + 1 != 0);
    }
}
