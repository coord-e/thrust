//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }

#[thrust::requires(true)]
#[thrust::ensures(exists x:int. result == 2 * x)]
fn f() -> i32 {
    let x = rand();
    x + x
}

fn main() {}
