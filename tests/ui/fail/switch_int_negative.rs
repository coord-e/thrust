//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i32 { unimplemented!() }

fn main() {
    let x = rand();
    match x {
        -1 => assert!(x > 0),
        _ => {}
    }
}
