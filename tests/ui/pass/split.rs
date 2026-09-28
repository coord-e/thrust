//@check-pass

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(-1000 <= result && result <= 1000)]
fn rand() -> i32 { unimplemented!() }

fn split<'a>((a, b): &'a mut (i32, i32)) -> (&'a mut i32, &'a mut i32) {
    (a, b)
}

fn main() {
    let a = rand();
    let b = rand();
    let mut p = (a, b);
    let (ma, mb) = split(&mut p);
    *ma += 1;
    assert!(p.0 == a + 1);
}
