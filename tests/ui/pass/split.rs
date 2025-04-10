//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
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
