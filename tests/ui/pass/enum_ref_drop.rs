//@check-pass

pub enum X<'a, 'b> {
    A(&'a mut i64),
    B(&'b mut i64),
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn rand() -> i64 { unimplemented!() }

fn x(i: &mut i64) -> X {
    if *i >= 0 {
        X::A(i)
    } else {
        X::B(i)
    }
}

fn main() {
    let mut i = rand();
    if i64::MIN < i && i < i64::MAX {
        match x(&mut i) {
            X::A(a) => *a += 1,
            X::B(b) => *b = -*b,
        }
        assert!(i > 0);
    }
}
