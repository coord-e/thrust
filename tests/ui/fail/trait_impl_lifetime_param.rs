//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result >= 0)]
    fn get(&self) -> i64;
}

struct R<'a> {
    r: &'a i64,
}

impl<'a> thrust_models::Model for R<'a> {
    type Ty = Self;
}

impl<'a> Get for R<'a> {
    fn get(&self) -> i64 {
        if *self.r >= 0 {
            *self.r
        } else {
            -1
        }
    }
}

fn main() {
    let x = 5;
    let r = R { r: &x };
    assert!(r.get() >= 0);
}
