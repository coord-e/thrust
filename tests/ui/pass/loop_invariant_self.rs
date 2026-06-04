//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

struct Counter(i64);
impl thrust_models::Model for Counter {
    type Ty = (thrust_models::model::Int,);
}

#[thrust_macros::context]
impl Counter {
    #[thrust_macros::invariant_context]
    fn run(self) {
        let mut c = self;
        let mut x = 1_i64;
        while rand() == 0 {
            thrust_macros::invariant!(|x: i64, c: Self| x >= 1 && c == c);
            x = x + 1;
            c = Counter(0);
        }
        let _last = c;
        assert!(x >= 1);
    }
}

fn main() { Counter(0).run(); }
