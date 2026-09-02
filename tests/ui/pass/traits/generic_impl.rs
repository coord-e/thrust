//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
//@check-pass

use thrust_models::Model;

#[thrust_macros::context]
trait Foo {
    type Item;

    #[thrust_macros::predicate]
    fn valid(self, x: Self::Item) -> bool;
}

struct Bar<T>(T);

#[thrust_macros::context]
impl<T> Foo for Bar<T>
where
    T: Foo + Model,
    <T as Foo>::Item: Model,
    <T as Model>::Ty: PartialEq,
{
    type Item = T::Item;

    #[thrust_macros::predicate]
    fn valid(self, x: Self::Item) -> bool {
        "true"; true
    }
}

impl<T> Model for Bar<T> {
    type Ty = Bar<T>;
}

#[thrust_macros::requires(T::valid(x, v))]
#[thrust_macros::ensures(T::valid(result, v))]
fn identity<T>(x: T, v: T::Item) -> T
where
    T: Foo + Model,
    <T as Foo>::Item: Model,
{
    x
}

fn main() {}