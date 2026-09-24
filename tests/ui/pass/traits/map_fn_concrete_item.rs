//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

struct Map<I, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<I, F>;
}

// `Map`'s own struct-level type arguments are `<I, F>` -- fixing the closure's
// output to a concrete `i64` (rather than an impl-only `B: Model` that never
// appears in `Map<I, F>`'s own type arguments) removes the type parameter that
// panicked when a call site tried to resolve it.
#[thrust_macros::context]
impl<I: Iterator<Item = i64> + thrust_models::Model, F: Fn(i64) -> i64> Iterator for Map<I, F>
where
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some((self.func)(v))
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|i: i64| pre!(self.func(i)))
        "(and
            (q_invariant_4d8c188fb84596fee9a2d9c5fc98ae25<a0> (tuple_proj<a0-a1>.0 self_))
            (forall ((i Int))
                (q_pre_next_4d8c188fb84596fecd3dcc87543efe66<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (q_completed_4d8c188fb84596fe73c306e4bc6f95ef<a0>
                (mut<a0>
                    (tuple_proj<a0-a1>.0 (mut_current<Tuple<a0-a1>> self_))
                    (tuple_proj<a0-a1>.0 (mut_final<Tuple<a0-a1>> self_))
                )
            )
            (=
                (tuple_proj<a0-a1>.1 (mut_current<Tuple<a0-a1>> self_))
                (tuple_proj<a0-a1>.1 (mut_final<Tuple<a0-a1>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)) &&
        // pre!(self.func(i)) && post!(self.func(i), item) && self.func == dist.func
        "(exists ((i Int))
            (and
                (q_step_4d8c188fb84596fe3fcc020be02ea8ac<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    i
                    (tuple_proj<a0-a1>.0 dist)
                )
                (q_pre_next_4d8c188fb84596fecd3dcc87543efe66<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                )
                (q_post_next_4d8c188fb84596fecd3dcc87543efe66<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                    item
                )
                (=
                    (tuple_proj<a0-a1>.1 self_)
                    (tuple_proj<a0-a1>.1 dist)
                )
            )
        )";
        true
    }
}

fn main() {}
