//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

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

// A variation on Creusot's `MapExt`, not `MapExt` itself -- the difference is
// in the second paragraph. The closure receives the ghost history of items
// produced so far (`Ghost<Seq<Item>>`), so its precondition can depend on what
// has come before instead of being stated unconditionally over the whole item
// type (contrast `map_fn_uncond_pre.rs`). The history lives in a ghost `produced`
// field updated by `next` itself -- no existential witness array in `step`.
//
// The precondition here is conditioned on the history alone, not on what the
// inner iterator can still actually produce (Creusot's `next_precondition`,
// which quantifies over `self.iter.produces(...)`): that reachability-
// conditioned form was tried first and is NOT inductive on its own (see the
// commit report) -- Creusot pairs it with a `preservation` law justified by
// `produces_trans`, untried here. What DOES verify is `preservation` stated as
// a fact about the closure alone, quantified over an arbitrary history: for
// ANY history, if the closure accepted one more item, its precondition still
// holds for ANY next item at the extended history. That is enough to make the
// per-position "precondition holds for the current history" conjunct
// inductive, without needing `produces`/`produces_refl`/`produces_trans` at
// all -- at the cost of requiring the precondition to hold for every possible
// next item, not just producible ones.
struct Map<I, F> {
    iter: I,
    func: F,
    produced: Ghost<Seq<Int>>,
}

impl<I, F> Model for Map<I, F> {
    type Ty = Map<I, F>;
}

// Obstacle: a `Ghost`-typed FIELD has no model-level accessor in a `ghost!`
// body. `Map`'s model is the struct itself, so `s.produced` stays
// `Ghost<Seq<Int>>` there and `push` is not found (E0599); reaching it through
// a `&mut Map` the way `fold_fn_ghost_call_law.rs` reaches `Run`'s tuple model
// is not available. A `Ghost<T>` PARAMETER is modelled as `T`, so the push has
// to happen in a function that takes one. Binding the field to a local first
// does not help either -- the ghost term then reports the item as not live.
//
// This is NOT the `Self`-in-a-generic-trait-impl gap that forall-sort c0cfee5
// fixed; `ghost_in_generic_impl.rs` shows `ghost!` working directly in such an
// impl now. Only the field access keeps this workaround.
#[thrust_macros::ensures(result == produced.push(x))]
fn push_produced(produced: Ghost<Seq<Int>>, x: i64) -> Ghost<Seq<Int>> {
    thrust_macros::ghost!(|produced: Ghost<Seq<Int>>, x: i64| -> Seq<Int> { produced.push(x) })
}

#[thrust_macros::context]
impl<I: Iterator<Item = i64> + Model, F: Fn(i64, Ghost<Seq<Int>>) -> i64> Iterator for Map<I, F>
where
    <I as Model>::Ty: PartialEq,
{
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                let r = (self.func)(v, self.produced);
                self.produced = push_produced(self.produced, v);
                Some(r)
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|e: i64| pre!(self.func(e, self.produced))) &&
        // preservation(self.func): forall(|harr, hlen, e1: i64, e2: i64, b: i64|
        //     pre!(self.func(e1, (harr,hlen))) && post!(self.func(e1, (harr,hlen)), b)
        //     ==> pre!(self.func(e2, (harr,hlen).push(e1))))
        //
        // Obstacle found and worked around here: quantifying with `forall` over
        // a variable of the packed `Seq`-model TUPLE sort
        // (`Tuple<Array<Int-Int>-Int>`) crashes COAR's SMT-LIB2 parser
        // (`Failure "<name> is already bound"`, independent of the chosen bound
        // name -- confirmed with several). Workaround: quantify over the
        // tuple's own FIELDS (an `Array Int Int` and an `Int` length) and
        // reconstruct the tuple inline via the `tuple<...>` constructor.
        // Break: drop the `self.iter.invariant()` conjunct -- `next`'s own
        // `requires(Self::invariant(*self))` no longer implies the inner
        // iterator's precondition, so `self.iter.next()` cannot be called.
        "(and
            true
            (forall ((e Int))
                (q_pre_next_bedbd733d3f248d989e85efaa8d1bc7<a1>
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                    e
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 self_)
                )
            )
            (forall ((harr (Array Int Int)) (hlen Int))
                (forall ((e1 Int))
                    (forall ((e2 Int))
                        (forall ((b Int))
                            (=>
                                (and
                                    (q_pre_next_bedbd733d3f248d989e85efaa8d1bc7<a1>
                                        (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                                        e1
                                        (tuple<Array<Int-Int>-Int> harr hlen)
                                    )
                                    (q_post_next_bedbd733d3f248d989e85efaa8d1bc7<a1>
                                        (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                                        e1
                                        (tuple<Array<Int-Int>-Int> harr hlen)
                                        b
                                    )
                                )
                                (q_pre_next_bedbd733d3f248d989e85efaa8d1bc7<a1>
                                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                                    e2
                                    (tuple<Array<Int-Int>-Int> (store harr hlen e1) (+ hlen 1))
                                )
                            )
                        )
                    )
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func && *self.produced == !self.produced
        "(and
            (q_completed_bedbd733d3f248d6f3ca13bf4a6f7f6<a0>
                (mut<a0>
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.0 (mut_current<Tuple<a0-a1-Tuple<Array<Int-Int>-Int>>> self_))
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.0 (mut_final<Tuple<a0-a1-Tuple<Array<Int-Int>-Int>>> self_))
                )
            )
            (=
                (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 (mut_current<Tuple<a0-a1-Tuple<Array<Int-Int>-Int>>> self_))
                (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 (mut_final<Tuple<a0-a1-Tuple<Array<Int-Int>-Int>>> self_))
            )
            (=
                (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 (mut_current<Tuple<a0-a1-Tuple<Array<Int-Int>-Int>>> self_))
                (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 (mut_final<Tuple<a0-a1-Tuple<Array<Int-Int>-Int>>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)) &&
        // pre!(self.func(i, self.produced)) && post!(self.func(i, self.produced), item) &&
        // self.func == dist.func && dist.produced == self.produced.push(i)
        "(exists ((i Int))
            (and
                (q_step_bedbd733d3f248d84d555206bfaa09e<a0>
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.0 self_)
                    i
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.0 dist)
                )
                (q_pre_next_bedbd733d3f248d989e85efaa8d1bc7<a1>
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                    i
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 self_)
                )
                (q_post_next_bedbd733d3f248d989e85efaa8d1bc7<a1>
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                    i
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 self_)
                    item
                )
                (=
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 self_)
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.1 dist)
                )
                (=
                    (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 dist)
                    (tuple<Array<Int-Int>-Int>
                        (store
                            (tuple_proj<Array<Int-Int>-Int>.0 (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 self_))
                            (tuple_proj<Array<Int-Int>-Int>.1 (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 self_))
                            i
                        )
                        (+ (tuple_proj<Array<Int-Int>-Int>.1 (tuple_proj<a0-a1-Tuple<Array<Int-Int>-Int>>.2 self_)) 1)
                    )
                )
            )
        )";
        true
    }
}

fn main() {}
