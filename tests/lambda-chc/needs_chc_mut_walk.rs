// The strongest lambda+CHC case: a *mutable* walk whose loop invariant must
// track the array through the subsequence prophecy.
//
// `slice()` yields a length-2 slice `[10, 20]`. The loop zeroes it in place by
// peeling off the first element with `split_first_mut`, writing through it, and
// rebinding `s` to the mutable tail view. `s` is a `&mut` subsequence, so its
// model is a `Mut` of a lambda-backed `Seq`; each write is propagated back to
// `sl` through that view's prophecy. To discharge `sl[0] == 0` afterwards, a
// solver must synthesize a loop invariant relating the mutated prefix and the
// pending tail prophecy -- unavoidably reasoning about the subsequence lambda
// and its `Mut` resolution, not just lengths.
//
// A concrete-length producer is used so `sl` is known non-empty and `sl[0]` is
// in bounds; the property is a guard-free, non-vacuous goal. (Walking the
// reborrow `s` to empty leaves `sl` itself at its original length -- the
// prophecy chain preserves it -- so no `is_empty` guard is needed.)
//
// This program also depends on the enum-drop fix in `refine/env.rs`: the
// `Option<(&mut i32, &mut [i32])>` returned by `split_first_mut` is dropped on
// the loop's exit edge, which previously panicked. See
// `tests/ui/{pass,fail}/enum_tuple_mut_drop.rs`.
//
// Safe, so a lambda-capable CHC solver should return `sat`; Spacer returns
// `unknown`. Produces `needs_chc_mut_walk.smt2`.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 2
        && (*result).array[0] == 10
        && (*result).array[1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

#[thrust::callable]
fn check() {
    let sl = slice();
    let mut s = &mut *sl;
    while let Some((first, rest)) = s.split_first_mut() {
        *first = 0;
        s = rest;
    }
    assert!(sl[0] == 0);
}

fn main() {}
