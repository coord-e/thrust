// The strongest lambda+CHC case: a *mutable* walk whose loop invariant must
// track the array through the subsequence prophecy.
//
// The loop zeroes `slice` in place by peeling off the first element with
// `split_first_mut`, writing through it, and rebinding `s` to the mutable tail
// view. `s` is a `&mut` subsequence, so its model is a `Mut` of a lambda-backed
// `Seq`; each iteration's write is propagated back to `slice` through that view's
// prophecy. To discharge `slice[0] == 0` afterwards, a solver must synthesize a
// loop invariant relating the mutated prefix and the pending tail prophecy --
// unavoidably reasoning about the subsequence lambda and its `Mut` resolution,
// not just lengths.
//
// (This program also depends on the enum-drop fix in `refine/env.rs`: the
// `Option<(&mut i32, &mut [i32])>` returned by `split_first_mut` is dropped on
// the loop's exit edge, which previously panicked. See `tests/ui/*/enum_tuple_
// mut_drop.rs`.)
//
// Safe, so a lambda-capable CHC solver should return `sat`; Spacer returns
// `unknown`. Produces `needs_chc_mut_walk.smt2`.
#[thrust::callable]
fn check(slice: &mut [i32]) {
    let mut s = &mut *slice;
    while let Some((first, rest)) = s.split_first_mut() {
        *first = 0;
        s = rest;
    }
    if !slice.is_empty() {
        assert!(slice[0] == 0);
    }
}

fn main() {}
