#!/usr/bin/env python3
"""Decidable Z3 check of the `split_first_mut` soundness property.

`check_nonrec.py` eliminates the predicate variables and lets plain Z3 discharge
the `split_first_mut` CHC. That works for the *safety* (UNSAT) direction, but Z3
cannot *model-find* through the subsequence `lambda`s, so it returns `unknown`
for the one goal whose job is to exhibit the mutation counterexample -- i.e. to
show the post-mutation path is genuinely reachable and not vacuously closed.

This script closes that gap with a decidable reduction. The programs pin the
slice length to a concrete value, and for a *concrete* length `n` the guarded
subarray lambda

    λk. ite(0 <= k && k < n, select(arr, start + k), default)

is provably equal to a store-chain over a constant-`default` array:

    store(... store(K(default), 0, arr[start]) ..., n-1, arr[start+n-1])

(both map k in [0, n) to arr[start+k] and everything else to `default`). Z3's
array theory decides equalities between such store-chains completely, so we can
verify the exact soundness property the lambda encoding is meant to provide.

The essential slice of the `split_first_mut` CHC, with the predicate variables
already eliminated by hand:

  * `slice` starts as `[10, 20]`            -> cur[0] = 10
  * split off `first` (= cur[0]) and `tail` (= subsequence(1, 2))
  * mutate `*first = 11`                    -> fin[0] = 11
  * drop the unmutated `tail`               -> subseq(fin, 1, 1) == subseq(cur, 1, 1)
  * the program then claims `slice[0] == 12`

The path is safe to reject iff `slice[0] != 12` is satisfiable on this path,
i.e. iff the path is not vacuous.
"""
import z3

I = z3.IntSort()
Arr = z3.ArraySort(I, I)


def subseq(arr, start, n, default=0):
    """Normalized length-`n` sub-view as a store-chain (== the guarded lambda)."""
    a = z3.K(I, z3.IntVal(default))
    for k in range(n):
        a = z3.Store(a, k, z3.Select(arr, start + k))
    return a


def guarded_lambda(arr, start, n, default=0):
    """The exact term Thrust emits, for cross-checking the store-chain equivalence."""
    k = z3.Int("sub!idx")
    return z3.Lambda([k], z3.If(z3.And(0 <= k, k < n), arr[start + k], z3.IntVal(default)))


def check(name, expected, assertions):
    s = z3.Solver()
    s.add(*assertions)
    r = s.check()
    ok = "OK" if str(r) == expected else "!! MISMATCH"
    print(f"  [{ok}] {name}: {r} (expected {expected})")
    return str(r) == expected


def main():
    cur = z3.Const("cur", Arr)   # (*slice).array   -- initial
    fin = z3.Const("fin", Arr)   # (!slice).array   -- prophecy / final
    N = 2                        # slice length, pinned by the program

    tail_cur = subseq(cur, 1, N - 1)   # subsequence(1, 2), length 1
    tail_fin = subseq(fin, 1, N - 1)

    ok = True

    print("store-chain == guarded lambda (the reduction is faithful):")
    # For concrete n the two encodings are the same array; violating equality is UNSAT.
    ok &= check("subseq(cur,1,1) == guarded_lambda(cur,1,1)", "unsat",
                [subseq(cur, 1, 1) != guarded_lambda(cur, 1, 1)])

    print("new guarded model -- the mutation reproduction:")
    mutation_path = [cur[0] == 10, fin[0] == 11, tail_fin == tail_cur]
    # The rejected assertion is `slice[0] == 12`; the path reaches its violation
    # (`slice[0] != 12`) iff the path is satisfiable. slice[0] after the call = fin[0].
    ok &= check("post-mutation path with slice[0] != 12 is reachable", "sat",
                mutation_path + [fin[0] != 12])
    ok &= check("tail resolution leaves the split-off index 0 free", "sat",
                [tail_fin == tail_cur, cur[0] != fin[0]])
    ok &= check("tail resolution still pins the in-range element (index 1)", "unsat",
                [tail_fin == tail_cur, cur[1] != fin[1]])

    print("old offset/whole-array model -- the bug it replaces:")
    # Sharing the backing array resolves the tail as full array equality cur == fin.
    ok &= check("whole-array tail resolution makes the path vacuous", "unsat",
                [cur == fin, cur[0] == 10, fin[0] == 11])

    print()
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
