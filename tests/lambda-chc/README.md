# Lambda-backed subsequence CHC fixtures

Hand-off test cases for developing CHC solver support for **array `lambda`s**.
They are *not* run by `cargo test`: the `ui_test` harness only scans `tests/ui/`,
and these constraints cannot be discharged by the default Spacer (`z3` HORN)
solver, which does not support `lambda`.

## Why lambdas?

Thrust models a slice/`Vec` as a `Seq` tuple `(array, length)`. A *subsequence*
view — the tail returned by `split_first`/`split_last` and friends — is built
with `Seq::subsequence(start, end)`. Instead of sharing the backing array and
tracking a separate offset (the approach explored in #163/#164), the subsequence
is modeled as a **fresh, normalized sub-array view** (`Term::Subarray`), emitted
as an SMT-LIB `lambda`:

```smt2
(lambda ((k Int))
  (ite (and (<= 0 k) (< k <length>))
       (select <array> (+ <start> k))
       <default>))
```

Logical index `k` reads the backing array at `start + k` while `k` is in range,
and is pinned to the element sort's canonical `default` otherwise. See
`Term::Subarray` in `src/chc.rs` and its emission in `src/chc/smtlib2.rs`. Reads
of a subsequence are beta-reduced back to `select(array, start + k)` by a `select`
peephole (slice indexing always carries an `index < length` precondition), so the
lambda survives only where a view is compared as a whole array — which is exactly
where its semantics matter.

## Why the range guard is required for soundness

The offset-sharing model is unsound for the *mutable* split. When an unmutated
tail view is dropped, its prophecy is resolved with `final == current`. Under
offset-sharing the two subsequence triples still carry the **whole** backing
array, so that equality forces `(!slice).array == (*slice).array` at *every*
index — including index 0, which belongs to the `first` element that was split
off. Combined with `first`'s resolved final value and the slice's initial state,
the path becomes contradictory and *every* assertion after the split is
discharged vacuously (even `assert!(false)`).

A naive lambda fix — an *unguarded* shift `λk. select(arr, start + k)` — does
**not** help: array indices range over all of ℤ, so the shift is a bijection and
equating two shifted views is still equivalent to full array equality (take
`k = -1` to reach index 0). The **range guard** is what makes the difference:
pinning out-of-range positions to a shared `default` makes full array equality of
two normalized views coincide with element-wise equality over `[0, length)` only.
Resolving a tail view (`start = 1`) then constrains indices `>= 1` and leaves the
split-off index 0 free, so mutating `first` stays consistent and false claims
about `slice[0]` are correctly refuted.

## Files

### Non-recursive `split_first_mut` (does not really need CHC)

| Rust program                  | Generated CHC                  | Expected |
| ----------------------------- | ------------------------------ | -------- |
| `split_first_mut.rs`          | `split_first_mut.smt2`         | `sat` (safe)   |
| `split_first_mut_mutation.rs` | `split_first_mut_mutation.smt2`| `unsat` (rejected — the false `slice[0] == 12` claim must fail) |

These programs are straight-line: their CHC predicates are just acyclic state
relations, so no invariant synthesis is needed and they can be validated with
plain Z3 after eliminating the predicate variables (see below).

### Programs that genuinely need CHC — with a *load-bearing* lambda

| Rust program                   | Generated CHC                   | Needs |
| ------------------------------ | ------------------------------- | ----- |
| `needs_chc_recursive_nth.rs`   | `needs_chc_recursive_nth.smt2`  | a **recursive summary that indexes the array**: `nth(s, n) == s.array[n]` |
| `needs_chc_loop_index.rs`      | `needs_chc_loop_index.smt2`     | a **loop invariant that is a lambda**: `s == slice.subsequence(i, len)` |

Both are safe, so a lambda-capable CHC solver should return `sat`; Spacer returns
`unknown`.

The point of these two (versus a naive `mylen(s) == s.len()` / `count == len`
counter) is that the synthesized invariant/summary must constrain the **array**
(the lambda), not just the `length` field:

- `recursive_nth`: proving `nth(s, 1) == s[1]` needs the summary `nth(s, n) ==
  s.array[n]`. Closing the recursion requires the solver to show
  `select(subsequence(s,1,len).array, n-1) == select(s.array, n)` — i.e. to
  `select` through the guarded subsequence lambda. A length-only summary is
  useless here.
- `loop_index`: proving the in-loop `*first == slice[i]` needs the invariant
  `s == slice.subsequence(i, len)`, whose array component is a guarded
  subsequence lambda whose *shift is the loop counter* `i`. The invariant itself
  contains a lambda.

Note: the most direct way to make a lambda load-bearing is a *mutable*
subsequence walk (a loop/recursion over `split_first_mut`), where the invariant
must track the array through the tail prophecy. Thrust does not support that yet
(it panics in `refine/env.rs` on the prophecy existentials), so these two use
immutable reads whose summary/invariant nonetheless has to talk about the array.

## Validation

Requires `z3` on `PATH` and the `z3` Python module (`pip install z3-solver`).

### `check_nonrec.py` — predicate elimination + plain Z3

```console
$ python3 check_nonrec.py split_first_mut.smt2
$ python3 check_nonrec.py split_first_mut_mutation.smt2
```

Unfolds the acyclic predicates into every goal (`… => false`) clause and checks
the residual lambda/array formula. `all goals unsat` ⇒ safe; `some goal sat` ⇒
rejected. This validates `split_first_mut.smt2` as **safe** outright. For
`split_first_mut_mutation.smt2` it proves the other goals `unsat` but returns
`unknown` on the counterexample goal: Z3 cannot *model-find* through the guarded
lambda (this is the very gap the fixtures target). That goal is covered by:

### `soundness_check.py` — decidable store-chain distillation

```console
$ python3 soundness_check.py
```

For a *concrete* length `n`, the guarded subarray lambda is provably equal to a
store-chain over a constant-`default` array (the script checks this equivalence,
then relies on it). Z3's array theory decides store-chain equalities completely,
so this verifies the exact soundness property with **no `unknown`s**: the
post-mutation path is satisfiable (non-vacuous, so the bad `slice[0] == 12` claim
is genuinely rejected), the tail resolution leaves index 0 free but still pins the
in-range elements, and the old whole-array model makes the same path vacuous.

## Regenerating the `.smt2`

```console
$ THRUST_OUTPUT_DIR=<dir> \
    cargo run -- -Adead_code -C debug-assertions=off tests/lambda-chc/<name>.rs
$ cp <dir>/thrust_output.smt2 tests/lambda-chc/<name>.smt2
```

The `.smt2` is written before the solver is invoked, so it is produced even when
no `lambda`-capable solver is installed.
