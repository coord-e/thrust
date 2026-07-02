# Lambda-backed subsequence CHC fixtures

These are hand-off test cases for developing CHC solver support for **array
`lambda`s**. They are *not* run by `cargo test`: the `ui_test` harness only
scans `tests/ui/`, and the generated constraints cannot be discharged by the
default Spacer (`z3` HORN) solver, which does not support `lambda`.

## Why lambdas?

Thrust models a slice/`Vec` as a `Seq` tuple `(array, length)`. A *subsequence*
view — the tail returned by `split_first`/`split_last` and friends — is built
with `Seq::subsequence(start, end)`. Instead of sharing the backing array and
tracking a separate offset (the approach explored in #163/#164), the subsequence
is modeled as a **fresh, shifted array view**:

```
s.subsequence(start, end)  ==  (λi. s.array[start + i],  end - start)
```

The shifted array is emitted to SMT-LIB as a `lambda`:

```smt2
(lambda ((shift!idx Int)) (select <array> (+ <start> shift!idx)))
```

(see `Term::ArrayShift` in `src/chc.rs` and its emission in
`src/chc/smtlib2.rs`).

## Why this is the sound model

The offset-sharing model is unsound for the *mutable* split. When an unmutated
tail view is dropped, its prophecy is resolved with model equality
`final == current`. Under offset-sharing, the two subsequence triples still carry
the **whole** backing array, so that equality forces
`(!slice).array == (*slice).array` at *every* index — including index 0, which
belongs to the `first` element that was split off. Combined with `first`'s
resolved final value and the slice's initial state, the path constraints become
contradictory and *every* assertion after the split is discharged vacuously
(even `assert!(false)`).

With the lambda model, the tail's `final == current` equates

```smt2
(lambda ((i Int)) (select (!slice).array (+ 1 i)))
  == (lambda ((i Int)) (select (*slice).array (+ 1 i)))
```

which, by array extensionality, only constrains indices `>= 1`. Index 0 stays
free, so mutating `first` is consistent, the path is not vacuous, and false
claims about `slice[0]` are correctly refuted.

## Files

| Rust program                       | Generated CHC                        | Expected result |
| ---------------------------------- | ------------------------------------ | --------------- |
| `split_first_mut.rs`               | `split_first_mut.smt2`               | `sat` (safe)    |
| `split_first_mut_mutation.rs`      | `split_first_mut_mutation.smt2`      | `unsat` (rejected — the false `slice[0] == 12` claim must fail) |

The lambda appears in the clause that encodes the `split_first_mut`
postcondition: the tail's current and final arrays are each a `(lambda ...)`
shifted by 1. Search the `.smt2` for `lambda` to find it.

## Regenerating

```console
$ THRUST_OUTPUT_DIR=<dir> \
    cargo run -- -Adead_code -C debug-assertions=false tests/lambda-chc/<name>.rs
$ cp <dir>/thrust_output.smt2 tests/lambda-chc/<name>.smt2
```

The `.smt2` is written before the solver is invoked, so it is produced even when
no `lambda`-capable solver is installed.
