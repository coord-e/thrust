# Z3 Spacer performance regression — hand-off analysis

**TL;DR.** Thrust's `mut_recursive` pass test times out under recent z3. Root
cause is a performance regression in **z3's Spacer (CHC/PDR) engine, introduced
in z3 4.16.0**. The CHC system Thrust generates for this test is solved in
~0.3 s by every z3 from 4.13.0 through 4.15.2, but z3 4.16.0 fails to solve it
within 180 s (effectively hangs). This is **not** a Thrust bug and **not** a
soundness issue — z3 4.16.0 simply can no longer find an inductive invariant
that older z3 finds instantly.

## Symptom

- Test: `tests/ui/pass/mut_recursive.rs` — a recursive `sum(a: &mut i64, i: i64)`.
- Under z3 ≥ 4.16.0, `thrust-rustc` reports `verification error: Timeout(..)`.
- **CI is unaffected**: `.github/actions/setup-z3` pins z3 **4.13.0**. Only
  developers running a current z3 locally hit it.

## The query

- Small CHC system: **11 predicates, 74 lines, HORN logic**, one datatype
  `mut<Int>` = `(current, final)` — the prophecy-pair encoding of `&mut i64`.
- Proving the program safe = proving the system **`sat`** (an inductive
  invariant exists). The required invariant is simple and linear:
  `final(*a) = initial(*a) + i`.
- Exact solver call Thrust makes (see `src/chc/solver.rs`):
  `z3 fp.spacer.global=true fp.validate=true <file>`

## Reproduction — version matrix

Same query, same args, different z3 release binary:

| z3 version | result | time |
|-----------:|:------:|-----:|
| 4.13.0 (CI pin) | `sat` | 0.3 s |
| 4.13.4 | `sat` | 0.3 s |
| 4.14.0 | `sat` | 0.3 s |
| 4.14.1 | `sat` | 0.3 s |
| 4.15.0 | `sat` | 0.2 s |
| 4.15.2 | `sat` | 0.2 s |
| **4.16.0 (latest)** | **no answer** | **> 180 s (killed)** |

- **Regression window: between 4.15.2 and 4.16.0.**
- Reproduces with the default args, with **no** args, and with
  `fp.spacer.global=false` — i.e. it is the core Spacer engine, not the
  "global guidance" heuristic.
- The **fail-twin** (`tests/ui/fail/mut_recursive.rs`, an `unsat`/refutation) is
  **fast on every version** (~0 s) — only the `sat` / invariant-synthesis path
  regressed.

## What does NOT work (no flag workaround)

17 Spacer option combinations were tried on 4.16.0 — all time out:
`fp.spacer.global` on/off, `fp.validate` on/off, `fp.xform.inline_linear`,
`fp.xform.inline_eager`, `fp.spacer.mbqi`, `fp.spacer.ground_pobs`,
`fp.spacer.use_iuc`, `fp.spacer.q3.use_qgen`, `fp.spacer.p3.share_invariants`+
`share_lemmas`, `fp.spacer.weak_abs`, `fp.spacer.elim_aux`,
`fp.spacer.reset_pob_queue`, `fp.spacer.gpdr`, `fp.spacer.simplify_pob`, and two
random seeds.

## What DOES work

- **z3 ≤ 4.15.2** — solves in ~0.2–0.3 s. (CI already pins 4.13.0.)
- **CoAR / PCSat** (a different CHC solver, via `tests/thrust-pcsat-wrapper`) —
  solves in ~5–19 s. This confirms the system is genuinely satisfiable; the
  invariant exists and is easy to find for a non-Spacer engine.

## Minimal reproducer

`z3_4.16_spacer_regression_repro.smt2` (in this directory) is self-contained —
no Thrust needed. To reproduce:

```sh
# get release binaries from https://github.com/Z3Prover/z3/releases
z3-4.15.2 fp.spacer.global=true fp.validate=true z3_4.16_spacer_regression_repro.smt2   # -> sat, ~0.2s
z3-4.16.0 fp.spacer.global=true fp.validate=true z3_4.16_spacer_regression_repro.smt2   # -> hangs
```

This is a clean candidate to file upstream at
<https://github.com/Z3Prover/z3/issues> (performance regression, `sat` instance,
Spacer).

## Related but SEPARATE finding (not the version regression)

Branch `claude/analyze-terminator-predicate-var-CFFwy` ("Drop pvar of call
destination") inlines the per-call-result predicate. Its CHC is the standard
minimal encoding (7 predicates; it correctly keeps the function pre/post
summary as the recursion cut-point). That encoding times out on **all** z3
versions including 4.13.0 — a *distinct*, encoding-induced Spacer blind spot,
**not** the 4.16.0 regression. PCSat solves it (~10 s), so the encoding is
sound and satisfiable; it is just outside Spacer's reach. That branch's pass
test has been routed through the PCSat wrapper as the fix.

Takeaway tying the two together: Spacer is *fragile* on this prophecy-encoded
`&mut`-recursion invariant. The redundant per-call predicates kept z3 ≤ 4.15.2
fast on the current encoding; 4.16.0 lost even that, and the minimal encoding
loses it on every version. A non-Spacer CHC backend (PCSat) is unaffected.

## Code pointers

- `src/chc/solver.rs` — solver invocation, default args, env vars
  (`THRUST_SOLVER`, `THRUST_SOLVER_ARGS`, `THRUST_SOLVER_TIMEOUT_SECS`).
- `.github/actions/setup-z3/action.yml` — the z3 4.13.0 pin.
- `tests/thrust-pcsat-wrapper` — PCSat path (needs Docker + the COAR image
  `ghcr.io/hiroshi-unno/coar`).
