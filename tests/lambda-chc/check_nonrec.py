#!/usr/bin/env python3
"""Validate a *non-recursive* Thrust CHC system with plain Z3.

The `split_first_mut` programs have no loops or recursion, so their CHC
predicates are just straight-line state relations forming an acyclic DAG. Such a
system needs no invariant synthesis: its least model is reached by finite
forward unfolding. This script eliminates the predicate variables by unfolding
them into every goal (`... => false`) clause and checks the residual formula --
which still contains the subsequence `lambda`s -- with Z3's array theory.

CHC semantics: the program is SAFE (Thrust `sat`) iff every goal clause body is
UNSAT in the least model, i.e. no execution reaches a violated assertion.

    all goals UNSAT  ->  SAFE (verified)
    some goal SAT    ->  UNSAFE (rejected; the SAT assignment is a counterexample)

Usage: python3 check_nonrec.py <file.smt2>
"""
import re
import sys
import z3

_counter = [0]


def fresh(prefix, sort):
    _counter[0] += 1
    return z3.Const(f"{prefix}!{_counter[0]}", sort)


def is_pred(decl_name):
    return re.fullmatch(r"p\d+", decl_name) is not None


def load(path):
    """Return (definitions, goals).

    definitions: pred_name -> list of (head_arg_exprs, body_expr) with the
                 clause's universally-bound vars already replaced by fresh consts.
    goals:       list of body_expr for `... => false` clauses (fresh-instantiated).
    """
    text = open(path).read()
    # Drop (check-sat); parse_smt2_string wants only decls/definitions/asserts.
    text = text.replace("(check-sat)", "")
    asserts = z3.parse_smt2_string(text)

    defs, goals = {}, []
    for a in asserts:
        if z3.is_quantifier(a):
            assert a.is_forall()
            n = a.num_vars()
            consts = [fresh("q", a.var_sort(i)) for i in range(n)]
            # De Bruijn: var 0 is the *last* bound variable.
            body = z3.substitute_vars(a.body(), *reversed(consts))
        else:
            body = a
        assert z3.is_app(body) and body.decl().kind() == z3.Z3_OP_IMPLIES, body
        hyp, head = body.arg(0), body.arg(1)
        if z3.is_false(head):
            goals.append(hyp)
        else:
            assert is_pred(head.decl().name()), head
            defs.setdefault(head.decl().name(), []).append(
                ([head.arg(i) for i in range(head.num_args())], hyp)
            )
    return defs, goals


def expand(expr, defs):
    """Replace every predicate atom in `expr` by its unfolded definition."""
    if not z3.is_app(expr):
        return expr
    name = expr.decl().name()
    if is_pred(name):
        actual = [expr.arg(i) for i in range(expr.num_args())]
        branches = []
        for head_args, body in defs.get(name, []):
            # Fresh-rename this clause instance so repeated uses don't alias.
            reals = collect_consts(body) | {c for a in head_args for c in collect_consts(a)}
            sub = [(c, fresh("u", c.sort())) for c in reals]
            h2 = [z3.substitute(a, sub) for a in head_args]
            b2 = z3.substitute(body, sub)
            eqs = [act == h for act, h in zip(actual, h2)]
            branches.append(z3.And(*eqs, expand(b2, defs)))
        return z3.Or(*branches) if branches else z3.BoolVal(False)
    # Structural node: rebuild with expanded children.
    children = [expand(expr.arg(i), defs) for i in range(expr.num_args())]
    return expr.decl()(*children) if children else expr


def collect_consts(expr, acc=None):
    if acc is None:
        acc = set()
    if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        acc.add(expr)
    for i in range(expr.num_args() if z3.is_app(expr) else 0):
        collect_consts(expr.arg(i), acc)
    return acc


def main(path):
    defs, goals = load(path)
    print(f"{path}: {sum(len(v) for v in defs.values())} defining clauses, "
          f"{len(goals)} goal clause(s)")
    any_reachable = False
    any_unknown = False
    for i, g in enumerate(goals):
        s = z3.Solver()
        s.add(expand(g, defs))
        r = s.check()
        note = ""
        if r == z3.sat:
            note = "  <-- reachable violation (counterexample)"
        elif r == z3.unknown:
            note = "  <-- Z3 could not decide (lambda model-finding; see soundness_check.py)"
        print(f"  goal {i}: {r}{note}")
        any_reachable |= (r == z3.sat)
        any_unknown |= (r == z3.unknown)
    if any_reachable:
        verdict = "UNSAFE -> Thrust reports Unsat (rejected)"
    elif any_unknown:
        verdict = "INDETERMINATE -> some goal undecided by plain Z3; run soundness_check.py"
    else:
        verdict = "SAFE -> Thrust reports sat (verified)"
    print(f"  => {verdict}")


if __name__ == "__main__":
    main(sys.argv[1])
