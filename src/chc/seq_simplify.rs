//! Rewrites `select(seq_concat_arr(...), i)` and `select(seq_subseq_arr(...), i)`
//! to a one-step unfolding of their `define-fun-rec` bodies, expressed as `ite`.
//!
//! Without this, pcsat has to find an inductive invariant to prove indexed
//! properties of unbounded concat / subsequence; with it, the unfolded `ite`
//! form discharges them directly.

use super::*;

fn rewrite_select(arr: Term, index: Term) -> Term {
    match arr {
        Term::SeqConcatArr(_, mut args) => {
            assert_eq!(args.len(), 4, "SeqConcatArr takes 4 args");
            let _tn = args.pop().unwrap();
            let ta = args.pop().unwrap();
            let sn = args.pop().unwrap();
            let sa = args.pop().unwrap();
            let cond = index.clone().lt(sn.clone());
            let then_ = simplify_term(sa.select(index.clone()));
            let else_ = simplify_term(ta.select(index.sub(sn)));
            Term::ite(cond, then_, else_)
        }
        Term::SeqSubseqArr(elem, mut args) => {
            assert_eq!(args.len(), 3, "SeqSubseqArr takes 3 args");
            let r = args.pop().unwrap();
            let l = args.pop().unwrap();
            let a = args.pop().unwrap();
            let len = r.sub(l.clone());
            let in_range = index.clone().ge(Term::int(0)).and(index.clone().lt(len));
            let then_ = simplify_term(a.select(l.add(index)));
            let else_ = Term::default_for(&elem);
            Term::ite(in_range, then_, else_)
        }
        arr => arr.select(index),
    }
}

fn simplify_term(term: Term) -> Term {
    match term {
        Term::Null
        | Term::Var(_)
        | Term::Bool(_)
        | Term::Int(_)
        | Term::String(_)
        | Term::EmptyArray(_)
        | Term::FormulaQuantifiedVar(_, _) => term,
        Term::Box(t) => Term::Box(Box::new(simplify_term(*t))),
        Term::Mut(t1, t2) => Term::Mut(Box::new(simplify_term(*t1)), Box::new(simplify_term(*t2))),
        Term::BoxCurrent(t) => Term::BoxCurrent(Box::new(simplify_term(*t))),
        Term::MutCurrent(t) => Term::MutCurrent(Box::new(simplify_term(*t))),
        Term::MutFinal(t) => Term::MutFinal(Box::new(simplify_term(*t))),
        Term::App(Function::SELECT, mut args) if args.len() == 2 => {
            let index = simplify_term(args.pop().unwrap());
            let arr = simplify_term(args.pop().unwrap());
            rewrite_select(arr, index)
        }
        Term::App(fun, args) => Term::App(fun, args.into_iter().map(simplify_term).collect()),
        Term::SeqConcatArr(s, args) => {
            Term::SeqConcatArr(s, args.into_iter().map(simplify_term).collect())
        }
        Term::SeqSubseqArr(s, args) => {
            Term::SeqSubseqArr(s, args.into_iter().map(simplify_term).collect())
        }
        Term::Tuple(ts) => Term::Tuple(ts.into_iter().map(simplify_term).collect()),
        Term::TupleProj(t, i) => Term::TupleProj(Box::new(simplify_term(*t)), i),
        Term::DatatypeCtor(s1, s2, args) => {
            Term::DatatypeCtor(s1, s2, args.into_iter().map(simplify_term).collect())
        }
        Term::DatatypeDiscr(sym, arg) => Term::DatatypeDiscr(sym, Box::new(simplify_term(*arg))),
    }
}

fn simplify_atom(atom: Atom) -> Atom {
    let Atom { guard, pred, args } = atom;
    let guard = guard.map(|fo| Box::new(simplify_formula(*fo)));
    let args = args.into_iter().map(simplify_term).collect();
    Atom { guard, pred, args }
}

fn simplify_formula(formula: Formula) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(simplify_atom(atom)),
        Formula::Not(fo) => Formula::Not(Box::new(simplify_formula(*fo))),
        Formula::And(fs) => Formula::And(fs.into_iter().map(simplify_formula).collect()),
        Formula::Or(fs) => Formula::Or(fs.into_iter().map(simplify_formula).collect()),
        Formula::Implies(lhs, rhs) => Formula::Implies(
            Box::new(simplify_formula(*lhs)),
            Box::new(simplify_formula(*rhs)),
        ),
        Formula::Exists(vars, fo) => Formula::Exists(vars, Box::new(simplify_formula(*fo))),
        Formula::Forall(vars, fo) => Formula::Forall(vars, Box::new(simplify_formula(*fo))),
    }
}

fn simplify_body(body: Body) -> Body {
    let Body { atoms, formula } = body;
    let atoms = atoms.into_iter().map(simplify_atom).collect();
    let formula = simplify_formula(formula);
    Body { atoms, formula }
}

fn simplify_clause(clause: Clause) -> Clause {
    let Clause {
        vars,
        head,
        body,
        debug_info,
    } = clause;
    let head = simplify_atom(head);
    let body = simplify_body(body);
    Clause {
        vars,
        head,
        body,
        debug_info,
    }
}

pub fn seq_simplify(system: System) -> System {
    let System {
        raw_commands,
        datatypes,
        user_defined_pred_defs,
        clauses,
        pred_vars,
        uses_seq_concat,
        uses_seq_subseq,
    } = system;
    let clauses = clauses.into_iter().map(simplify_clause).collect();
    System {
        raw_commands,
        datatypes,
        user_defined_pred_defs,
        clauses,
        pred_vars,
        uses_seq_concat,
        uses_seq_subseq,
    }
}
