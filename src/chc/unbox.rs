use super::*;

fn unbox_term(term: Term) -> Term {
    match term {
        Term::Var(_) | Term::Bool(_) | Term::Int(_) | Term::String(_) => term,
        Term::Box(t) => unbox_term(*t),
        Term::Mut(t1, t2) => Term::Mut(Box::new(unbox_term(*t1)), Box::new(unbox_term(*t2))),
        Term::BoxCurrent(t) => unbox_term(*t),
        Term::MutCurrent(t) => Term::MutCurrent(Box::new(unbox_term(*t))),
        Term::MutFinal(t) => Term::MutFinal(Box::new(unbox_term(*t))),
        Term::App(fun, args) => Term::App(fun, args.into_iter().map(unbox_term).collect()),
        Term::Tuple(ts) => Term::Tuple(ts.into_iter().map(unbox_term).collect()),
        Term::TupleProj(t, i) => Term::TupleProj(Box::new(unbox_term(*t)), i),
    }
}

fn unbox_atom(atom: Atom) -> Atom {
    let Atom { pred, args } = atom;
    let args = args.into_iter().map(unbox_term).collect();
    Atom { pred, args }
}

fn unbox_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Null => Sort::Null,
        Sort::Int => Sort::Int,
        Sort::Bool => Sort::Bool,
        Sort::String => Sort::String,
        Sort::Box(inner) => unbox_sort(*inner),
        Sort::Mut(inner) => Sort::Mut(Box::new(unbox_sort(*inner))),
        Sort::Tuple(sorts) => Sort::Tuple(sorts.into_iter().map(unbox_sort).collect()),
    }
}

fn unbox_clause(clause: Clause) -> Clause {
    let Clause { vars, head, body } = clause;
    let vars = vars.into_iter().map(unbox_sort).collect();
    let head = unbox_atom(head);
    let body = body.into_iter().map(unbox_atom).collect();
    Clause { vars, head, body }
}

fn unbox_pred_sig(pred_sig: PredSig) -> PredSig {
    pred_sig.into_iter().map(unbox_sort).collect()
}

pub fn unbox(system: System) -> System {
    let System { clauses, pred_vars } = system;
    let clauses = clauses.into_iter().map(unbox_clause).collect();
    let pred_vars = pred_vars.into_iter().map(unbox_pred_sig).collect();
    System { clauses, pred_vars }
}
