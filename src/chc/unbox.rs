//! An optimization that removes `Box` sorts and terms from a CHC system.

use super::*;

fn unbox_term(term: Term) -> Term {
    match term {
        Term::Var(_) | Term::Bool(_) | Term::Int(_) | Term::String(_) | Term::Null => term,
        Term::Box(t) => unbox_term(*t),
        Term::Mut(t1, t2) => Term::Mut(Box::new(unbox_term(*t1)), Box::new(unbox_term(*t2))),
        Term::BoxCurrent(t) => unbox_term(*t),
        Term::MutCurrent(t) => Term::MutCurrent(Box::new(unbox_term(*t))),
        Term::MutFinal(t) => Term::MutFinal(Box::new(unbox_term(*t))),
        Term::App(fun, args) => Term::App(fun, args.into_iter().map(unbox_term).collect()),
        Term::Tuple(ts) => Term::Tuple(ts.into_iter().map(unbox_term).collect()),
        Term::TupleProj(t, i) => Term::TupleProj(Box::new(unbox_term(*t)), i),
        Term::DatatypeCtor(s1, s2, args) => Term::DatatypeCtor(
            unbox_datatype_sort(s1),
            s2,
            args.into_iter().map(unbox_term).collect(),
        ),
        Term::DatatypeDiscr(sym, arg) => Term::DatatypeDiscr(sym, Box::new(unbox_term(*arg))),
        Term::FormulaExistentialVar(sort, name) => {
            Term::FormulaExistentialVar(unbox_sort(sort), name)
        }
    }
}

fn unbox_matcher_pred(pred: MatcherPred) -> Pred {
    let MatcherPred {
        datatype_symbol,
        datatype_args,
    } = pred;
    let datatype_args = datatype_args.into_iter().map(unbox_sort).collect();
    Pred::Matcher(MatcherPred {
        datatype_symbol,
        datatype_args,
    })
}

fn unbox_pred(pred: Pred) -> Pred {
    match pred {
        Pred::Known(pred) => Pred::Known(pred),
        Pred::Var(pred) => Pred::Var(pred),
        Pred::Matcher(pred) => unbox_matcher_pred(pred),
    }
}

fn unbox_atom(atom: Atom) -> Atom {
    let Atom { guard, pred, args } = atom;
    let guard = guard.map(|fo| Box::new(unbox_formula(*fo)));
    let pred = unbox_pred(pred);
    let args = args.into_iter().map(unbox_term).collect();
    Atom { guard, pred, args }
}

fn unbox_datatype_sort(sort: DatatypeSort) -> DatatypeSort {
    let DatatypeSort { symbol, args } = sort;
    let args = args.into_iter().map(unbox_sort).collect();
    DatatypeSort { symbol, args }
}

fn unbox_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Null => Sort::Null,
        Sort::Int => Sort::Int,
        Sort::Bool => Sort::Bool,
        Sort::String => Sort::String,
        Sort::Param(i) => Sort::Param(i),
        Sort::Box(inner) => unbox_sort(*inner),
        Sort::Mut(inner) => Sort::Mut(Box::new(unbox_sort(*inner))),
        Sort::Tuple(sorts) => Sort::Tuple(sorts.into_iter().map(unbox_sort).collect()),
        Sort::Datatype(sort) => Sort::Datatype(unbox_datatype_sort(sort)),
    }
}

fn unbox_formula(formula: Formula) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(unbox_atom(atom)),
        Formula::Not(fo) => Formula::Not(Box::new(unbox_formula(*fo))),
        Formula::And(fs) => Formula::And(fs.into_iter().map(unbox_formula).collect()),
        Formula::Or(fs) => Formula::Or(fs.into_iter().map(unbox_formula).collect()),
        Formula::Exists(vars, fo) => {
            let vars = vars.into_iter().map(|(v, s)| (v, unbox_sort(s))).collect();
            Formula::Exists(vars, Box::new(unbox_formula(*fo)))
        }
    }
}

fn unbox_body(body: Body) -> Body {
    let Body { atoms, formula } = body;
    let atoms = atoms.into_iter().map(unbox_atom).collect();
    let formula = unbox_formula(formula);
    Body { atoms, formula }
}

fn unbox_clause(clause: Clause) -> Clause {
    let Clause {
        vars,
        head,
        body,
        debug_info,
    } = clause;
    let vars = vars.into_iter().map(unbox_sort).collect();
    let head = unbox_atom(head);
    let body = unbox_body(body);
    Clause {
        vars,
        head,
        body,
        debug_info,
    }
}

fn unbox_pred_var_def(pred_var_def: PredVarDef) -> PredVarDef {
    let PredVarDef { sig, debug_info } = pred_var_def;
    let sig = sig.into_iter().map(unbox_sort).collect();
    PredVarDef { sig, debug_info }
}

fn unbox_datatype_selector(selector: DatatypeSelector) -> DatatypeSelector {
    let DatatypeSelector { symbol, sort } = selector;
    let sort = unbox_sort(sort);
    DatatypeSelector { symbol, sort }
}

fn unbox_datatype_ctor(ctor: DatatypeCtor) -> DatatypeCtor {
    let DatatypeCtor {
        symbol,
        selectors,
        discriminant,
    } = ctor;
    let selectors = selectors.into_iter().map(unbox_datatype_selector).collect();
    DatatypeCtor {
        symbol,
        selectors,
        discriminant,
    }
}

fn unbox_datatype(datatype: Datatype) -> Datatype {
    let Datatype {
        symbol,
        params,
        ctors,
    } = datatype;
    let ctors = ctors.into_iter().map(unbox_datatype_ctor).collect();
    Datatype {
        symbol,
        params,
        ctors,
    }
}

/// Remove all `Box` sorts and `Box`/`BoxCurrent` terms from the system.
///
/// The box values in Thrust represent an owned pointer, but are logically equivalent to the inner type.
/// This pass removes them to reduce the complexity of the CHCs sent to the solver.
/// This function traverses a [`System`] and removes all `Box` related constructs.
pub fn unbox(system: System) -> System {
    let System {
        clauses,
        pred_vars,
        datatypes,
    } = system;
    let datatypes = datatypes.into_iter().map(unbox_datatype).collect();
    let clauses = clauses.into_iter().map(unbox_clause).collect();
    let pred_vars = pred_vars.into_iter().map(unbox_pred_var_def).collect();
    System {
        clauses,
        pred_vars,
        datatypes,
    }
}
