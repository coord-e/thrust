//! An optimization that removes `Box` sorts and terms from a CHC system.

use super::*;

fn term_sort(term: &Term, vars: &rustc_index::IndexVec<TermVarIdx, Sort>) -> Sort {
    term.sort(|v| vars[*v].clone())
}

fn unbox_term(term: Term, vars: &rustc_index::IndexVec<TermVarIdx, Sort>) -> Term {
    match term {
        Term::Var(_) | Term::Bool(_) | Term::Int(_) | Term::String(_) | Term::Null => term,
        Term::Box(t) => unbox_term(*t, vars),
        Term::Mut(t1, t2) => Term::Mut(
            Box::new(unbox_term(*t1, vars)),
            Box::new(unbox_term(*t2, vars)),
        ),
        Term::BoxCurrent(t) => unbox_term(*t, vars),
        Term::MutCurrent(t) => Term::MutCurrent(Box::new(unbox_term(*t, vars))),
        Term::MutFinal(t) => Term::MutFinal(Box::new(unbox_term(*t, vars))),
        Term::App(fun, args) => {
            Term::App(fun, args.into_iter().map(|t| unbox_term(t, vars)).collect())
        }
        Term::Tuple(ts) => {
            let ts: Vec<_> = ts.into_iter().map(|t| unbox_term(t, vars)).collect();
            if let [t] = &ts[..] {
                t.clone()
            } else {
                Term::Tuple(ts)
            }
        }
        Term::TupleProj(t, i) => {
            let sort = term_sort(&t, vars);
            let term = unbox_term(*t, vars);
            match unbox_sort(sort) {
                Sort::Tuple(sorts) if sorts.len() == 1 => {
                    assert_eq!(i, 0, "invalid 1-tuple projection");
                    term
                }
                Sort::Tuple(_) => Term::TupleProj(Box::new(term), i),
                _ if i == 0 => term,
                _ => Term::TupleProj(Box::new(term), i),
            }
        }
        Term::DatatypeCtor(s1, s2, args) => Term::DatatypeCtor(
            unbox_datatype_sort(s1),
            s2,
            args.into_iter().map(|t| unbox_term(t, vars)).collect(),
        ),
        Term::DatatypeDiscr(sym, arg) => Term::DatatypeDiscr(sym, Box::new(unbox_term(*arg, vars))),
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
        Pred::UserDefined(pred) => Pred::UserDefined(pred),
    }
}

fn unbox_atom(atom: Atom, vars: &rustc_index::IndexVec<TermVarIdx, Sort>) -> Atom {
    let Atom { guard, pred, args } = atom;
    let guard = guard.map(|fo| Box::new(unbox_formula(*fo, vars)));
    let pred = unbox_pred(pred);
    let args = args.into_iter().map(|t| unbox_term(t, vars)).collect();
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
        Sort::Tuple(sorts) => {
            let sorts: Vec<_> = sorts.into_iter().map(unbox_sort).collect();
            if let [sort] = &sorts[..] {
                sort.clone()
            } else {
                Sort::Tuple(sorts)
            }
        }
        Sort::Array(s1, s2) => Sort::Array(Box::new(unbox_sort(*s1)), Box::new(unbox_sort(*s2))),
        Sort::Datatype(sort) => Sort::Datatype(unbox_datatype_sort(sort)),
    }
}

fn unbox_formula(formula: Formula, vars: &rustc_index::IndexVec<TermVarIdx, Sort>) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(unbox_atom(atom, vars)),
        Formula::Not(fo) => Formula::Not(Box::new(unbox_formula(*fo, vars))),
        Formula::And(fs) => Formula::And(fs.into_iter().map(|f| unbox_formula(f, vars)).collect()),
        Formula::Or(fs) => Formula::Or(fs.into_iter().map(|f| unbox_formula(f, vars)).collect()),
        Formula::Exists(exists_vars, fo) => {
            let exists_vars = exists_vars
                .into_iter()
                .map(|(v, s)| (v, unbox_sort(s)))
                .collect();
            Formula::Exists(exists_vars, Box::new(unbox_formula(*fo, vars)))
        }
    }
}

fn unbox_body(body: Body, vars: &rustc_index::IndexVec<TermVarIdx, Sort>) -> Body {
    let Body { atoms, formula } = body;
    let atoms = atoms.into_iter().map(|a| unbox_atom(a, vars)).collect();
    let formula = unbox_formula(formula, vars);
    Body { atoms, formula }
}

fn unbox_clause(clause: Clause) -> Clause {
    let Clause {
        vars,
        head,
        body,
        debug_info,
    } = clause;
    let head = unbox_atom(head, &vars);
    let body = unbox_body(body, &vars);
    let vars = vars.into_iter().map(unbox_sort).collect();
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

fn rewrite_1_tuple_projs(body: &str) -> String {
    fn rewrite_expr(bytes: &[u8], pos: &mut usize) -> String {
        if bytes.get(*pos) == Some(&b'(')
            && bytes
                .get(*pos + 1..)
                .is_some_and(|rest| rest.starts_with(b"tuple_proj"))
        {
            let name_start = *pos + 1;
            let mut name_end = name_start;
            while !matches!(bytes.get(name_end), None | Some(b' ' | b'\n' | b'\t' | b'\r')) {
                name_end += 1;
            }
            let name = std::str::from_utf8(&bytes[name_start..name_end]).unwrap();
            if name.ends_with(".0") && !name.contains('-') {
                *pos = name_end;
                while matches!(bytes.get(*pos), Some(b' ' | b'\n' | b'\t' | b'\r')) {
                    *pos += 1;
                }
                let arg = rewrite_expr(bytes, pos);
                while matches!(bytes.get(*pos), Some(b' ' | b'\n' | b'\t' | b'\r')) {
                    *pos += 1;
                }
                assert_eq!(bytes.get(*pos), Some(&b')'), "malformed tuple projection");
                *pos += 1;
                return arg;
            }
        }

        if bytes.get(*pos) == Some(&b'(') {
            *pos += 1;
            let mut expr = String::from("(");
            while bytes.get(*pos) != Some(&b')') {
                if bytes.get(*pos) == Some(&b'(') {
                    expr.push_str(&rewrite_expr(bytes, pos));
                } else {
                    expr.push(bytes[*pos] as char);
                    *pos += 1;
                }
            }
            *pos += 1;
            expr.push(')');
            expr
        } else {
            let start = *pos;
            while !matches!(
                bytes.get(*pos),
                None | Some(b' ' | b'\n' | b'\t' | b'\r' | b')')
            ) {
                *pos += 1;
            }
            std::str::from_utf8(&bytes[start..*pos]).unwrap().to_string()
        }
    }

    let bytes = body.as_bytes();
    let mut pos = 0;
    let mut rewritten = String::new();
    while pos < bytes.len() {
        if bytes[pos] == b'(' {
            rewritten.push_str(&rewrite_expr(bytes, &mut pos));
        } else {
            rewritten.push(bytes[pos] as char);
            pos += 1;
        }
    }
    rewritten
}

fn unbox_user_defined_pred_def(user_defined_pred_def: UserDefinedPredDef) -> UserDefinedPredDef {
    let UserDefinedPredDef { symbol, sig, body } = user_defined_pred_def;
    let sig = sig
        .into_iter()
        .map(|(name, sort)| (name, unbox_sort(sort)))
        .collect();
    let body = rewrite_1_tuple_projs(&body);
    UserDefinedPredDef { symbol, sig, body }
}

/// Remove all `Box` sorts and `Box`/`BoxCurrent` terms from the system.
///
/// The box values in Thrust represent an owned pointer, but are logically equivalent to the inner type.
/// This pass removes them to reduce the complexity of the CHCs sent to the solver.
/// This function traverses a [`System`] and removes all `Box` related constructs.
pub fn unbox(system: System) -> System {
    let System {
        raw_commands,
        datatypes,
        user_defined_pred_defs,
        clauses,
        pred_vars,
    } = system;
    let datatypes = datatypes.into_iter().map(unbox_datatype).collect();
    let clauses = clauses.into_iter().map(unbox_clause).collect();
    let pred_vars = pred_vars.into_iter().map(unbox_pred_var_def).collect();
    let user_defined_pred_defs = user_defined_pred_defs
        .into_iter()
        .map(unbox_user_defined_pred_def)
        .collect();
    System {
        raw_commands,
        datatypes,
        user_defined_pred_defs,
        clauses,
        pred_vars,
    }
}
