use std::collections::HashSet;

use crate::chc;

#[derive(Debug, Clone)]
struct List<T> {
    open_char: Option<char>,
    close_char: Option<char>,
    delimiter: char,
    items: Vec<T>,
}

impl<T> std::fmt::Display for List<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.open_char {
            write!(f, "{}", c)?;
        }
        for (i, e) in self.items.iter().enumerate() {
            if i != 0 {
                write!(f, "{}", self.delimiter)?;
            }
            write!(f, "{}", e)?;
        }
        if let Some(c) = self.close_char {
            write!(f, "{}", c)?;
        }
        Ok(())
    }
}

impl<T> List<T> {
    pub fn closed<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open_char: Some('('),
            close_char: Some(')'),
            delimiter: ' ',
            items: inner.into_iter().collect(),
        }
    }

    pub fn open<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open_char: None,
            close_char: None,
            delimiter: ' ',
            items: inner.into_iter().collect(),
        }
    }

    pub fn sorts<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open_char: Some('<'),
            close_char: Some('>'),
            delimiter: '-',
            items: inner.into_iter().collect(),
        }
    }
}

#[derive(Debug, Clone)]
struct Sort<'a> {
    inner: &'a chc::Sort,
}

impl<'a> std::fmt::Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Sort::Int => write!(f, "Int"),
            chc::Sort::Bool => write!(f, "Bool"),
            chc::Sort::String => write!(f, "String"),
            chc::Sort::Box(s) => write!(f, "Box{}", List::sorts(std::iter::once(Sort::new(s)))),
            chc::Sort::Mut(s) => write!(f, "Mut{}", List::sorts(std::iter::once(Sort::new(s)))),
            chc::Sort::Tuple(ss) => write!(f, "Tuple{}", List::sorts(ss.iter().map(Sort::new))),
        }
    }
}

impl<'a> Sort<'a> {
    pub fn new(inner: &'a chc::Sort) -> Self {
        Self { inner }
    }
}

#[derive(Debug, Clone)]
struct Term<'a> {
    // we need clause to select box/mut selector/constructor based on sort
    clause: &'a chc::Clause,
    inner: &'a chc::Term,
}

impl<'a> std::fmt::Display for Term<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Term::Var(v) => write!(f, "{}", v),
            chc::Term::Int(i) => write!(f, "{}", i),
            chc::Term::Bool(b) => write!(f, "{}", b),
            chc::Term::String(s) => write!(f, "\"{}\"", s.escape_default()),
            chc::Term::Box(t) => {
                let s = self.clause.term_sort(t);
                write!(
                    f,
                    "(box{} {})",
                    List::sorts(std::iter::once(Sort::new(&s))),
                    Term::new(self.clause, t)
                )
            }
            chc::Term::Mut(t1, t2) => {
                let s = self.clause.term_sort(t1);
                write!(
                    f,
                    "(mut{} {} {})",
                    List::sorts(std::iter::once(Sort::new(&s))),
                    Term::new(self.clause, t1),
                    Term::new(self.clause, t2)
                )
            }
            chc::Term::BoxCurrent(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "(box_current{} {})",
                    List::sorts(std::iter::once(Sort::new(&s))),
                    Term::new(self.clause, t)
                )
            }
            chc::Term::MutCurrent(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "(mut_current{} {})",
                    List::sorts(std::iter::once(Sort::new(&s))),
                    Term::new(self.clause, t)
                )
            }
            chc::Term::MutFinal(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "(mut_final{} {})",
                    List::sorts(std::iter::once(Sort::new(&s))),
                    Term::new(self.clause, t)
                )
            }
            chc::Term::App(fn_, args) => {
                write!(
                    f,
                    "({} {})",
                    fn_,
                    List::open(args.iter().map(|t| Term::new(self.clause, t)))
                )
            }
            chc::Term::Tuple(ts) => {
                let ss: Vec<_> = ts.iter().map(|t| self.clause.term_sort(t)).collect();
                write!(
                    f,
                    "(tuple{} {})",
                    List::sorts(ss.iter().map(Sort::new)),
                    List::open(ts.iter().map(|t| Term::new(self.clause, t)))
                )
            }
            chc::Term::TupleProj(t, i) => {
                let s = self.clause.term_sort(t);
                write!(
                    f,
                    "(tuple_proj{}.{} {})",
                    List::sorts(s.as_tuple().unwrap().iter().map(Sort::new)),
                    i,
                    Term::new(self.clause, t)
                )
            }
        }
    }
}

impl<'a> Term<'a> {
    pub fn new(clause: &'a chc::Clause, inner: &'a chc::Term) -> Self {
        Self { clause, inner }
    }
}

#[derive(Debug, Clone)]
pub struct Atom<'a> {
    clause: &'a chc::Clause,
    inner: &'a chc::Atom,
}

impl<'a> std::fmt::Display for Atom<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inner.pred.is_negative() {
            write!(f, "(not ")?;
        }
        if self.inner.args.is_empty() {
            write!(f, "{}", self.inner.pred.name())?;
        } else {
            let args = List::open(self.inner.args.iter().map(|t| Term::new(self.clause, t)));
            write!(f, "({} {})", self.inner.pred.name(), args)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'a> Atom<'a> {
    pub fn new(clause: &'a chc::Clause, inner: &'a chc::Atom) -> Self {
        Self { clause, inner }
    }
}

#[derive(Debug, Clone)]
pub struct Clause<'a> {
    inner: &'a chc::Clause,
}

impl<'a> std::fmt::Display for Clause<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let body = List::open(self.inner.body.iter().map(|a| Atom::new(self.inner, a)));
        let head = Atom::new(self.inner, &self.inner.head);
        if self.inner.vars.is_empty() {
            write!(f, "(=> (and {body}) {head})")
        } else {
            let vars = List::closed(
                self.inner
                    .vars
                    .iter_enumerated()
                    .map(|(v, s)| List::closed([v.to_string(), Sort::new(s).to_string()])),
            );
            write!(f, "(forall {vars} (=> (and {body}) {head}))")
        }
    }
}

impl<'a> Clause<'a> {
    pub fn new(inner: &'a chc::Clause) -> Self {
        Self { inner }
    }
}

#[derive(Debug, Clone)]
pub struct System<'a> {
    inner: &'a chc::System,
}

impl<'a> std::fmt::Display for System<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(set-logic HORN)")?;
        let mut sorts: Vec<_> = self.collect_sorts().into_iter().collect();
        sorts.sort_by_key(|s| s.length()); // print small one first
        for s in sorts {
            if let chc::Sort::Box(inner) = &s {
                let inner = Sort::new(inner);
                let ss = List::sorts(std::iter::once(inner.clone()));
                writeln!(
                    f,
                    "(declare-datatypes () ((Box{ss} (box{ss} (box_current{ss} {inner})))))"
                )?;
            }
            if let chc::Sort::Mut(inner) = &s {
                let inner = Sort::new(inner);
                let ss = List::sorts(std::iter::once(inner.clone()));
                writeln!(
                    f,
                    "(declare-datatypes () ((Mut{ss} (mut{ss} (mut_current{ss} {inner}) (mut_final{ss} {inner})))))",
                )?;
            }
            if let chc::Sort::Tuple(elems) = &s {
                let ss = List::sorts(elems.iter().map(Sort::new));
                let projs = elems
                    .iter()
                    .map(Sort::new)
                    .enumerate()
                    .map(|(i, s)| format!("(tuple_proj{ss}.{i} {s})"))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(
                    f,
                    "(declare-datatypes () ((Tuple{ss} (tuple{ss} {projs}))))",
                )?;
            }
        }
        for (p, sorts) in self.inner.pred_vars.iter_enumerated() {
            writeln!(
                f,
                "(declare-fun {} {} Bool)",
                p,
                List::closed(sorts.iter().map(Sort::new))
            )?;
        }
        for clause in &self.inner.clauses {
            writeln!(f, "(assert {})", Clause::new(clause))?;
        }
        Ok(())
    }
}

// FIXME: this is obviously ineffective and should be replaced
fn term_sorts(clause: &chc::Clause, t: &chc::Term, sorts: &mut HashSet<chc::Sort>) {
    sorts.insert(clause.term_sort(t));
    match t {
        chc::Term::Var(_) => {}
        chc::Term::Bool(_) => {}
        chc::Term::Int(_) => {}
        chc::Term::String(_) => {}
        chc::Term::Box(t) => term_sorts(clause, t, sorts),
        chc::Term::Mut(t1, t2) => {
            term_sorts(clause, t1, sorts);
            term_sorts(clause, t2, sorts);
        }
        chc::Term::BoxCurrent(t) => term_sorts(clause, t, sorts),
        chc::Term::MutCurrent(t) => term_sorts(clause, t, sorts),
        chc::Term::MutFinal(t) => term_sorts(clause, t, sorts),
        chc::Term::App(_fun, args) => {
            for arg in args {
                term_sorts(clause, arg, sorts);
            }
        }
        chc::Term::Tuple(ts) => {
            for t in ts {
                term_sorts(clause, t, sorts);
            }
        }
        chc::Term::TupleProj(t, _) => term_sorts(clause, t, sorts),
    }
}

fn atom_sorts(clause: &chc::Clause, a: &chc::Atom, sorts: &mut HashSet<chc::Sort>) {
    for a in &a.args {
        term_sorts(clause, a, sorts);
    }
}

impl<'a> System<'a> {
    pub fn new(inner: &'a chc::System) -> Self {
        Self { inner }
    }

    fn collect_sorts(&self) -> HashSet<chc::Sort> {
        let mut sorts = HashSet::new();

        for sig in &self.inner.pred_vars {
            sorts.extend(sig.clone());
        }

        for clause in &self.inner.clauses {
            sorts.extend(clause.vars.clone());
            atom_sorts(clause, &clause.head, &mut sorts);
            for a in &clause.body {
                atom_sorts(clause, a, &mut sorts);
            }
        }

        sorts
    }
}
