use std::collections::HashSet;

use crate::chc::{self, hoice::HoiceDatatypeRenamer};

#[derive(Debug, Clone)]
pub struct FormatContext {
    renamer: HoiceDatatypeRenamer,
    datatypes: Vec<chc::Datatype>,
}

// FIXME: this is obviously ineffective and should be replaced
fn term_sorts(clause: &chc::Clause, t: &chc::Term, sorts: &mut HashSet<chc::Sort>) {
    sorts.insert(clause.term_sort(t));
    match t {
        chc::Term::Null => {}
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
        chc::Term::DatatypeCtor(_, _, args) => {
            for arg in args {
                term_sorts(clause, arg, sorts);
            }
        }
        chc::Term::DatatypeDiscr(_, t) => term_sorts(clause, t, sorts),
    }
}

fn atom_sorts(clause: &chc::Clause, a: &chc::Atom, sorts: &mut HashSet<chc::Sort>) {
    for a in &a.args {
        term_sorts(clause, a, sorts);
    }
}

#[derive(Debug, Clone)]
pub(super) struct Sort<'a> {
    inner: &'a chc::Sort,
}

impl<'a> std::fmt::Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Sort::Null => write!(f, "Null"),
            chc::Sort::Int => write!(f, "Int"),
            chc::Sort::Bool => write!(f, "Bool"),
            chc::Sort::String => write!(f, "String"),
            chc::Sort::Param(i) => write!(f, "T{}", i),
            chc::Sort::Box(s) => write!(f, "Box{}", Sort::new(s).sorts()),
            chc::Sort::Mut(s) => write!(f, "Mut{}", Sort::new(s).sorts()),
            chc::Sort::Tuple(ss) => write!(f, "Tuple{}", Sorts::new(ss)),
            chc::Sort::Datatype(s) => write!(f, "{}{}", s.symbol, Sorts::new(&s.args)),
        }
    }
}

impl<'a> Sort<'a> {
    pub fn new(inner: &'a chc::Sort) -> Self {
        Self { inner }
    }

    pub fn sorts(self) -> impl std::fmt::Display {
        format!("<{}>", self)
    }

    pub fn to_symbol(&self) -> chc::DatatypeSymbol {
        chc::DatatypeSymbol::new(self.to_string())
    }
}

#[derive(Debug, Clone)]
struct Sorts<'a> {
    inner: &'a [chc::Sort],
}

impl<'a> std::fmt::Display for Sorts<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inner.is_empty() {
            return Ok(());
        }
        write!(f, "<")?;
        for (i, s) in self.inner.iter().enumerate() {
            if i != 0 {
                write!(f, "-")?;
            }
            write!(f, "{}", Sort::new(s))?;
        }
        write!(f, ">")?;
        Ok(())
    }
}

impl<'a> Sorts<'a> {
    pub fn new(inner: &'a [chc::Sort]) -> Self {
        Self { inner }
    }
}

fn builtin_sort_datatype(s: chc::Sort) -> Option<chc::Datatype> {
    let symbol = Sort::new(&s).to_symbol();
    let d = match s {
        chc::Sort::Null => chc::Datatype {
            symbol,
            ctors: vec![chc::DatatypeCtor {
                symbol: chc::DatatypeSymbol::new("null".to_string()),
                selectors: vec![],
                discriminant: 0,
            }],
        },
        chc::Sort::Box(inner) => {
            let ss = Sort::new(&inner).sorts();
            chc::Datatype {
                symbol,
                ctors: vec![chc::DatatypeCtor {
                    symbol: chc::DatatypeSymbol::new(format!("box{ss}")),
                    selectors: vec![chc::DatatypeSelector {
                        symbol: chc::DatatypeSymbol::new(format!("box_current{ss}")),
                        sort: *inner,
                    }],
                    discriminant: 0,
                }],
            }
        }
        chc::Sort::Mut(inner) => {
            let ss = Sort::new(&inner).sorts();
            chc::Datatype {
                symbol,
                ctors: vec![chc::DatatypeCtor {
                    symbol: chc::DatatypeSymbol::new(format!("mut{ss}")),
                    selectors: vec![
                        chc::DatatypeSelector {
                            symbol: chc::DatatypeSymbol::new(format!("mut_current{ss}")),
                            sort: *inner.clone(),
                        },
                        chc::DatatypeSelector {
                            symbol: chc::DatatypeSymbol::new(format!("mut_final{ss}")),
                            sort: *inner,
                        },
                    ],
                    discriminant: 0,
                }],
            }
        }
        chc::Sort::Tuple(elems) => {
            let ss = Sorts::new(&elems);
            let selectors = elems
                .iter()
                .enumerate()
                .map(|(i, sort)| chc::DatatypeSelector {
                    symbol: chc::DatatypeSymbol::new(format!("tuple_proj{ss}.{i}")),
                    sort: sort.clone(),
                })
                .collect();
            chc::Datatype {
                symbol,
                ctors: vec![chc::DatatypeCtor {
                    symbol: chc::DatatypeSymbol::new(format!("tuple{ss}")),
                    selectors,
                    discriminant: 0,
                }],
            }
        }
        _ => return None,
    };
    Some(d)
}

fn collect_sorts(system: &chc::System) -> HashSet<chc::Sort> {
    let mut sorts = HashSet::new();

    for sig in &system.pred_vars {
        sorts.extend(sig.clone());
    }

    for clause in &system.clauses {
        sorts.extend(clause.vars.clone());
        atom_sorts(clause, &clause.head, &mut sorts);
        for a in &clause.body {
            atom_sorts(clause, a, &mut sorts);
        }
    }

    sorts
}

impl FormatContext {
    pub fn from_system(system: &chc::System) -> Self {
        let sorts = collect_sorts(system);
        let datatypes: Vec<_> = sorts
            .into_iter()
            .flat_map(builtin_sort_datatype)
            .chain(system.datatypes.clone())
            .collect();
        let renamer = HoiceDatatypeRenamer::new(&datatypes);
        FormatContext { renamer, datatypes }
    }

    pub fn datatypes(&self) -> &[chc::Datatype] {
        &self.datatypes
    }

    pub fn box_ctor(&self, sort: &chc::Sort) -> impl std::fmt::Display {
        let ss = Sort::new(sort).sorts();
        format!("box{ss}")
    }

    pub fn box_current(&self, sort: &chc::Sort) -> impl std::fmt::Display {
        let ss = Sort::new(sort).sorts();
        format!("box_current{ss}")
    }

    pub fn mut_ctor(&self, sort: &chc::Sort) -> impl std::fmt::Display {
        let ss = Sort::new(sort).sorts();
        format!("mut{ss}")
    }

    pub fn mut_current(&self, sort: &chc::Sort) -> impl std::fmt::Display {
        let ss = Sort::new(sort).sorts();
        format!("mut_current{ss}")
    }

    pub fn mut_final(&self, sort: &chc::Sort) -> impl std::fmt::Display {
        let ss = Sort::new(sort).sorts();
        format!("mut_final{ss}")
    }

    pub fn tuple_ctor(&self, sorts: &[chc::Sort]) -> impl std::fmt::Display {
        let ss = Sorts::new(sorts);
        format!("tuple{ss}")
    }

    pub fn tuple_proj(&self, sorts: &[chc::Sort], idx: usize) -> impl std::fmt::Display {
        let ss = Sorts::new(sorts);
        format!("tuple_proj{ss}.{idx}")
    }

    pub fn fmt_sort(&self, sort: &chc::Sort) -> impl std::fmt::Display {
        let sym = Sort::new(sort).to_symbol();
        self.fmt_datatype_symbol(&sym)
    }

    pub fn fmt_datatype_symbol(&self, sym: &chc::DatatypeSymbol) -> impl std::fmt::Display {
        self.renamer.rename(sym)
    }
}
