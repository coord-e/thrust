//! Wrappers around CHC structures to display them in SMT-LIB2 format.
//!
//! The main entry point is the [`System`] wrapper, which takes a [`chc::System`] and provides a
//! [`std::fmt::Display`] implementation that produces a complete SMT-LIB2.
//! It uses [`FormatContext`] to handle the complexities of the conversion,
//! such as naming convention and solver-specific workarounds.
//! The output of this module is what gets passed to the external CHC solver.

use crate::chc::{
    self,
    format_context::{FormatContext, SortSymbol},
};

fn seq_concat_arr_name(elem: &chc::Sort) -> chc::DatatypeSymbol {
    chc::DatatypeSymbol::new(format!("seq_concat_arr_{}", SortSymbol::new(elem)))
}

fn seq_subseq_arr_name(elem: &chc::Sort) -> chc::DatatypeSymbol {
    chc::DatatypeSymbol::new(format!("seq_subseq_arr_{}", SortSymbol::new(elem)))
}

fn empty_arr_name(elem: &chc::Sort) -> chc::DatatypeSymbol {
    chc::DatatypeSymbol::new(format!("empty_arr_{}", SortSymbol::new(elem)))
}

fn collect_term_uses(term: &chc::Term, empty: &mut std::collections::BTreeSet<chc::Sort>) {
    match term {
        chc::Term::Null
        | chc::Term::Var(_)
        | chc::Term::Bool(_)
        | chc::Term::Int(_)
        | chc::Term::String(_)
        | chc::Term::FormulaQuantifiedVar(_, _) => {}
        chc::Term::EmptyArray(s) => {
            empty.insert(s.clone());
        }
        chc::Term::Box(t)
        | chc::Term::BoxCurrent(t)
        | chc::Term::MutCurrent(t)
        | chc::Term::MutFinal(t)
        | chc::Term::TupleProj(t, _)
        | chc::Term::DatatypeDiscr(_, t) => collect_term_uses(t, empty),
        chc::Term::Mut(t1, t2) => {
            collect_term_uses(t1, empty);
            collect_term_uses(t2, empty);
        }
        chc::Term::App(_, args)
        | chc::Term::Tuple(args)
        | chc::Term::SeqConcatArr(_, args)
        | chc::Term::SeqSubseqArr(_, args)
        | chc::Term::DatatypeCtor(_, _, args) => {
            for arg in args {
                collect_term_uses(arg, empty);
            }
        }
    }
}

/// Walks the system and collects element sorts of every [`chc::Term::EmptyArray`]
/// reachable from any clause's atoms or guards. We also include the value sort of
/// every `seq_subseq_arr`, since its `define-fun-rec` base case references an
/// empty array of that sort.
fn collect_empty_array_value_sorts(system: &chc::System) -> std::collections::BTreeSet<chc::Sort> {
    let mut empty = std::collections::BTreeSet::new();
    let mut visit = |atom: &chc::Atom| {
        if let Some(guard) = &atom.guard {
            for a in guard.iter_atoms() {
                for arg in &a.args {
                    collect_term_uses(arg, &mut empty);
                }
            }
        }
        for arg in &atom.args {
            collect_term_uses(arg, &mut empty);
        }
    };
    for clause in &system.clauses {
        visit(&clause.head);
        for atom in clause.body.iter_atoms() {
            visit(atom);
        }
    }
    for elem in &system.uses_seq_subseq {
        empty.insert(elem.clone());
    }
    empty
}

/// Display wrapper that emits [`fmt_default`] for the given sort.
struct DefaultValue<'a> {
    ctx: &'a FormatContext,
    sort: &'a chc::Sort,
}

impl<'a> DefaultValue<'a> {
    fn new(ctx: &'a FormatContext, sort: &'a chc::Sort) -> Self {
        Self { ctx, sort }
    }
}

impl<'a> std::fmt::Display for DefaultValue<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt_default(self.sort, self.ctx, f)
    }
}

/// Emits a canonical SMT value of `sort`. The exact value is unspecified;
/// only used where any well-typed value would do (e.g. the element of an
/// [`chc::Term::EmptyArray`] or the base case of `seq_subseq_arr`).
fn fmt_default(
    sort: &chc::Sort,
    ctx: &FormatContext,
    f: &mut std::fmt::Formatter,
) -> std::fmt::Result {
    match sort {
        chc::Sort::Null => write!(f, "null"),
        chc::Sort::Int => write!(f, "0"),
        chc::Sort::Bool => write!(f, "false"),
        chc::Sort::String => write!(f, "\"\""),
        chc::Sort::Box(s) => {
            write!(f, "({} ", ctx.box_ctor(s))?;
            fmt_default(s, ctx, f)?;
            write!(f, ")")
        }
        chc::Sort::Mut(s) => {
            write!(f, "({} ", ctx.mut_ctor(s))?;
            fmt_default(s, ctx, f)?;
            write!(f, " ")?;
            fmt_default(s, ctx, f)?;
            write!(f, ")")
        }
        chc::Sort::Tuple(ts) => {
            if ts.is_empty() {
                write!(f, "{}", ctx.tuple_ctor(ts))
            } else {
                write!(f, "({}", ctx.tuple_ctor(ts))?;
                for s in ts {
                    write!(f, " ")?;
                    fmt_default(s, ctx, f)?;
                }
                write!(f, ")")
            }
        }
        chc::Sort::Array(_, v) => {
            write!(f, "((as const (Array Int {})) ", ctx.fmt_sort(v))?;
            fmt_default(v, ctx, f)?;
            write!(f, ")")
        }
        // TODO: defaults for Datatype and Param.
        chc::Sort::Datatype(_) | chc::Sort::Param(_) => {
            unimplemented!("no default value for sort {sort:?}")
        }
    }
}

/// A helper struct to display a list of items.
#[derive(Debug, Clone)]
struct List<T> {
    open: Option<&'static str>,
    close: Option<&'static str>,
    delimiter: &'static str,
    items: Vec<T>,
}

impl<T> std::fmt::Display for List<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.open {
            write!(f, "{}", c)?;
        }
        for (i, e) in self.items.iter().enumerate() {
            if i != 0 {
                write!(f, "{}", self.delimiter)?;
            }
            write!(f, "{}", e)?;
        }
        if let Some(c) = self.close {
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
            open: Some("("),
            close: Some(")"),
            delimiter: " ",
            items: inner.into_iter().collect(),
        }
    }

    pub fn multiline_closed<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: Some("(\n"),
            close: Some("\n)"),
            delimiter: "\n",
            items: inner.into_iter().collect(),
        }
    }

    pub fn multiline_open<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: None,
            close: None,
            delimiter: "\n",
            items: inner.into_iter().collect(),
        }
    }

    pub fn open<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: None,
            close: None,
            delimiter: " ",
            items: inner.into_iter().collect(),
        }
    }
}

/// A wrapper around a [`chc::Term`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
struct Term<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    // we need clause to select box/mut selector/constructor based on sort
    clause: &'a chc::Clause,
    inner: &'a chc::Term,
}

impl<'ctx, 'a> std::fmt::Display for Term<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Term::Null => write!(f, "null"),
            chc::Term::Var(v) => write!(f, "{}", v),
            chc::Term::Int(i) => write!(f, "{}", i),
            chc::Term::Bool(b) => write!(f, "{}", b),
            chc::Term::String(s) => write!(f, "\"{}\"", s.escape_default()),
            chc::Term::Box(t) => {
                let s = self.clause.term_sort(t);
                write!(
                    f,
                    "({} {})",
                    self.ctx.box_ctor(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::Mut(t1, t2) => {
                let s = self.clause.term_sort(t1);
                write!(
                    f,
                    "({} {} {})",
                    self.ctx.mut_ctor(&s),
                    Term::new(self.ctx, self.clause, t1),
                    Term::new(self.ctx, self.clause, t2)
                )
            }
            chc::Term::BoxCurrent(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.box_current(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::MutCurrent(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.mut_current(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::MutFinal(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.mut_final(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::App(fn_, args) => {
                write!(
                    f,
                    "({} {})",
                    fn_,
                    List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                )
            }
            chc::Term::EmptyArray(elem) => {
                let name = self.ctx.fmt_datatype_symbol(&empty_arr_name(elem));
                write!(f, "{}", name)
            }
            chc::Term::SeqConcatArr(elem, args) => {
                let name = self.ctx.fmt_datatype_symbol(&seq_concat_arr_name(elem));
                write!(
                    f,
                    "({} {})",
                    name,
                    List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                )
            }
            chc::Term::SeqSubseqArr(elem, args) => {
                let name = self.ctx.fmt_datatype_symbol(&seq_subseq_arr_name(elem));
                write!(
                    f,
                    "({} {})",
                    name,
                    List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                )
            }
            chc::Term::Tuple(ts) => {
                let ss: Vec<_> = ts.iter().map(|t| self.clause.term_sort(t)).collect();
                if ss.is_empty() {
                    write!(f, "{}", self.ctx.tuple_ctor(&ss),)
                } else {
                    write!(
                        f,
                        "({} {})",
                        self.ctx.tuple_ctor(&ss),
                        List::open(ts.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                    )
                }
            }
            chc::Term::TupleProj(t, i) => {
                let s = self.clause.term_sort(t);
                write!(
                    f,
                    "({} {})",
                    self.ctx.tuple_proj(s.as_tuple().unwrap(), *i),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::DatatypeCtor(sort, sym, args) => {
                if args.is_empty() {
                    write!(f, "{}", self.ctx.datatype_ctor(sort, sym))
                } else {
                    write!(
                        f,
                        "({} {})",
                        self.ctx.datatype_ctor(sort, sym),
                        List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                    )
                }
            }
            chc::Term::DatatypeDiscr(_s, t) => {
                let s = self.clause.term_sort(t).into_datatype().unwrap();
                write!(
                    f,
                    "({} {})",
                    self.ctx.datatype_discr(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::FormulaQuantifiedVar(_, name) => write!(f, "{}", name),
        }
    }
}

impl<'ctx, 'a> Term<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Term) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Atom`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Atom<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Atom,
}

impl<'ctx, 'a> std::fmt::Display for Atom<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(guard) = &self.inner.guard {
            let guard = Formula::new(self.ctx, self.clause, guard);
            write!(f, "(=> {} ", guard)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, "(not ")?;
        }
        let pred = match &self.inner.pred {
            chc::Pred::Matcher(p) => self.ctx.matcher_pred(p).to_string(),
            p => p.name().into_owned(),
        };
        if self.inner.args.is_empty() {
            write!(f, "{}", pred)?;
        } else {
            let args = List::open(
                self.inner
                    .args
                    .iter()
                    .map(|t| Term::new(self.ctx, self.clause, t)),
            );
            write!(f, "({} {})", pred, args)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, ")")?;
        }
        if self.inner.guard.is_some() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'ctx, 'a> Atom<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Atom) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Formula`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Formula<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Formula,
}

impl<'ctx, 'a> std::fmt::Display for Formula<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Formula::Atom(atom) => {
                let atom = Atom::new(self.ctx, self.clause, atom);
                write!(f, "{}", atom)
            }
            chc::Formula::Not(fo) => {
                let fo = Formula::new(self.ctx, self.clause, fo);
                write!(f, "(not {})", fo)
            }
            chc::Formula::And(fs) => {
                let fs = List::open(fs.iter().map(|fo| Formula::new(self.ctx, self.clause, fo)));
                write!(f, "(and {})", fs)
            }
            chc::Formula::Or(fs) => {
                let fs = List::open(fs.iter().map(|fo| Formula::new(self.ctx, self.clause, fo)));
                write!(f, "(or {})", fs)
            }
            chc::Formula::Implies(lhs, rhs) => {
                let lhs = Formula::new(self.ctx, self.clause, lhs);
                let rhs = Formula::new(self.ctx, self.clause, rhs);
                write!(f, "(=> {lhs} {rhs})")
            }
            chc::Formula::Exists(vars, fo) => {
                let vars =
                    List::closed(vars.iter().map(|(v, s)| {
                        List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])
                    }));
                let fo = Formula::new(self.ctx, self.clause, fo);
                write!(f, "(exists {vars} {fo})")
            }
            chc::Formula::Forall(vars, fo) => {
                let vars =
                    List::closed(vars.iter().map(|(v, s)| {
                        List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])
                    }));
                let fo = Formula::new(self.ctx, self.clause, fo);
                write!(f, "(forall {vars} {fo})")
            }
        }
    }
}

impl<'ctx, 'a> Formula<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Formula) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Body`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Body<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Body,
}

impl<'ctx, 'a> std::fmt::Display for Body<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let atoms = List::open(
            self.inner
                .atoms
                .iter()
                .map(|a| Atom::new(self.ctx, self.clause, a)),
        );
        let formula = Formula::new(self.ctx, self.clause, &self.inner.formula);
        write!(f, "(and {atoms} {formula})")
    }
}

impl<'ctx, 'a> Body<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Body) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Clause`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Clause<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Clause,
}

impl<'ctx, 'a> std::fmt::Display for Clause<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.inner.debug_info.is_empty() {
            writeln!(f, "{}", self.inner.debug_info.display("; "))?;
        }
        let body = Body::new(self.ctx, self.inner, &self.inner.body);
        let head = Atom::new(self.ctx, self.inner, &self.inner.head);
        if !self.inner.vars.is_empty() {
            let vars = List::closed(
                self.inner
                    .vars
                    .iter_enumerated()
                    .map(|(v, s)| List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])),
            );
            write!(f, "(forall {vars} ")?;
        }
        write!(f, "(=> {body} {head})")?;
        if !self.inner.vars.is_empty() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'ctx, 'a> Clause<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Clause) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a [`chc::RawCommand`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct RawCommand<'a> {
    inner: &'a chc::RawCommand,
}

impl<'a> std::fmt::Display for RawCommand<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner.command,)
    }
}

impl<'a> RawCommand<'a> {
    pub fn new(inner: &'a chc::RawCommand) -> Self {
        Self { inner }
    }
}

/// A wrapper around a [`chc::DatatypeSelector`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct DatatypeSelector<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::DatatypeSelector,
}

impl<'ctx, 'a> std::fmt::Display for DatatypeSelector<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} {})",
            &self.inner.symbol,
            self.ctx.fmt_sort(&self.inner.sort)
        )
    }
}

impl<'ctx, 'a> DatatypeSelector<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::DatatypeSelector) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a [`chc::DatatypeCtor`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct DatatypeCtor<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::DatatypeCtor,
}

impl<'ctx, 'a> std::fmt::Display for DatatypeCtor<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let selectors = self
            .inner
            .selectors
            .iter()
            .map(|s| DatatypeSelector::new(self.ctx, s));
        write!(f, "    ({} {})", &self.inner.symbol, List::open(selectors))
    }
}

impl<'ctx, 'a> DatatypeCtor<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::DatatypeCtor) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a slice of [`chc::Datatype`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Datatypes<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a [chc::Datatype],
}

impl<'ctx, 'a> std::fmt::Display for Datatypes<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inner.is_empty() {
            return Ok(());
        }

        let datatypes = self
            .inner
            .iter()
            .map(|d| format!("({} 0)", self.ctx.fmt_datatype_symbol(&d.symbol)));
        let ctors = self.inner.iter().map(|d| {
            format!(
                "  (par () (\n{}\n  ))",
                List::multiline_open(d.ctors.iter().map(|c| DatatypeCtor::new(self.ctx, c)))
            )
        });
        write!(
            f,
            "(declare-datatypes {} {})",
            List::closed(datatypes),
            List::multiline_closed(ctors)
        )
    }
}

impl<'ctx, 'a> Datatypes<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a [chc::Datatype]) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a [`chc::Datatype`] that provides a [`std::fmt::Display`] implementation for the
/// discriminant function in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct DatatypeDiscrFun<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Datatype,
}

impl<'ctx, 'a> std::fmt::Display for DatatypeDiscrFun<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sym = &self.inner.symbol;
        let cases = self
            .inner
            .ctors
            .iter()
            .rfold("(- 1)".to_owned(), |acc, ctor| {
                format!(
                    "(ite ((_ is {ctor}) x) {discr} {acc})",
                    ctor = &ctor.symbol,
                    discr = ctor.discriminant,
                )
            });
        write!(
            f,
            "(define-fun {discr} ((x {sym})) Int {cases})",
            discr = self.ctx.datatype_discr_def(sym),
            sym = self.ctx.fmt_datatype_symbol(sym),
        )
    }
}

impl<'ctx, 'a> DatatypeDiscrFun<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Datatype) -> DatatypeDiscrFun<'ctx, 'a> {
        DatatypeDiscrFun { ctx, inner }
    }
}

/// A wrapper around a [`chc::Datatype`] that provides a [`std::fmt::Display`] implementation for the
/// matcher predicate in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct MatcherPredFun<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Datatype,
}

impl<'ctx, 'a> std::fmt::Display for MatcherPredFun<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sym = &self.inner.symbol;
        let mut offset = 0;
        let mut variants = Vec::new();
        for ctor in &self.inner.ctors {
            let args = List::open(
                (0..ctor.selectors.len())
                    .map(|i| i + offset)
                    .map(|i| format!("x{i}")),
            );
            offset += ctor.selectors.len();
            let repr = if ctor.selectors.is_empty() {
                ctor.symbol.to_string()
            } else {
                format!("({} {})", &ctor.symbol, args)
            };
            variants.push(format!("(= v {repr})"));
        }
        let params = List::closed(
            self.inner
                .ctors
                .iter()
                .flat_map(|c| &c.selectors)
                .enumerate()
                .map(|(idx, s)| format!("(x{} {})", idx, self.ctx.fmt_sort(&s.sort)))
                .chain([format!("(v {})", self.ctx.fmt_datatype_symbol(sym))]),
        );
        write!(
            f,
            "(define-fun {name} {params} Bool (or {variants}))",
            name = self.ctx.matcher_pred_def(sym),
            variants = List::open(variants),
        )
    }
}

impl<'ctx, 'a> MatcherPredFun<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Datatype) -> MatcherPredFun<'ctx, 'a> {
        MatcherPredFun { ctx, inner }
    }
}

pub struct UserDefinedPredDef<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::UserDefinedPredDef,
}

impl<'ctx, 'a> std::fmt::Display for UserDefinedPredDef<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = List::closed(
            self.inner
                .sig
                .iter()
                .map(|(name, sort)| format!("({} {})", name, self.ctx.fmt_sort(sort))),
        );
        write!(
            f,
            "(define-fun {name} {params} Bool {body})",
            name = self.inner.symbol,
            body = &self.inner.body,
        )
    }
}

impl<'ctx, 'a> UserDefinedPredDef<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::UserDefinedPredDef) -> Self {
        Self { ctx, inner }
    }
}
/// A wrapper around a [`chc::System`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct System<'a> {
    ctx: FormatContext,
    inner: &'a chc::System,
}

impl<'a> std::fmt::Display for System<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(set-logic HORN)\n")?;

        writeln!(f, "{}\n", Datatypes::new(&self.ctx, self.ctx.datatypes()))?;
        for datatype in self.ctx.datatypes() {
            writeln!(f, "{}", DatatypeDiscrFun::new(&self.ctx, datatype))?;
            writeln!(f, "{}", MatcherPredFun::new(&self.ctx, datatype))?;
        }

        // insert command from #![thrust::raw_command()] here
        for raw_command in &self.inner.raw_commands {
            writeln!(f, "{}\n", RawCommand::new(raw_command))?;
        }

        for elem in &collect_empty_array_value_sorts(self.inner) {
            let name = self.ctx.fmt_datatype_symbol(&empty_arr_name(elem));
            let elem_ty = self.ctx.fmt_sort(elem);
            let default = DefaultValue::new(&self.ctx, elem);
            writeln!(
                f,
                "(define-fun {name} () (Array Int {elem_ty}) \
                 ((as const (Array Int {elem_ty})) {default}))\n",
            )?;
        }
        for elem in &self.inner.uses_seq_concat {
            let name = self.ctx.fmt_datatype_symbol(&seq_concat_arr_name(elem));
            let elem_ty = self.ctx.fmt_sort(elem);
            writeln!(
                f,
                "(define-fun-rec {name} \
                  ((sa (Array Int {elem_ty})) (sn Int) (ta (Array Int {elem_ty})) (tn Int)) \
                  (Array Int {elem_ty}) \
                  (ite (<= tn 0) sa \
                       (store ({name} sa sn ta (- tn 1)) \
                              (+ sn (- tn 1)) \
                              (select ta (- tn 1)))))\n",
            )?;
        }
        for elem in &self.inner.uses_seq_subseq {
            let name = self.ctx.fmt_datatype_symbol(&seq_subseq_arr_name(elem));
            let elem_ty = self.ctx.fmt_sort(elem);
            let base = self.ctx.fmt_datatype_symbol(&empty_arr_name(elem));
            writeln!(
                f,
                "(define-fun-rec {name} \
                  ((a (Array Int {elem_ty})) (l Int) (r Int)) (Array Int {elem_ty}) \
                  (ite (<= r l) {base} \
                       (store ({name} a l (- r 1)) \
                              (- (- r 1) l) \
                              (select a (- r 1)))))\n",
            )?;
        }

        for user_defined_pred_def in &self.inner.user_defined_pred_defs {
            writeln!(
                f,
                "{}\n",
                UserDefinedPredDef::new(&self.ctx, user_defined_pred_def)
            )?;
        }

        writeln!(f)?;
        for (p, def) in self.inner.pred_vars.iter_enumerated() {
            if !def.debug_info.is_empty() {
                writeln!(f, "{}", def.debug_info.display("; "))?;
            }
            writeln!(
                f,
                "(declare-fun {} {} Bool)\n",
                p,
                List::closed(def.sig.iter().map(|s| self.ctx.fmt_sort(s)))
            )?;
        }
        for (id, clause) in self.inner.clauses.iter_enumerated() {
            writeln!(
                f,
                "; {:?}\n(assert {})\n",
                id,
                Clause::new(&self.ctx, clause)
            )?;
        }
        Ok(())
    }
}

impl<'a> System<'a> {
    pub fn new(inner: &'a chc::System) -> Self {
        let ctx = FormatContext::from_system(inner);
        Self { ctx, inner }
    }
}
