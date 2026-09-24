//! Wrappers around CHC structures to display them in SMT-LIB2 format.
//!
//! The main entry point is the [`System`] wrapper, which takes a [`chc::System`] and provides a
//! [`std::fmt::Display`] implementation that produces a complete SMT-LIB2.
//! It uses [`FormatContext`] to handle the complexities of the conversion,
//! such as naming convention and solver-specific workarounds.
//! The output of this module is what gets passed to the external CHC solver.

use std::collections::BTreeSet;

use rustc_index::IndexVec;

use crate::chc::{self, format_context::FormatContext};

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
#[derive(Clone)]
struct Term<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    // we need variable sorts to select box/mut selector/constructor
    var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
    inner: &'a chc::Term,
}

impl<'ctx, 'a> std::fmt::Display for Term<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Term::Null => write!(f, "null"),
            chc::Term::ForallDefault(idx) => write!(f, "default_{idx}"),
            chc::Term::Var(v) => write!(f, "{}", v),
            chc::Term::Int(i) => write!(f, "{}", i),
            chc::Term::Bool(b) => write!(f, "{}", b),
            chc::Term::String(s) => write!(f, "\"{}\"", s.escape_default()),
            chc::Term::Box(t) => {
                let s = t.sort(|v| self.var_sorts[*v].clone());
                write!(
                    f,
                    "({} {})",
                    self.ctx.box_ctor(&s),
                    Term::new(self.ctx, self.var_sorts, t)
                )
            }
            chc::Term::Mut(t1, t2) => {
                let s = t1.sort(|v| self.var_sorts[*v].clone());
                write!(
                    f,
                    "({} {} {})",
                    self.ctx.mut_ctor(&s),
                    Term::new(self.ctx, self.var_sorts, t1),
                    Term::new(self.ctx, self.var_sorts, t2)
                )
            }
            chc::Term::BoxCurrent(t) => {
                let s = t.sort(|v| self.var_sorts[*v].clone()).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.box_current(&s),
                    Term::new(self.ctx, self.var_sorts, t)
                )
            }
            chc::Term::MutCurrent(t) => {
                let s = t.sort(|v| self.var_sorts[*v].clone()).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.mut_current(&s),
                    Term::new(self.ctx, self.var_sorts, t)
                )
            }
            chc::Term::MutFinal(t) => {
                let s = t.sort(|v| self.var_sorts[*v].clone()).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.mut_final(&s),
                    Term::new(self.ctx, self.var_sorts, t)
                )
            }
            chc::Term::App(fn_, args) => {
                write!(
                    f,
                    "({} {})",
                    fn_,
                    List::open(args.iter().map(|t| Term::new(self.ctx, self.var_sorts, t)))
                )
            }
            chc::Term::ArrayEmpty(index, elem) => {
                let index_sort = self.ctx.fmt_sort(index);
                let elem_sort = self.ctx.fmt_sort(elem);
                let default = chc::Term::default_for(elem);
                write!(
                    f,
                    "((as const (Array {index_sort} {elem_sort})) {})",
                    Term::new(self.ctx, self.var_sorts, &default)
                )
            }
            chc::Term::SeqEmpty(elem) => {
                write!(f, "(as seq.empty (Seq {}))", self.ctx.fmt_sort(elem))
            }
            chc::Term::Tuple(ts) => {
                let ss: Vec<_> = ts
                    .iter()
                    .map(|t| t.sort(|v| self.var_sorts[*v].clone()))
                    .collect();
                if ss.is_empty() {
                    write!(f, "{}", self.ctx.tuple_ctor(&ss),)
                } else {
                    write!(
                        f,
                        "({} {})",
                        self.ctx.tuple_ctor(&ss),
                        List::open(ts.iter().map(|t| Term::new(self.ctx, self.var_sorts, t)))
                    )
                }
            }
            chc::Term::TupleProj(t, i) => {
                let s = t.sort(|v| self.var_sorts[*v].clone());
                write!(
                    f,
                    "({} {})",
                    self.ctx.tuple_proj(s.as_tuple().unwrap(), *i),
                    Term::new(self.ctx, self.var_sorts, t)
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
                        List::open(args.iter().map(|t| Term::new(self.ctx, self.var_sorts, t)))
                    )
                }
            }
            chc::Term::DatatypeDiscr(_s, t) => {
                let s = t
                    .sort(|v| self.var_sorts[*v].clone())
                    .into_datatype()
                    .unwrap();
                write!(
                    f,
                    "({} {})",
                    self.ctx.datatype_discr(&s),
                    Term::new(self.ctx, self.var_sorts, t)
                )
            }
            chc::Term::FormulaQuantifiedVar(_, name) => write!(f, "{}", name),
        }
    }
}

impl<'ctx, 'a> Term<'ctx, 'a> {
    pub fn new(
        ctx: &'ctx FormatContext,
        var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
        inner: &'a chc::Term,
    ) -> Self {
        Self {
            ctx,
            var_sorts,
            inner,
        }
    }
}

/// A wrapper around a [`chc::Atom`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Clone)]
pub struct Atom<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
    inner: &'a chc::Atom,
}

impl<'ctx, 'a> std::fmt::Display for Atom<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(guard) = &self.inner.guard {
            let guard = Formula::new(self.ctx, self.var_sorts, guard);
            write!(f, "(=> {} ", guard)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, "(not ")?;
        }
        let pred = match &self.inner.pred {
            chc::Pred::Matcher(p) => self.ctx.matcher_pred(p).to_string(),
            chc::Pred::ForallPred(p) => self.ctx.forall_pred(p).to_string(),
            p => p.name().into_owned(),
        };
        if self.inner.args.is_empty() {
            write!(f, "{}", pred)?;
        } else {
            let args = List::open(
                self.inner
                    .args
                    .iter()
                    .map(|t| Term::new(self.ctx, self.var_sorts, t)),
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
    pub fn new(
        ctx: &'ctx FormatContext,
        var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
        inner: &'a chc::Atom,
    ) -> Self {
        Self {
            ctx,
            var_sorts,
            inner,
        }
    }
}

/// A wrapper around a [`chc::Formula`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Clone)]
pub struct Formula<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
    inner: &'a chc::Formula,
}

impl<'ctx, 'a> std::fmt::Display for Formula<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Formula::Atom(atom) => {
                let atom = Atom::new(self.ctx, self.var_sorts, atom);
                write!(f, "{}", atom)
            }
            chc::Formula::Not(fo) => {
                let fo = Formula::new(self.ctx, self.var_sorts, fo);
                write!(f, "(not {})", fo)
            }
            chc::Formula::And(fs) => {
                let fs = List::open(
                    fs.iter()
                        .map(|fo| Formula::new(self.ctx, self.var_sorts, fo)),
                );
                write!(f, "(and {})", fs)
            }
            chc::Formula::Or(fs) => {
                let fs = List::open(
                    fs.iter()
                        .map(|fo| Formula::new(self.ctx, self.var_sorts, fo)),
                );
                write!(f, "(or {})", fs)
            }
            chc::Formula::Implies(lhs, rhs) => {
                let lhs = Formula::new(self.ctx, self.var_sorts, lhs);
                let rhs = Formula::new(self.ctx, self.var_sorts, rhs);
                write!(f, "(=> {lhs} {rhs})")
            }
            chc::Formula::Exists(vars, fo) => {
                let vars =
                    List::closed(vars.iter().map(|(v, s)| {
                        List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])
                    }));
                let fo = Formula::new(self.ctx, self.var_sorts, fo);
                write!(f, "(exists {vars} {fo})")
            }
            chc::Formula::Forall(vars, fo) => {
                let vars =
                    List::closed(vars.iter().map(|(v, s)| {
                        List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])
                    }));
                let fo = Formula::new(self.ctx, self.var_sorts, fo);
                write!(f, "(forall {vars} {fo})")
            }
        }
    }
}

impl<'ctx, 'a> Formula<'ctx, 'a> {
    pub fn new(
        ctx: &'ctx FormatContext,
        var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
        inner: &'a chc::Formula,
    ) -> Self {
        Self {
            ctx,
            var_sorts,
            inner,
        }
    }
}

/// A wrapper around a [`chc::Body`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Clone)]
pub struct Body<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
    inner: &'a chc::Body,
}

impl<'ctx, 'a> std::fmt::Display for Body<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let atoms = List::open(
            self.inner
                .atoms
                .iter()
                .map(|a| Atom::new(self.ctx, self.var_sorts, a)),
        );
        let formula = Formula::new(self.ctx, self.var_sorts, &self.inner.formula);
        write!(f, "(and {atoms} {formula})")
    }
}

impl<'ctx, 'a> Body<'ctx, 'a> {
    pub fn new(
        ctx: &'ctx FormatContext,
        var_sorts: &'a IndexVec<chc::TermVarIdx, chc::Sort>,
        inner: &'a chc::Body,
    ) -> Self {
        Self {
            ctx,
            var_sorts,
            inner,
        }
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
        let body = Body::new(self.ctx, &self.inner.vars, &self.inner.body);
        let head = Atom::new(self.ctx, &self.inner.vars, &self.inner.head);
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

struct ClauseComments<'a> {
    clause: &'a chc::Clause,
}

fn write_comment(
    f: &mut std::fmt::Formatter<'_>,
    indent: usize,
    text: impl std::fmt::Display,
) -> std::fmt::Result {
    for line in text.to_string().lines() {
        writeln!(f, "; {:indent$}{line}", "")?;
    }
    Ok(())
}

fn write_origin_entry(
    f: &mut std::fmt::Formatter<'_>,
    indent: usize,
    entry: &chc::debug::origin::Entry,
) -> std::fmt::Result {
    write_comment(f, indent, entry.text())?;
    for mapping in entry.mappings() {
        write_comment(f, indent + 2, mapping)?;
    }
    Ok(())
}

impl std::fmt::Display for ClauseComments<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.clause.debug_info.is_empty() {
            writeln!(f, "{}", self.clause.debug_info.display("; "))?;
        }
        let origin = &self.clause.origin;
        if !origin.environment.is_empty() {
            write_comment(f, 0, "Γ")?;
            for entry in &origin.environment {
                write_origin_entry(f, 2, entry)?;
            }
        }
        if !origin.body.is_empty() {
            write_comment(f, 0, "body:")?;
            for entry in &origin.body {
                write_origin_entry(f, 2, entry)?;
            }
        }
        write_comment(f, 0, format_args!("head: {}", origin.head.text()))?;
        for mapping in origin.head.mappings() {
            write_comment(f, 2, mapping)?;
        }
        Ok(())
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
            "(define-fun {name} {params} Bool ",
            name = self.inner.symbol,
        )?;
        match &self.inner.body {
            chc::UserDefinedPredBody::Raw(body) => write!(f, "{body}")?,
            chc::UserDefinedPredBody::Formula(formula) => {
                let var_sorts: IndexVec<chc::TermVarIdx, chc::Sort> = self
                    .inner
                    .sig
                    .iter()
                    .map(|(_, sort)| sort.clone())
                    .collect();
                write!(f, "{}", Formula::new(self.ctx, &var_sorts, formula))?;
            }
        }
        write!(f, ")")
    }
}

impl<'ctx, 'a> UserDefinedPredDef<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::UserDefinedPredDef) -> Self {
        Self { ctx, inner }
    }
}

pub struct ForallPredDef<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    pred: &'a chc::ForallPred,
}

impl<'ctx, 'a> std::fmt::Display for ForallPredDef<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self.pred.params.iter().map(|sort| self.ctx.fmt_sort(sort));
        let params = List::closed(params);
        write!(
            f,
            "(declare-forall-fun {name} {params} Bool)",
            name = self.ctx.forall_pred(self.pred),
        )
    }
}

impl<'ctx, 'a> ForallPredDef<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, pred: &'a chc::ForallPred) -> Self {
        Self { ctx, pred }
    }
}

pub struct DepExistsPredVarDef<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    id: &'a chc::PredVarId,
    def: &'a chc::PredVarDef,
    // A `BTreeSet`, not a `HashSet`: `fmt` below iterates this directly to
    // list a `declare-dep-exists-fun`'s dependencies, so whatever order it
    // arrives in is the order emitted. It is ordered where it is built, in
    // `chc::System::compute_dependency`, rather than sorted here.
    dependencies: &'a BTreeSet<chc::ForallPred>,
}

impl<'ctx, 'a> std::fmt::Display for DepExistsPredVarDef<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.def.debug_info.is_empty() {
            writeln!(f, "{}", self.def.debug_info.display("; "))?;
        }
        writeln!(
            f,
            "(declare-dep-exists-fun {} {} {} Bool)",
            self.id,
            List::closed(self.dependencies.iter().map(|p| self.ctx.forall_pred(p))),
            List::closed(self.def.sig.iter().map(|s| self.ctx.fmt_sort(s))),
        )
    }
}

impl<'ctx, 'a> DepExistsPredVarDef<'ctx, 'a> {
    pub fn new(
        ctx: &'ctx FormatContext,
        id: &'a chc::PredVarId,
        def: &'a chc::PredVarDef,
        dependencies: &'a BTreeSet<chc::ForallPred>,
    ) -> Self {
        Self {
            ctx,
            id,
            def,
            dependencies,
        }
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

        for forall_sort_def in &self.inner.forall_sorts {
            if !forall_sort_def.debug_info.is_empty() {
                writeln!(f, "{}", forall_sort_def.debug_info.display("; "))?;
            }
            writeln!(f, "(declare-forall-sort {})\n", forall_sort_def.idx)?;
        }
        let used_forall_defaults = self.inner.used_forall_default_sorts();
        for forall_sort_def in &self.inner.forall_sorts {
            if !used_forall_defaults.contains(&forall_sort_def.idx) {
                continue;
            }
            // The padding of an empty array at an abstract element sort: an arbitrary but
            // fixed value that nothing is allowed to observe. Under `(set-logic HORN)` a
            // top-level `declare-const` names something the solver must *build*, and an
            // abstract sort has no value the solver can build, so that spelling stops the
            // query at the parser. A nullary `declare-forall-fun` is the universal reading:
            // the clauses have to hold whatever the padding is, which is what "nothing may
            // observe it" means.
            writeln!(
                f,
                "(declare-forall-fun default_{} () {})\n",
                forall_sort_def.idx, forall_sort_def.idx
            )?;
        }

        writeln!(f, "{}\n", Datatypes::new(&self.ctx, self.ctx.datatypes()))?;
        for datatype in self.ctx.datatypes() {
            writeln!(f, "{}", DatatypeDiscrFun::new(&self.ctx, datatype))?;
            writeln!(f, "{}", MatcherPredFun::new(&self.ctx, datatype))?;
        }

        for pred in &self.inner.forall_pred_vars {
            writeln!(f, "{}\n", ForallPredDef::new(&self.ctx, pred))?;
        }

        // insert command from #![thrust::raw_command()] here
        for raw_command in &self.inner.raw_commands {
            writeln!(f, "{}\n", RawCommand::new(raw_command))?;
        }

        for user_defined_pred_def in self.inner.user_defined_preds_in_dependency_order() {
            writeln!(
                f,
                "{}\n",
                UserDefinedPredDef::new(&self.ctx, user_defined_pred_def)
            )?;
        }

        writeln!(f)?;
        let dependencies = self.inner.compute_dependency();
        for (p, def) in self.inner.pred_vars.iter_enumerated() {
            if dependencies.contains_key(&p) && !dependencies[&p].is_empty() {
                writeln!(
                    f,
                    "{}\n",
                    DepExistsPredVarDef::new(&self.ctx, &p, def, &dependencies[&p])
                )?;
            } else {
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
        }
        for (id, clause) in self.inner.clauses.iter_enumerated() {
            writeln!(
                f,
                "; {:?}\n{}(assert {})\n",
                id,
                ClauseComments { clause },
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
