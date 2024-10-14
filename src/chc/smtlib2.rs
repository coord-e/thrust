use crate::chc::{self, format_context::FormatContext};

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
            chc::Term::Tuple(ts) => {
                let ss: Vec<_> = ts.iter().map(|t| self.clause.term_sort(t)).collect();
                write!(
                    f,
                    "({} {})",
                    self.ctx.tuple_ctor(&ss),
                    List::open(ts.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                )
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
            chc::Term::DatatypeCtor(_, sym, args) => {
                write!(
                    f,
                    "({} {})",
                    sym,
                    List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                )
            }
            chc::Term::DatatypeDiscr(s, t) => {
                write!(
                    f,
                    "(|datatype_discr{}| {})",
                    self.ctx.fmt_datatype_symbol(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
        }
    }
}

impl<'ctx, 'a> Term<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Term) -> Self {
        Self { ctx, clause, inner }
    }
}

#[derive(Debug, Clone)]
pub struct Atom<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Atom,
}

impl<'ctx, 'a> std::fmt::Display for Atom<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inner.pred.is_negative() {
            write!(f, "(not ")?;
        }
        if self.inner.args.is_empty() {
            write!(f, "{}", self.inner.pred.name())?;
        } else {
            let args = List::open(
                self.inner
                    .args
                    .iter()
                    .map(|t| Term::new(self.ctx, self.clause, t)),
            );
            write!(f, "({} {})", self.inner.pred.name(), args)?;
        }
        if self.inner.pred.is_negative() {
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

#[derive(Debug, Clone)]
pub struct Clause<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Clause,
}

impl<'ctx, 'a> std::fmt::Display for Clause<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let body = List::open(
            self.inner
                .body
                .iter()
                .map(|a| Atom::new(self.ctx, self.inner, a)),
        );
        let head = Atom::new(self.ctx, self.inner, &self.inner.head);
        if self.inner.vars.is_empty() {
            write!(f, "(=> (and {body}) {head})")
        } else {
            let vars = List::closed(
                self.inner
                    .vars
                    .iter_enumerated()
                    .map(|(v, s)| List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])),
            );
            write!(f, "(forall {vars} (=> (and {body}) {head}))")
        }
    }
}

impl<'ctx, 'a> Clause<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Clause) -> Self {
        Self { ctx, inner }
    }
}

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
        write!(f, "({} {})", &self.inner.symbol, List::open(selectors))
    }
}

impl<'ctx, 'a> DatatypeCtor<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::DatatypeCtor) -> Self {
        Self { ctx, inner }
    }
}

#[derive(Debug, Clone)]
pub struct Datatypes<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a [chc::Datatype],
}

impl<'ctx, 'a> std::fmt::Display for Datatypes<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let datatypes = self
            .inner
            .iter()
            .map(|d| format!("({} 0)", self.ctx.fmt_datatype_symbol(&d.symbol)));
        let ctors = self.inner.iter().map(|d| {
            format!(
                "(par () {})",
                List::multiline_closed(d.ctors.iter().map(|c| DatatypeCtor::new(self.ctx, c)))
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
        writeln!(
            f,
            "(define-fun |datatype_discr{sym}| ((x {sym})) Int {cases})",
            sym = self.ctx.fmt_datatype_symbol(sym),
        )
    }
}

impl<'ctx, 'a> DatatypeDiscrFun<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Datatype) -> DatatypeDiscrFun<'ctx, 'a> {
        DatatypeDiscrFun { ctx, inner }
    }
}

#[derive(Debug, Clone)]
pub struct System<'a> {
    ctx: FormatContext,
    inner: &'a chc::System,
}

impl<'a> std::fmt::Display for System<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(set-logic HORN)")?;

        writeln!(f, "{}", Datatypes::new(&self.ctx, self.ctx.datatypes()))?;
        for datatype in &self.inner.datatypes {
            writeln!(f, "{}", DatatypeDiscrFun::new(&self.ctx, datatype))?;
        }
        for (p, sorts) in self.inner.pred_vars.iter_enumerated() {
            writeln!(
                f,
                "(declare-fun {} {} Bool)",
                p,
                List::closed(sorts.iter().map(|s| self.ctx.fmt_sort(s)))
            )?;
        }
        for clause in &self.inner.clauses {
            writeln!(f, "(assert {})", Clause::new(&self.ctx, clause))?;
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
