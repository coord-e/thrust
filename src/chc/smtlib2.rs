use crate::chc;

#[derive(Debug, Clone)]
struct List<T> {
    closed: bool,
    items: Vec<T>,
}

impl<T> std::fmt::Display for List<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.closed {
            write!(f, "(")?;
        }
        for (i, e) in self.items.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", e)?;
        }
        if self.closed {
            write!(f, ")")?;
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
            closed: true,
            items: inner.into_iter().collect(),
        }
    }

    pub fn open<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            closed: false,
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
            chc::Sort::Box(s) => write!(f, "(Box {})", Sort::new(s)),
            chc::Sort::Mut(s) => write!(f, "(Mut {})", Sort::new(s)),
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
    inner: &'a chc::Term,
}

impl<'a> std::fmt::Display for Term<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Term::Var(v) => write!(f, "{}", v),
            chc::Term::Int(i) => write!(f, "{}", i),
            chc::Term::Bool(b) => write!(f, "{}", b),
            chc::Term::String(s) => write!(f, "\"{}\"", s.escape_default()),
            chc::Term::Box(t) => write!(f, "(box {})", Term::new(t)),
            chc::Term::Mut(t1, t2) => write!(f, "(mut {} {})", Term::new(t1), Term::new(t2)),
            chc::Term::BoxCurrent(t) => write!(f, "(box_current {})", Term::new(t)),
            chc::Term::MutCurrent(t) => write!(f, "(mut_current {})", Term::new(t)),
            chc::Term::MutFinal(t) => write!(f, "(mut_final {})", Term::new(t)),
            chc::Term::App(fn_, args) => {
                write!(f, "({} {})", fn_, List::open(args.iter().map(Term::new)))
            }
        }
    }
}

impl<'a> Term<'a> {
    pub fn new(inner: &'a chc::Term) -> Self {
        Self { inner }
    }
}

#[derive(Debug, Clone)]
pub struct Atom<'a> {
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
            let args = List::open(self.inner.args.iter().map(Term::new));
            write!(f, "({} {})", self.inner.pred.name(), args)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'a> Atom<'a> {
    pub fn new(inner: &'a chc::Atom) -> Self {
        Self { inner }
    }
}

#[derive(Debug, Clone)]
pub struct Clause<'a> {
    inner: &'a chc::Clause,
}

impl<'a> std::fmt::Display for Clause<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let body = List::open(self.inner.body.iter().map(Atom::new));
        let head = Atom::new(&self.inner.head);
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
        writeln!(f, "(define-fun != ((x Int) (y Int)) Bool (not (= x y)))")?;
        writeln!(f, "(declare-datatypes (T) ((Box (box (box_current T)))))")?;
        writeln!(
            f,
            "(declare-datatypes (T) ((Mut (mut (mut_current T) (mut_final T)))))"
        )?;
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

impl<'a> System<'a> {
    pub fn new(inner: &'a chc::System) -> Self {
        Self { inner }
    }
}
