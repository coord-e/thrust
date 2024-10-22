/// Multi-sorted CHC system with tuples.
use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;

mod clause_builder;
mod format_context;
mod hoice;
mod smtlib2;
mod solver;
mod unbox;

pub use clause_builder::{ClauseBuilder, Var};
pub use solver::{CheckSatError, Config};
pub use unbox::unbox;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DatatypeSymbol {
    inner: String,
}

impl std::fmt::Display for DatatypeSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b DatatypeSymbol
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.text(self.inner.clone())
    }
}

impl DatatypeSymbol {
    pub fn new(inner: String) -> Self {
        DatatypeSymbol { inner }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    Null,
    Int,
    Bool,
    String,
    Box(Box<Sort>),
    Mut(Box<Sort>),
    Tuple(Vec<Sort>),
    Datatype(DatatypeSymbol),
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Sort
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Sort::Null => allocator.text("null"),
            Sort::Int => allocator.text("int"),
            Sort::Bool => allocator.text("bool"),
            Sort::String => allocator.text("string"),
            Sort::Box(s) => allocator
                .text("box")
                .append(allocator.line())
                .append(s.pretty_atom(allocator))
                .group(),
            Sort::Mut(s) => allocator
                .text("mut")
                .append(allocator.line())
                .append(s.pretty_atom(allocator))
                .group(),
            Sort::Tuple(ss) => {
                let separator = allocator.text(",").append(allocator.line());
                if ss.len() == 1 {
                    ss[0].pretty(allocator).append(separator).parens().group()
                } else {
                    allocator
                        .intersperse(ss.iter().map(|s| s.pretty(allocator)), separator)
                        .parens()
                        .group()
                }
            }
            Sort::Datatype(symbol) => symbol.pretty(allocator),
        }
    }
}

impl Sort {
    fn pretty_atom<'b, 'a, D>(
        &'b self,
        allocator: &'a D,
    ) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec>
    where
        D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        match &self {
            Sort::Box(_) | Sort::Mut(_) => self.pretty(allocator).parens(),
            _ => self.pretty(allocator),
        }
    }

    fn walk<'a>(&'a self, f: impl FnMut(&'a Sort)) {
        self.walk_impl(Box::new(f))
    }

    fn walk_impl<'a, 'b>(&'a self, mut f: Box<dyn FnMut(&'a Sort) + 'b>) {
        f(self);
        match self {
            Sort::Box(s) | Sort::Mut(s) => s.walk(Box::new(&mut f)),
            Sort::Tuple(ss) => {
                for s in ss {
                    s.walk(Box::new(&mut f));
                }
            }
            _ => {}
        }
    }

    fn deref(self) -> Self {
        match self {
            Sort::Box(s) => *s,
            Sort::Mut(s) => *s,
            _ => panic!("invalid deref"),
        }
    }

    fn tuple_elem(self, index: usize) -> Self {
        match self {
            Sort::Tuple(ss) => ss[index].clone(),
            _ => panic!("invalid tuple_elem"),
        }
    }

    pub fn as_tuple(&self) -> Option<&[Sort]> {
        match self {
            Sort::Tuple(ss) => Some(ss),
            _ => None,
        }
    }

    pub fn null() -> Self {
        Sort::Null
    }

    pub fn int() -> Self {
        Sort::Int
    }

    pub fn string() -> Self {
        Sort::String
    }

    pub fn bool() -> Self {
        Sort::Bool
    }

    pub fn box_(sort: Sort) -> Self {
        Sort::Box(Box::new(sort))
    }

    pub fn mut_(sort: Sort) -> Self {
        Sort::Mut(Box::new(sort))
    }

    pub fn tuple(sorts: Vec<Sort>) -> Self {
        Sort::Tuple(sorts)
    }

    pub fn datatype(symbol: DatatypeSymbol) -> Self {
        Sort::Datatype(symbol)
    }

    pub fn is_singleton(&self) -> bool {
        match self {
            Sort::Null => true,
            Sort::Tuple(ts) => ts.iter().all(Sort::is_singleton),
            Sort::Box(s) => s.is_singleton(),
            Sort::Mut(s) => s.is_singleton(),
            _ => false,
        }
    }
}

rustc_index::newtype_index! {
    #[debug_format = "v{}"]
    pub struct TermVarIdx { }
}

impl std::fmt::Display for TermVarIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "v{}", self.index())
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b TermVarIdx
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self).annotate(TermVarIdx::color_spec())
    }
}

impl TermVarIdx {
    fn color_spec() -> termcolor::ColorSpec {
        termcolor::ColorSpec::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Function {
    name: &'static str,
    is_infix: bool,
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.name)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Function
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self).annotate(Function::color_spec())
    }
}

impl Function {
    fn color_spec() -> termcolor::ColorSpec {
        termcolor::ColorSpec::new()
    }

    const fn new(name: &'static str) -> Self {
        Function {
            name,
            is_infix: false,
        }
    }

    const fn infix(name: &'static str) -> Self {
        Function {
            name,
            is_infix: true,
        }
    }

    pub fn name(&self) -> &str {
        self.name
    }

    pub fn is_infix(&self) -> bool {
        self.is_infix
    }

    fn sort<I>(&self, _args: I) -> Sort
    where
        I: IntoIterator<Item = Sort>,
    {
        match *self {
            Self::ADD => Sort::int(),
            Self::SUB => Sort::int(),
            Self::MUL => Sort::int(),
            Self::EQ => Sort::bool(),
            Self::GE => Sort::bool(),
            Self::GT => Sort::bool(),
            Self::LE => Sort::bool(),
            Self::LT => Sort::bool(),
            Self::NOT => Sort::bool(),
            Self::NEG => Sort::int(),
            _ => unimplemented!(),
        }
    }

    pub const ADD: Function = Function::infix("+");
    pub const SUB: Function = Function::infix("-");
    pub const MUL: Function = Function::infix("*");
    pub const EQ: Function = Function::infix("=");
    pub const GE: Function = Function::infix(">=");
    pub const GT: Function = Function::infix(">");
    pub const LE: Function = Function::infix("<=");
    pub const LT: Function = Function::infix("<");
    pub const NOT: Function = Function::new("not");
    pub const NEG: Function = Function::new("-");
}

#[derive(Debug, Clone)]
pub enum Term<V = TermVarIdx> {
    Null,
    Var(V),
    Bool(bool),
    Int(i64),
    String(String),
    Box(Box<Term<V>>),
    Mut(Box<Term<V>>, Box<Term<V>>),
    BoxCurrent(Box<Term<V>>),
    MutCurrent(Box<Term<V>>),
    MutFinal(Box<Term<V>>),
    App(Function, Vec<Term<V>>),
    Tuple(Vec<Term<V>>),
    TupleProj(Box<Term<V>>, usize),
    DatatypeCtor(DatatypeSymbol, DatatypeSymbol, Vec<Term<V>>),
    DatatypeDiscr(DatatypeSymbol, Box<Term<V>>),
}

impl<'a, 'b, D, V> Pretty<'a, D, termcolor::ColorSpec> for &'b Term<V>
where
    V: Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Term::Null => allocator.text("null"),
            Term::Var(var) => allocator.text(format!("{var:?}")),
            Term::Int(n) => allocator.as_string(n),
            Term::Bool(b) => allocator.as_string(b),
            Term::String(s) => allocator.text(s.clone()).double_quotes(),
            Term::Box(t) => t.pretty(allocator).angles(),
            Term::Mut(t1, t2) => t1
                .pretty(allocator)
                .append(allocator.text(","))
                .append(allocator.line())
                .append(t2.pretty(allocator))
                .angles(),
            Term::BoxCurrent(t) | Term::MutCurrent(t) => {
                allocator.text("*").append(t.pretty(allocator))
            }
            Term::MutFinal(t) => allocator.text("°").append(t.pretty(allocator)),
            Term::App(f, args) if f.is_infix() => args[0]
                .pretty_atom(allocator)
                .append(allocator.line())
                .append(f.pretty(allocator))
                .append(allocator.line())
                .append(args[1].pretty_atom(allocator))
                .group(),
            Term::App(f, args) => {
                let inner = allocator.intersperse(
                    args.iter().map(|t| t.pretty_atom(allocator)),
                    allocator.line(),
                );
                let f = f.pretty(allocator);
                if args.is_empty() {
                    f
                } else {
                    f.append(allocator.line()).append(inner.nest(2)).group()
                }
            }
            Term::Tuple(ts) => {
                let separator = allocator.text(",").append(allocator.line());
                if ts.len() == 1 {
                    ts[0].pretty(allocator).append(separator).parens()
                } else {
                    allocator
                        .intersperse(ts.iter().map(|t| t.pretty(allocator)), separator)
                        .parens()
                }
            }
            Term::TupleProj(t, i) => t
                .pretty_atom(allocator)
                .append(allocator.text("."))
                .append(allocator.as_string(i)),
            Term::DatatypeCtor(_, symbol, args) => {
                let separator = allocator.text(",").append(allocator.line());
                let args = allocator
                    .intersperse(args.iter().map(|t| t.pretty(allocator)), separator)
                    .parens();
                symbol.pretty(allocator).append(args).group()
            }
            Term::DatatypeDiscr(_, t) => allocator
                .text("discriminant")
                .append(t.pretty(allocator).parens()),
        }
    }
}

impl<V> Term<V> {
    fn pretty_atom<'b, 'a, D>(
        &'b self,
        allocator: &'a D,
    ) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec>
    where
        V: Var,
        D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        match &self {
            Term::App(_f, args) if !args.is_empty() => self.pretty(allocator).parens(),
            _ => self.pretty(allocator),
        }
    }

    // TODO: ?
    fn subst_var_impl<F, W>(self, mut f: Box<dyn FnMut(V) -> Term<W> + '_>) -> Term<W> {
        match self {
            Term::Null => Term::Null,
            Term::Var(v) => f(v),
            Term::Bool(b) => Term::Bool(b),
            Term::Int(n) => Term::Int(n),
            Term::String(s) => Term::String(s),
            Term::Box(t) => Term::Box(Box::new(t.subst_var(f))),
            Term::Mut(t1, t2) => {
                Term::Mut(Box::new(t1.subst_var(&mut f)), Box::new(t2.subst_var(f)))
            }
            Term::BoxCurrent(t) => Term::BoxCurrent(Box::new(t.subst_var(f))),
            Term::MutCurrent(t) => Term::MutCurrent(Box::new(t.subst_var(f))),
            Term::MutFinal(t) => Term::MutFinal(Box::new(t.subst_var(f))),
            Term::App(fun, args) => {
                Term::App(fun, args.into_iter().map(|t| t.subst_var(&mut f)).collect())
            }
            Term::Tuple(ts) => Term::Tuple(ts.into_iter().map(|t| t.subst_var(&mut f)).collect()),
            Term::TupleProj(t, i) => Term::TupleProj(Box::new(t.subst_var(f)), i),
            Term::DatatypeCtor(d_sym, c_sym, args) => Term::DatatypeCtor(
                d_sym,
                c_sym,
                args.into_iter().map(|t| t.subst_var(&mut f)).collect(),
            ),
            Term::DatatypeDiscr(d_sym, t) => Term::DatatypeDiscr(d_sym, Box::new(t.subst_var(f))),
        }
    }

    pub fn subst_var<F, W>(self, f: F) -> Term<W>
    where
        F: FnMut(V) -> Term<W>,
    {
        self.subst_var_impl::<F, W>(Box::new(f))
    }

    pub fn map_var<F, W>(self, mut f: F) -> Term<W>
    where
        F: FnMut(V) -> W,
    {
        self.subst_var(|v| Term::Var(f(v)))
    }

    fn sort<F>(&self, mut var_sort: F) -> Sort
    where
        F: FnMut(&V) -> Sort,
    {
        match self {
            Term::Null => Sort::null(),
            Term::Var(v) => var_sort(v),
            Term::Bool(_) => Sort::bool(),
            Term::Int(_) => Sort::int(),
            Term::String(_) => Sort::string(),
            Term::Box(t) => Sort::box_(t.sort(var_sort)),
            Term::Mut(t, _) => Sort::mut_(t.sort(var_sort)),
            Term::BoxCurrent(t) => t.sort(var_sort).deref(),
            Term::MutCurrent(t) => t.sort(var_sort).deref(),
            Term::MutFinal(t) => t.sort(var_sort).deref(),
            Term::App(fun, args) => fun.sort(args.iter().map(|t| t.sort(&mut var_sort))),
            Term::Tuple(ts) => {
                // TODO: remove this
                let mut var_sort: Box<dyn FnMut(&V) -> Sort> = Box::new(var_sort);
                Sort::tuple(ts.iter().map(|t| t.sort(&mut var_sort)).collect())
            }
            Term::TupleProj(t, i) => t.sort(var_sort).tuple_elem(*i),
            Term::DatatypeCtor(d_sym, _, _) => Sort::datatype(d_sym.clone()),
            Term::DatatypeDiscr(_, _) => Sort::int(),
        }
    }

    fn fv_impl(&self) -> Box<dyn Iterator<Item = &V> + '_> {
        match self {
            Term::Var(v) => Box::new(std::iter::once(v)),
            Term::Null | Term::Bool(_) | Term::Int(_) | Term::String(_) => {
                Box::new(std::iter::empty())
            }
            Term::Box(t) => t.fv_impl(),
            Term::Mut(t1, t2) => Box::new(t1.fv_impl().chain(t2.fv_impl())),
            Term::BoxCurrent(t) => t.fv_impl(),
            Term::MutCurrent(t) => t.fv_impl(),
            Term::MutFinal(t) => t.fv_impl(),
            Term::App(_, args) => Box::new(args.iter().flat_map(|t| t.fv_impl())),
            Term::Tuple(ts) => Box::new(ts.iter().flat_map(|t| t.fv_impl())),
            Term::TupleProj(t, _) => t.fv_impl(),
            Term::DatatypeCtor(_, _, args) => Box::new(args.iter().flat_map(|t| t.fv_impl())),
            Term::DatatypeDiscr(_, t) => t.fv_impl(),
        }
    }

    pub fn fv(&self) -> impl Iterator<Item = &V> {
        self.fv_impl()
    }

    pub fn null() -> Self {
        Term::Null
    }

    pub fn var(v: V) -> Self {
        Term::Var(v)
    }

    pub fn int(n: i64) -> Self {
        Term::Int(n)
    }

    pub fn bool(b: bool) -> Self {
        Term::Bool(b)
    }

    pub fn string(s: String) -> Self {
        Term::String(s)
    }

    pub fn box_(t: Term<V>) -> Self {
        Term::Box(Box::new(t))
    }

    pub fn mut_(t1: Term<V>, t2: Term<V>) -> Self {
        Term::Mut(Box::new(t1), Box::new(t2))
    }

    pub fn box_current(self) -> Self {
        Term::BoxCurrent(Box::new(self))
    }

    pub fn mut_current(self) -> Self {
        Term::MutCurrent(Box::new(self))
    }

    pub fn mut_final(self) -> Self {
        Term::MutFinal(Box::new(self))
    }

    pub fn add(self, other: Self) -> Self {
        Term::App(Function::ADD, vec![self, other])
    }

    pub fn sub(self, other: Self) -> Self {
        Term::App(Function::SUB, vec![self, other])
    }

    pub fn mul(self, other: Self) -> Self {
        Term::App(Function::MUL, vec![self, other])
    }

    pub fn eq(self, other: Self) -> Self {
        Term::App(Function::EQ, vec![self, other])
    }

    pub fn ne(self, other: Self) -> Self {
        Term::App(
            Function::NOT,
            vec![Term::App(Function::EQ, vec![self, other])],
        )
    }

    pub fn ge(self, other: Self) -> Self {
        Term::App(Function::GE, vec![self, other])
    }

    pub fn gt(self, other: Self) -> Self {
        Term::App(Function::GT, vec![self, other])
    }

    pub fn le(self, other: Self) -> Self {
        Term::App(Function::LE, vec![self, other])
    }

    pub fn lt(self, other: Self) -> Self {
        Term::App(Function::LT, vec![self, other])
    }

    pub fn not(self) -> Self {
        Term::App(Function::NOT, vec![self])
    }

    pub fn neg(self) -> Self {
        Term::App(Function::NEG, vec![self])
    }

    pub fn tuple(ts: Vec<Term<V>>) -> Self {
        Term::Tuple(ts)
    }

    pub fn tuple_proj(self, i: usize) -> Self {
        Term::TupleProj(Box::new(self), i)
    }

    pub fn datatype_ctor(d_sym: DatatypeSymbol, c_sym: DatatypeSymbol, args: Vec<Term<V>>) -> Self {
        Term::DatatypeCtor(d_sym, c_sym, args)
    }

    pub fn datatype_discr(d_sym: DatatypeSymbol, t: Term<V>) -> Self {
        Term::DatatypeDiscr(d_sym, Box::new(t))
    }

    pub fn equal_to(self, other: Self) -> Atom<V> {
        Atom::new(KnownPred::EQUAL.into(), vec![self, other])
    }

    pub fn not_equal_to(self, other: Self) -> Atom<V> {
        Atom::new(KnownPred::NOT_EQUAL.into(), vec![self, other])
    }
}

rustc_index::newtype_index! {
    #[debug_format = "p{}"]
    pub struct PredVarId { }
}

impl std::fmt::Display for PredVarId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "p{}", self.index())
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b PredVarId
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self).annotate(PredVarId::color_spec())
    }
}

impl PredVarId {
    fn color_spec() -> termcolor::ColorSpec {
        let mut spec = termcolor::ColorSpec::new();
        spec.set_fg(Some(termcolor::Color::Cyan));
        spec
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KnownPred {
    name: &'static str,
    is_negative: bool,
    is_infix: bool,
}

impl std::fmt::Display for KnownPred {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.is_negative {
            f.write_str("!")?;
        }
        f.write_str(self.name)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b KnownPred
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self).annotate(KnownPred::color_spec())
    }
}

impl KnownPred {
    fn color_spec() -> termcolor::ColorSpec {
        let mut spec = termcolor::ColorSpec::new();
        spec.set_fg(Some(termcolor::Color::Red));
        spec
    }

    const fn new(name: &'static str) -> Self {
        KnownPred {
            name,
            is_negative: false,
            is_infix: false,
        }
    }

    const fn infix(name: &'static str) -> Self {
        KnownPred {
            name,
            is_negative: false,
            is_infix: true,
        }
    }

    const fn negated(mut self) -> Self {
        self.is_negative = true;
        self
    }

    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn is_negative(&self) -> bool {
        self.is_negative
    }

    pub fn is_infix(&self) -> bool {
        self.is_infix
    }

    pub fn is_top(&self) -> bool {
        self == &KnownPred::TOP
    }

    pub const TOP: KnownPred = KnownPred::new("true");
    pub const BOTTOM: KnownPred = KnownPred::new("false");
    pub const EQUAL: KnownPred = KnownPred::infix("=");
    pub const NOT_EQUAL: KnownPred = KnownPred::infix("=").negated();
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Pred {
    Known(KnownPred),
    Var(PredVarId),
}

impl std::fmt::Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Pred::Known(p) => p.fmt(f),
            Pred::Var(p) => p.fmt(f),
        }
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Pred
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Pred::Known(p) => p.pretty(allocator),
            Pred::Var(p) => p.pretty(allocator),
        }
    }
}

impl From<KnownPred> for Pred {
    fn from(p: KnownPred) -> Pred {
        Pred::Known(p)
    }
}

impl From<PredVarId> for Pred {
    fn from(p: PredVarId) -> Pred {
        Pred::Var(p)
    }
}

impl Pred {
    pub fn name(&self) -> std::borrow::Cow<'static, str> {
        match self {
            Pred::Known(p) => p.name().into(),
            Pred::Var(p) => p.to_string().into(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_negative(),
            Pred::Var(_) => false,
        }
    }

    pub fn is_infix(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_infix(),
            Pred::Var(_) => false,
        }
    }

    pub fn is_top(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_top(),
            Pred::Var(_) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Atom<V = TermVarIdx> {
    pub pred: Pred,
    pub args: Vec<Term<V>>,
}

impl<'a, 'b, D, V> Pretty<'a, D, termcolor::ColorSpec> for &'b Atom<V>
where
    V: Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        if self.pred.is_infix() {
            self.args[0]
                .pretty_atom(allocator)
                .append(allocator.line())
                .append(self.pred.pretty(allocator))
                .append(allocator.line())
                .append(self.args[1].pretty_atom(allocator))
                .group()
        } else {
            let inner = allocator.intersperse(
                self.args.iter().map(|t| t.pretty_atom(allocator)),
                allocator.line(),
            );
            let p = self.pred.pretty(allocator);
            if self.args.is_empty() {
                p
            } else {
                p.append(allocator.line()).append(inner.nest(2)).group()
            }
        }
    }
}

impl<V> Atom<V> {
    pub fn new(pred: Pred, args: Vec<Term<V>>) -> Self {
        Atom { pred, args }
    }

    pub fn top() -> Self {
        Atom {
            pred: KnownPred::TOP.into(),
            args: vec![],
        }
    }

    pub fn bottom() -> Self {
        Atom {
            pred: KnownPred::BOTTOM.into(),
            args: vec![],
        }
    }

    pub fn is_top(&self) -> bool {
        self.pred.is_top()
    }

    pub fn subst_var<F, W>(self, mut f: F) -> Atom<W>
    where
        F: FnMut(V) -> Term<W>,
    {
        Atom {
            pred: self.pred,
            args: self.args.into_iter().map(|t| t.subst_var(&mut f)).collect(),
        }
    }

    pub fn map_var<F, W>(self, mut f: F) -> Atom<W>
    where
        F: FnMut(V) -> W,
    {
        Atom {
            pred: self.pred,
            args: self.args.into_iter().map(|t| t.map_var(|v| f(v))).collect(),
        }
    }

    pub fn fv(&self) -> impl Iterator<Item = &V> {
        self.args.iter().flat_map(|t| t.fv())
    }
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub vars: IndexVec<TermVarIdx, Sort>,
    pub head: Atom<TermVarIdx>,
    pub body: Vec<Atom<TermVarIdx>>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Clause
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let vars = allocator
            .intersperse(
                self.vars
                    .iter_enumerated()
                    .map(|(v, s)| v.pretty(allocator).append(allocator.text(":")).append(s)),
                allocator.text(",").append(allocator.line()),
            )
            .group();
        let body = allocator.intersperse(
            &self.body,
            allocator
                .text("∧")
                .enclose(allocator.line(), allocator.space()),
        );
        let imp = self
            .head
            .pretty(allocator)
            .append(allocator.line())
            .append(allocator.text("⇐"))
            .group()
            .append(allocator.line().append(body).nest(2))
            .group();
        allocator
            .text("∀")
            .append(vars.nest(2))
            .append(allocator.text("."))
            .append(allocator.line().append(imp).nest(2))
            .group()
    }
}

impl Clause {
    fn term_sort(&self, term: &Term<TermVarIdx>) -> Sort {
        term.sort(|v| self.vars[*v].clone())
    }
}

#[derive(Debug, Clone)]
pub struct DatatypeSelector {
    pub symbol: DatatypeSymbol,
    pub sort: Sort,
}

#[derive(Debug, Clone)]
pub struct DatatypeCtor {
    pub symbol: DatatypeSymbol,
    pub selectors: Vec<DatatypeSelector>,
    pub discriminant: u32,
}

#[derive(Debug, Clone)]
pub struct Datatype {
    pub symbol: DatatypeSymbol,
    pub ctors: Vec<DatatypeCtor>,
}

rustc_index::newtype_index! {
    #[debug_format = "c{}"]
    pub struct ClauseId { }
}

pub type PredSig = Vec<Sort>;

#[derive(Debug, Clone, Default)]
pub struct System {
    pub datatypes: Vec<Datatype>,
    pub clauses: IndexVec<ClauseId, Clause>,
    pub pred_vars: IndexVec<PredVarId, PredSig>,
}

impl System {
    pub fn new_pred_var(&mut self, sig: PredSig) -> PredVarId {
        self.pred_vars.push(sig)
    }

    pub fn smtlib2(&self) -> smtlib2::System<'_> {
        smtlib2::System::new(self)
    }

    pub fn solve(&self) -> Result<(), CheckSatError> {
        let system = unbox(self.clone());
        let mut f = std::fs::File::create("refinement-analyzer.txt").unwrap();
        for (idx, c) in system.clauses.iter_enumerated() {
            use crate::pretty::PrettyDisplayExt as _;
            use std::io::Write as _;
            write!(f, "{:?}: {}\n", idx, c.display()).unwrap();
        }
        Config::load_env().check_sat(system.smtlib2())
    }
}
