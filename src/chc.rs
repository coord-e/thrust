//! A multi-sorted CHC system with tuples.

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;

use crate::pretty::PrettyDisplayExt as _;

mod clause_builder;
mod debug;
mod format_context;
mod hoice;
mod smtlib2;
mod solver;
mod unbox;

pub use clause_builder::{ClauseBuilder, Var};
pub use debug::DebugInfo;
pub use solver::{CheckSatError, Config};
pub use unbox::unbox;

/// A name of a datatype.
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

/// A datatype sort.
///
/// A datatype sort is a sort that is defined by a datatype. It has a symbol and a list of
/// argument sorts.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DatatypeSort {
    symbol: DatatypeSymbol,
    args: Vec<Sort>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b DatatypeSort
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let inner = allocator.intersperse(
            self.args.iter().map(|t| t.pretty_atom(allocator)),
            allocator.line(),
        );
        let sym = self.symbol.pretty(allocator);
        if self.args.is_empty() {
            sym
        } else {
            sym.append(allocator.line()).append(inner.nest(2)).group()
        }
    }
}

impl DatatypeSort {
    pub fn new(symbol: DatatypeSymbol, args: Vec<Sort>) -> Self {
        DatatypeSort { symbol, args }
    }
}

/// A sort is the type of a logical term.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    Null,
    Int,
    Bool,
    String,
    Param(usize),
    Box(Box<Sort>),
    Mut(Box<Sort>),
    Tuple(Vec<Sort>),
    Datatype(DatatypeSort),
}

impl From<DatatypeSort> for Sort {
    fn from(sort: DatatypeSort) -> Self {
        Sort::Datatype(sort)
    }
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
            Sort::Param(i) => allocator.text("T").append(allocator.as_string(i)),
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
            Sort::Datatype(sort) => sort.pretty(allocator),
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
            Sort::Box(_) | Sort::Mut(_) | Sort::Datatype { .. } => self.pretty(allocator).parens(),
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
            Sort::Datatype(sort) => {
                for s in &sort.args {
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

    pub fn tuple_elem(self, index: usize) -> Self {
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

    pub fn param(i: usize) -> Self {
        Sort::Param(i)
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

    pub fn datatype(symbol: DatatypeSymbol, args: Vec<Sort>) -> Self {
        Sort::Datatype(DatatypeSort { symbol, args })
    }

    pub fn into_datatype(self) -> Option<DatatypeSort> {
        match self {
            Sort::Datatype(sort) => Some(sort),
            _ => None,
        }
    }

    pub fn as_datatype(&self) -> Option<&DatatypeSort> {
        match self {
            Sort::Datatype(sort) => Some(sort),
            _ => None,
        }
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

    pub fn instantiate_params(&mut self, args: &[Sort]) {
        match self {
            Sort::Param(i) => *self = args[*i].clone(),
            Sort::Box(s) => s.instantiate_params(args),
            Sort::Mut(s) => s.instantiate_params(args),
            Sort::Tuple(ss) => {
                for s in ss {
                    s.instantiate_params(args);
                }
            }
            Sort::Datatype(sort) => {
                for s in &mut sort.args {
                    s.instantiate_params(args);
                }
            }
            _ => {}
        }
    }
}

rustc_index::newtype_index! {
    /// An index representing term-level variable.
    ///
    /// We manage term-level variables using indices that are unique in each clause.
    /// [`Clause`] contains `IndexVec<TermVarIdx, Sort>` that manages the indices and the sorts of the variables.
    #[orderable]
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

/// A known function symbol.
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

/// A logical term.
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
    DatatypeCtor(DatatypeSort, DatatypeSymbol, Vec<Term<V>>),
    DatatypeDiscr(DatatypeSymbol, Box<Term<V>>),
    /// Used in [`Formula`] to represent existentially quantified variables appearing in annotations.
    FormulaExistentialVar(Sort, String),
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
            Term::FormulaExistentialVar(_, name) => allocator.text(name.clone()),
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
    fn subst_var_impl<W>(self, mut f: Box<dyn FnMut(V) -> Term<W> + '_>) -> Term<W> {
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
            Term::DatatypeCtor(sort, c_sym, args) => Term::DatatypeCtor(
                sort,
                c_sym,
                args.into_iter().map(|t| t.subst_var(&mut f)).collect(),
            ),
            Term::DatatypeDiscr(d_sym, t) => Term::DatatypeDiscr(d_sym, Box::new(t.subst_var(f))),
            Term::FormulaExistentialVar(sort, name) => Term::FormulaExistentialVar(sort, name),
        }
    }

    pub fn subst_var<F, W>(self, f: F) -> Term<W>
    where
        F: FnMut(V) -> Term<W>,
    {
        self.subst_var_impl::<W>(Box::new(f))
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
            Term::DatatypeCtor(sort, _, _) => sort.clone().into(),
            Term::DatatypeDiscr(_, _) => Sort::int(),
            Term::FormulaExistentialVar(sort, _) => sort.clone(),
        }
    }

    fn fv_impl(&self) -> Box<dyn Iterator<Item = &V> + '_> {
        match self {
            Term::Var(v) => Box::new(std::iter::once(v)),
            Term::Null
            | Term::Bool(_)
            | Term::Int(_)
            | Term::String(_)
            | Term::FormulaExistentialVar { .. } => Box::new(std::iter::empty()),
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

    pub fn boxed(self) -> Self {
        Term::Box(Box::new(self))
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

    pub fn datatype_ctor(
        d_sym: DatatypeSymbol,
        d_args: Vec<Sort>,
        c_sym: DatatypeSymbol,
        args: Vec<Term<V>>,
    ) -> Self {
        Term::DatatypeCtor(DatatypeSort::new(d_sym, d_args), c_sym, args)
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
    /// An index representing predicate variables.
    ///
    /// We manage predicate variables using indices that are unique in a CHC system.
    /// [`System`] contains `IndexVec<PredVarId, PredVarDef>` that manages the indices
    /// and signatures of the predicate variables.
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

/// A known predicate.
///
/// A known predicate is a predicate that has a fixed meaning, such as `true`, `false`, `=`, etc.
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

    pub fn is_bottom(&self) -> bool {
        self == &KnownPred::BOTTOM
    }

    pub const TOP: KnownPred = KnownPred::new("true");
    pub const BOTTOM: KnownPred = KnownPred::new("false");
    pub const EQUAL: KnownPred = KnownPred::infix("=");
    pub const NOT_EQUAL: KnownPred = KnownPred::infix("=").negated();

    pub const LESS_THAN_OR_EQUAL: KnownPred = KnownPred::infix("<=");
    pub const GREATER_THAN_OR_EQUAL: KnownPred = KnownPred::infix(">=");
    pub const LESS_THAN: KnownPred = KnownPred::infix("<");
    pub const GREATER_THAN: KnownPred = KnownPred::infix(">");
}

/// A matcher predicate.
///
/// A matcher predicate is a predicate that relates a value of a datatype with its contents.
/// For example, given the following `enum` datatype:
///
/// ```rust
/// pub enum X {
///     A(i64),
///     B(bool),
/// }
/// ```
///
/// The corresponding matcher predicate is defined as:
///
/// ```smtlib2
/// (define-fun matcher_pred<X> ((x0 Int) (x1 Bool) (v X)) Bool (or (= v (X.A x0)) (= v (X.B x1))))
/// ```
///
/// See the implementation in the [`smtlib2`] module for the details.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatcherPred {
    datatype_symbol: DatatypeSymbol,
    datatype_args: Vec<Sort>,
}

impl std::fmt::Display for MatcherPred {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "matcher_pred")
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b MatcherPred
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let args = allocator.intersperse(
            self.datatype_args.iter().map(|a| a.pretty(allocator)),
            allocator.text(", "),
        );
        allocator
            .text("matcher_pred")
            .append(
                allocator
                    .as_string(&self.datatype_symbol)
                    .append(args.angles())
                    .angles(),
            )
            .group()
    }
}

impl MatcherPred {
    pub fn new(datatype_symbol: DatatypeSymbol, datatype_args: Vec<Sort>) -> Self {
        MatcherPred {
            datatype_symbol,
            datatype_args,
        }
    }

    pub fn name(&self) -> &'static str {
        "matcher_pred"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UserDefinedPred {
    inner: String,
}

impl std::fmt::Display for UserDefinedPred {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b UserDefinedPred
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.text(self.inner.clone())
    }
}

impl UserDefinedPred {
    pub fn new(inner: String) -> Self {
        Self { inner }
    }
}

/// A predicate.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    Known(KnownPred),
    Var(PredVarId),
    Matcher(MatcherPred),
    UserDefined(UserDefinedPred),
}

impl std::fmt::Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Pred::Known(p) => p.fmt(f),
            Pred::Var(p) => p.fmt(f),
            Pred::Matcher(p) => p.fmt(f),
            Pred::UserDefined(p) => p.fmt(f),
        }
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Pred
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Pred::Known(p) => p.pretty(allocator),
            Pred::Var(p) => p.pretty(allocator),
            Pred::Matcher(p) => p.pretty(allocator),
            Pred::UserDefined(p) => p.pretty(allocator),
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

impl From<MatcherPred> for Pred {
    fn from(p: MatcherPred) -> Pred {
        Pred::Matcher(p)
    }
}

impl From<UserDefinedPred> for Pred {
    fn from(p: UserDefinedPred) -> Pred {
        Pred::UserDefined(p)
    }
}

impl Pred {
    pub fn name(&self) -> std::borrow::Cow<'static, str> {
        match self {
            Pred::Known(p) => p.name().into(),
            Pred::Var(p) => p.to_string().into(),
            Pred::Matcher(p) => p.name().into(),
            Pred::UserDefined(p) => p.to_string().into(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_negative(),
            Pred::Var(_) => false,
            Pred::Matcher(_) => false,
            Pred::UserDefined(_) => false,
        }
    }

    pub fn is_infix(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_infix(),
            Pred::Var(_) => false,
            Pred::Matcher(_) => false,
            Pred::UserDefined(_) => false,
        }
    }

    pub fn is_top(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_top(),
            Pred::Var(_) => false,
            Pred::Matcher(_) => false,
            Pred::UserDefined(_) => false,
        }
    }

    pub fn is_bottom(&self) -> bool {
        match self {
            Pred::Known(p) => p.is_bottom(),
            Pred::Var(_) => false,
            Pred::Matcher(_) => false,
            Pred::UserDefined(_) => false,
        }
    }
}

/// An atom is a predicate applied to a list of terms.
#[derive(Debug, Clone)]
pub struct Atom<V = TermVarIdx> {
    /// With `guard`, this represents `guard => pred(args)`.
    ///
    /// As long as there is no pvar in the `guard`, it forms a valid CHC. However, in that case,
    /// it becomes odd to call this an `Atom`... It is our TODO to clean this up by either
    /// getting rid of the `guard` or renaming `Atom`.
    pub guard: Option<Box<Formula<V>>>,
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
        let guard = if let Some(guard) = &self.guard {
            guard.pretty(allocator).append(allocator.text(" ⇒"))
        } else {
            allocator.nil()
        };
        let atom = if self.pred.is_infix() {
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
        };
        guard.append(allocator.line()).append(atom).group()
    }
}

impl<V> Atom<V> {
    pub fn new(pred: Pred, args: Vec<Term<V>>) -> Self {
        Atom {
            guard: None,
            pred,
            args,
        }
    }

    pub fn with_guard(guard: Formula<V>, pred: Pred, args: Vec<Term<V>>) -> Self {
        Atom {
            guard: Some(Box::new(guard)),
            pred,
            args,
        }
    }

    pub fn top() -> Self {
        Atom::new(KnownPred::TOP.into(), vec![])
    }

    pub fn bottom() -> Self {
        Atom::new(KnownPred::BOTTOM.into(), vec![])
    }

    pub fn is_top(&self) -> bool {
        if let Some(guard) = &self.guard {
            guard.is_bottom() || self.pred.is_top()
        } else {
            self.pred.is_top()
        }
    }

    pub fn is_bottom(&self) -> bool {
        if let Some(guard) = &self.guard {
            guard.is_top() && self.pred.is_bottom()
        } else {
            self.pred.is_bottom()
        }
    }

    pub fn subst_var<F, W>(self, mut f: F) -> Atom<W>
    where
        F: FnMut(V) -> Term<W>,
    {
        Atom {
            guard: self.guard.map(|fo| Box::new(fo.subst_var(&mut f))),
            pred: self.pred,
            args: self.args.into_iter().map(|t| t.subst_var(&mut f)).collect(),
        }
    }

    pub fn map_var<F, W>(self, mut f: F) -> Atom<W>
    where
        F: FnMut(V) -> W,
    {
        Atom {
            guard: self.guard.map(|fo| Box::new(fo.map_var(&mut f))),
            pred: self.pred,
            args: self.args.into_iter().map(|t| t.map_var(&mut f)).collect(),
        }
    }

    pub fn fv(&self) -> impl Iterator<Item = &V> {
        let guard_fvs: Box<dyn Iterator<Item = &V>> = if let Some(guard) = &self.guard {
            Box::new(guard.fv())
        } else {
            Box::new(std::iter::empty())
        };
        self.args.iter().flat_map(|t| t.fv()).chain(guard_fvs)
    }

    pub fn guarded(self, new_guard: Formula<V>) -> Atom<V> {
        let Atom {
            guard: self_guard,
            pred,
            args,
        } = self;
        let guard = if let Some(self_guard) = self_guard {
            self_guard.and(new_guard)
        } else {
            new_guard
        };
        Atom {
            guard: Some(Box::new(guard)),
            pred,
            args,
        }
    }
}

/// An arbitrary formula built with atoms and logical connectives.
///
/// While it allows arbitrary [`Atom`] in its `Atom` variant, we only expect atoms with known
/// predicates (i.e., predicates other than `Pred::Var`) to appear in formulas. It is our TODO to
/// enforce this restriction statically. Also see the definition of [`Body`].
#[derive(Debug, Clone)]
pub enum Formula<V = TermVarIdx> {
    Atom(Atom<V>),
    Not(Box<Formula<V>>),
    And(Vec<Formula<V>>),
    Or(Vec<Formula<V>>),
    Exists(Vec<(String, Sort)>, Box<Formula<V>>),
}

impl<V> Default for Formula<V> {
    fn default() -> Self {
        Formula::top()
    }
}

impl<V> From<Atom<V>> for Formula<V> {
    fn from(atom: Atom<V>) -> Formula<V> {
        Formula::Atom(atom)
    }
}

impl<'a, 'b, D, V> Pretty<'a, D, termcolor::ColorSpec> for &'b Formula<V>
where
    V: Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Formula::Atom(atom) => atom.pretty(allocator),
            Formula::Not(fo) => allocator
                .text("¬")
                .append(fo.pretty_atom(allocator))
                .group(),
            Formula::And(fs) => {
                let inner = allocator.intersperse(
                    fs.iter().map(|f| f.pretty_atom(allocator)),
                    allocator.text("∧").append(allocator.line()),
                );
                inner.group()
            }
            Formula::Or(fs) => {
                let inner = allocator.intersperse(
                    fs.iter().map(|f| f.pretty_atom(allocator)),
                    allocator.text("∨").append(allocator.line()),
                );
                inner.group()
            }
            Formula::Exists(vars, fo) => {
                let vars = allocator.intersperse(
                    vars.iter().map(|(name, sort)| {
                        allocator
                            .text(name.clone())
                            .append(allocator.text(":"))
                            .append(allocator.text(" "))
                            .append(sort.pretty(allocator))
                    }),
                    allocator.text(", ").append(allocator.line()),
                );
                allocator
                    .text("∃")
                    .append(vars)
                    .append(allocator.text("."))
                    .append(allocator.line())
                    .append(fo.pretty(allocator).nest(2))
                    .group()
            }
        }
    }
}

impl<V> Formula<V> {
    fn pretty_atom<'a, 'b, D>(
        &'b self,
        allocator: &'a D,
    ) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec>
    where
        V: Var,
        D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        match self {
            Formula::And(_) | Formula::Or(_) | Formula::Exists { .. } => {
                self.pretty(allocator).parens()
            }
            _ => self.pretty(allocator),
        }
    }

    pub fn top() -> Self {
        Formula::Atom(Atom::top())
    }

    pub fn bottom() -> Self {
        Formula::Atom(Atom::bottom())
    }

    pub fn is_top(&self) -> bool {
        match self {
            Formula::Atom(atom) => atom.is_top(),
            Formula::Not(fo) => fo.is_bottom(),
            Formula::And(fs) => fs.iter().all(Formula::is_top),
            Formula::Or(fs) => fs.iter().any(Formula::is_top),
            Formula::Exists(_, fo) => fo.is_top(),
        }
    }

    pub fn is_bottom(&self) -> bool {
        match self {
            Formula::Atom(atom) => atom.is_bottom(),
            Formula::Not(fo) => fo.is_top(),
            Formula::And(fs) => fs.iter().any(Formula::is_bottom),
            Formula::Or(fs) => fs.iter().all(Formula::is_bottom),
            Formula::Exists(_, fo) => fo.is_bottom(),
        }
    }

    pub fn not(self) -> Self {
        match self {
            Formula::Not(fo) => *fo,
            _ => Formula::Not(Box::new(self)),
        }
    }

    pub fn and(self, other: Self) -> Self {
        match (self, other) {
            (Formula::And(mut fs), Formula::And(others)) => {
                fs.extend(others);
                Formula::And(fs)
            }
            (f1, f2) => Formula::And(vec![f1, f2]),
        }
    }

    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (Formula::Or(mut fs), Formula::Or(others)) => {
                fs.extend(others);
                Formula::Or(fs)
            }
            (f1, f2) => Formula::Or(vec![f1, f2]),
        }
    }

    pub fn exists(vars: Vec<(String, Sort)>, body: Self) -> Self {
        Formula::Exists(vars, Box::new(body))
    }

    pub fn subst_var<F, W>(self, f: F) -> Formula<W>
    where
        F: FnMut(V) -> Term<W>,
    {
        // TODO: remove this
        let mut f: Box<dyn FnMut(V) -> Term<W>> = Box::new(f);
        match self {
            Formula::Atom(atom) => Formula::Atom(atom.subst_var(f)),
            Formula::Not(fo) => Formula::Not(Box::new(fo.subst_var(f))),
            Formula::And(fs) => {
                Formula::And(fs.into_iter().map(|fo| fo.subst_var(&mut f)).collect())
            }
            Formula::Or(fs) => Formula::Or(fs.into_iter().map(|fo| fo.subst_var(&mut f)).collect()),
            Formula::Exists(vars, fo) => Formula::Exists(vars, Box::new(fo.subst_var(f))),
        }
    }

    pub fn map_var<F, W>(self, f: F) -> Formula<W>
    where
        F: FnMut(V) -> W,
    {
        // TODO: remove this
        let mut f: Box<dyn FnMut(V) -> W> = Box::new(f);
        match self {
            Formula::Atom(atom) => Formula::Atom(atom.map_var(f)),
            Formula::Not(fo) => Formula::Not(Box::new(fo.map_var(&mut f))),
            Formula::And(fs) => Formula::And(fs.into_iter().map(|fo| fo.map_var(&mut f)).collect()),
            Formula::Or(fs) => Formula::Or(fs.into_iter().map(|fo| fo.map_var(&mut f)).collect()),
            Formula::Exists(vars, fo) => Formula::Exists(vars, Box::new(fo.map_var(f))),
        }
    }

    pub fn fv(&self) -> impl Iterator<Item = &V> {
        self.fv_impl()
    }

    fn fv_impl(&self) -> Box<dyn Iterator<Item = &V> + '_> {
        match self {
            Formula::Atom(atom) => Box::new(atom.fv()),
            Formula::Not(fo) => Box::new(fo.fv()),
            Formula::And(fs) => Box::new(fs.iter().flat_map(Formula::fv)),
            Formula::Or(fs) => Box::new(fs.iter().flat_map(Formula::fv)),
            Formula::Exists(_, fo) => Box::new(fo.fv()),
        }
    }

    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom<V>> {
        self.iter_atoms_impl()
    }

    fn iter_atoms_impl(&self) -> Box<dyn Iterator<Item = &Atom<V>> + '_> {
        match self {
            Formula::Atom(atom) => Box::new(std::iter::once(atom)),
            Formula::Not(fo) => Box::new(fo.iter_atoms()),
            Formula::And(fs) => Box::new(fs.iter().flat_map(Formula::iter_atoms)),
            Formula::Or(fs) => Box::new(fs.iter().flat_map(Formula::iter_atoms)),
            Formula::Exists(_, fo) => Box::new(fo.iter_atoms()),
        }
    }

    pub fn push_conj(&mut self, other: Self) {
        match self {
            Formula::And(fs) => {
                fs.push(other);
            }
            _ => {
                let orig = std::mem::take(self);
                *self = Formula::And(vec![orig, other]);
            }
        }
    }

    pub fn simplify(&mut self) {
        match self {
            Formula::Atom(_atom) => {}
            Formula::Not(fo) => fo.simplify(),
            Formula::And(fs) => {
                for fo in &mut *fs {
                    fo.simplify();
                }
                fs.retain(|f| !f.is_top());
                if fs.is_empty() {
                    *self = Formula::top();
                } else if fs.len() == 1 {
                    *self = fs.pop().unwrap();
                }
            }
            Formula::Or(fs) => {
                for fo in &mut *fs {
                    fo.simplify();
                }
                fs.retain(|f| !f.is_bottom());
                if fs.is_empty() {
                    *self = Formula::bottom();
                } else if fs.len() == 1 {
                    *self = fs.pop().unwrap();
                }
            }
            Formula::Exists(_, fo) => {
                fo.simplify();
            }
        }
    }
}

/// The body part of a clause, consisting of atoms and a formula.
#[derive(Debug, Clone)]
pub struct Body<V = TermVarIdx> {
    pub atoms: Vec<Atom<V>>,
    /// NOTE: This doesn't contain predicate variables. Also see [`Formula`].
    pub formula: Formula<V>,
}

impl<V> Default for Body<V> {
    fn default() -> Self {
        Body {
            atoms: Default::default(),
            formula: Default::default(),
        }
    }
}

impl<V> From<Atom<V>> for Body<V> {
    fn from(atom: Atom<V>) -> Self {
        Body {
            atoms: vec![atom],
            formula: Formula::top(),
        }
    }
}

impl<V> From<Vec<Atom<V>>> for Body<V> {
    fn from(atoms: Vec<Atom<V>>) -> Self {
        Body {
            atoms,
            formula: Formula::top(),
        }
    }
}

impl<V> From<Formula<V>> for Body<V> {
    fn from(formula: Formula<V>) -> Self {
        Body {
            atoms: vec![],
            formula,
        }
    }
}

impl<V> Body<V> {
    pub fn new(atoms: Vec<Atom<V>>, formula: Formula<V>) -> Self {
        Body { atoms, formula }
    }

    pub fn top() -> Self {
        Body {
            atoms: vec![],
            formula: Formula::top(),
        }
    }

    pub fn bottom() -> Self {
        Body {
            atoms: vec![],
            formula: Formula::bottom(),
        }
    }

    pub fn is_top(&self) -> bool {
        self.formula.is_top() && self.atoms.iter().all(|a| a.is_top())
    }

    pub fn is_bottom(&self) -> bool {
        self.formula.is_bottom() || self.atoms.iter().any(|a| a.is_bottom())
    }

    pub fn push_conj(&mut self, other: impl Into<Body<V>>) {
        let Body { atoms, formula } = other.into();
        self.atoms.extend(atoms);
        self.formula.push_conj(formula);
    }

    pub fn map_var<F, W>(self, mut f: F) -> Body<W>
    where
        F: FnMut(V) -> W,
    {
        Body {
            atoms: self.atoms.into_iter().map(|a| a.map_var(&mut f)).collect(),
            formula: self.formula.map_var(f),
        }
    }

    pub fn subst_var<F, W>(self, mut f: F) -> Body<W>
    where
        F: FnMut(V) -> Term<W>,
    {
        Body {
            atoms: self
                .atoms
                .into_iter()
                .map(|a| a.subst_var(&mut f))
                .collect(),
            formula: self.formula.subst_var(f),
        }
    }

    pub fn simplify(&mut self) {
        self.formula.simplify();
        self.atoms.retain(|a| !a.is_top());
        if self.is_bottom() {
            self.atoms = vec![Atom::bottom()];
            self.formula = Formula::top();
        }
    }

    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom<V>> {
        self.formula.iter_atoms().chain(&self.atoms)
    }
}

impl<V> Body<V>
where
    V: Var,
{
    pub fn guarded(self, guard: Formula<V>) -> Body<V> {
        let Body { atoms, formula } = self;
        Body {
            atoms: atoms
                .into_iter()
                .map(|a| a.guarded(guard.clone()))
                .collect(),
            formula: guard.not().or(formula),
        }
    }
}

impl<'a, 'b, D, V> Pretty<'a, D, termcolor::ColorSpec> for &'b Body<V>
where
    V: Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let atoms = allocator.intersperse(
            &self.atoms,
            allocator
                .text("∧")
                .enclose(allocator.line(), allocator.space()),
        );
        let formula = self.formula.pretty(allocator);
        if self.atoms.is_empty() {
            formula
        } else if self.formula.is_top() {
            atoms.group()
        } else {
            atoms
                .append(allocator.line())
                .append(allocator.text("∧"))
                .append(allocator.line())
                .append(formula)
                .group()
        }
    }
}

/// A constrained Horn clause.
///
/// A constrained Horn clause is a formula of the form `∀vars. body ⇒ head` where `body` is a conjunction of
/// atoms and underlying logical formula, and `head` is an atom.
#[derive(Debug, Clone)]
pub struct Clause {
    pub vars: IndexVec<TermVarIdx, Sort>,
    pub head: Atom<TermVarIdx>,
    pub body: Body<TermVarIdx>,
    pub debug_info: DebugInfo,
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
        let body = self.body.pretty(allocator);
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
    pub fn is_nop(&self) -> bool {
        self.head.is_top() || self.body.is_bottom()
    }

    fn term_sort(&self, term: &Term<TermVarIdx>) -> Sort {
        term.sort(|v| self.vars[*v].clone())
    }
}

/// A command specified using `thrust::raw_command` attribute
///
/// Those will be directly inserted into the generated SMT-LIB2 file.
#[derive(Debug, Clone)]
pub struct RawCommand {
    pub command: String,
}

/// A selector for a datatype constructor.
///
/// A selector is a function that extracts a field from a datatype value.
/// Through currently we don't use selectors to access datatype fields in [`Term`]s,
/// we require the symbol as selector name to emit SMT-LIB2 representation of datatypes.
#[derive(Debug, Clone)]
pub struct DatatypeSelector {
    pub symbol: DatatypeSymbol,
    pub sort: Sort,
}

/// A datatype constructor.
#[derive(Debug, Clone)]
pub struct DatatypeCtor {
    pub symbol: DatatypeSymbol,
    pub selectors: Vec<DatatypeSelector>,
    pub discriminant: u32,
}

/// A datatype definition.
#[derive(Debug, Clone)]
pub struct Datatype {
    pub symbol: DatatypeSymbol,
    pub params: usize,
    pub ctors: Vec<DatatypeCtor>,
}

rustc_index::newtype_index! {
    /// An index of [`Clause`].
    ///
    /// [`System`] contains `IndexVec<ClauseId, Clause>` that manages the indices and the clauses.
    #[debug_format = "c{}"]
    pub struct ClauseId { }
}

pub type PredSig = Vec<Sort>;

/// A predicate variable definition.
#[derive(Debug, Clone)]
pub struct PredVarDef {
    pub sig: PredSig,
    /// We may attach a debug information to include in the resulting SMT-LIB2 file to indicate the
    /// origin of predicate variables.
    pub debug_info: DebugInfo,
}

/// A CHC system.
#[derive(Debug, Clone, Default)]
pub struct System {
    pub raw_commands: Vec<RawCommand>,
    pub datatypes: Vec<Datatype>,
    pub clauses: IndexVec<ClauseId, Clause>,
    pub pred_vars: IndexVec<PredVarId, PredVarDef>,
}

impl System {
    pub fn new_pred_var(&mut self, sig: PredSig, debug_info: DebugInfo) -> PredVarId {
        self.pred_vars.push(PredVarDef { sig, debug_info })
    }

    pub fn push_raw_command(&mut self, raw_command: RawCommand) {
        self.raw_commands.push(raw_command)
    }

    pub fn push_clause(&mut self, clause: Clause) -> Option<ClauseId> {
        if clause.is_nop() {
            return None;
        }
        tracing::debug!(clause = %clause.display(), id = ?self.clauses.next_index(), "push_clause");
        Some(self.clauses.push(clause))
    }

    pub fn smtlib2(&self) -> smtlib2::System<'_> {
        smtlib2::System::new(self)
    }

    /// Solves the CHC using an external SMT solver.
    ///
    /// This method first performs some optimization of the CHC,
    /// then formats it to SMT-LIB2, and finally calls the configured CHC solver.
    /// The solver and its arguments can be configured using environment
    /// variables
    /// (see <https://github.com/coord-e/thrust?tab=readme-ov-file#configuration>).
    pub fn solve(&self) -> Result<(), CheckSatError> {
        let system = unbox(self.clone());
        if let Ok(file) = std::env::var("THRUST_PRETTY_OUTPUT") {
            let mut f = std::fs::File::create(file).unwrap();
            for (idx, c) in system.clauses.iter_enumerated() {
                use crate::pretty::PrettyDisplayExt as _;
                use std::io::Write as _;
                writeln!(f, "{:?}: {}", idx, c.display()).unwrap();
            }
        }
        Config::from_env().check_sat(system.smtlib2())
    }
}
