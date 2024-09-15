use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;

use crate::chc;

mod template;
pub use template::{Template, TemplateBuilder};

mod clause_builder;
pub use clause_builder::ClauseBuilderExt;

rustc_index::newtype_index! {
    #[debug_format = "${}"]
    pub struct FunctionParamIdx { }
}

impl std::fmt::Display for FunctionParamIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "${}", self.index())
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b FunctionParamIdx
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self)
    }
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub params: IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
    pub ret: Box<RefinedType<FunctionParamIdx>>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b FunctionType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        allocator
            .intersperse(self.params.iter().map(|ty| ty.pretty(allocator)), separator)
            .parens()
            .append(allocator.space())
            .append(allocator.text("→"))
            .append(allocator.line())
            .append(self.ret.pretty(allocator))
            .group()
    }
}

impl FunctionType {
    pub fn new(
        params: IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
        ret: RefinedType<FunctionParamIdx>,
    ) -> Self {
        FunctionType {
            params,
            ret: Box::new(ret),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefKind {
    Mut,
    Immut,
}

impl std::fmt::Display for RefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RefKind::Mut => f.write_str("mut"),
            RefKind::Immut => f.write_str("immut"),
        }
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b RefKind
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerKind {
    Ref(RefKind),
    Own,
}

impl std::fmt::Display for PointerKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            PointerKind::Own => f.write_str("own"),
            PointerKind::Ref(m) => write!(f, "&{}", m),
        }
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b PointerKind
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self)
    }
}

impl From<RefKind> for PointerKind {
    fn from(kind: RefKind) -> PointerKind {
        PointerKind::Ref(kind)
    }
}

impl PointerKind {
    pub fn deref_term<V>(self, term: chc::Term<V>) -> chc::Term<V> {
        match self {
            PointerKind::Own | PointerKind::Ref(RefKind::Immut) => term.box_current(),
            PointerKind::Ref(RefKind::Mut) => term.mut_current(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PointerType {
    pub kind: PointerKind,
    pub elem: Box<Type>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b PointerType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        self.kind
            .pretty(allocator)
            .append(allocator.space())
            .append(self.elem.pretty_atom(allocator))
    }
}

impl PointerType {
    pub fn mut_to(ty: Type) -> Self {
        PointerType {
            kind: PointerKind::Ref(RefKind::Mut),
            elem: Box::new(ty),
        }
    }

    pub fn immut_to(ty: Type) -> Self {
        PointerType {
            kind: PointerKind::Ref(RefKind::Immut),
            elem: Box::new(ty),
        }
    }

    pub fn is_mut(&self) -> bool {
        match self.kind {
            PointerKind::Ref(RefKind::Mut) => true,
            _ => false,
        }
    }

    pub fn is_own(&self) -> bool {
        match self.kind {
            PointerKind::Own => true,
            _ => false,
        }
    }

    pub fn own(ty: Type) -> Self {
        PointerType {
            kind: PointerKind::Own,
            elem: Box::new(ty),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TupleType {
    pub elems: Vec<Type>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b TupleType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        if self.elems.len() == 1 {
            self.elems[0].pretty(allocator).append(separator).parens()
        } else {
            allocator
                .intersperse(self.elems.iter().map(|s| s.pretty(allocator)), separator)
                .parens()
        }
    }
}

impl TupleType {
    pub fn new(elems: Vec<Type>) -> Self {
        TupleType { elems }
    }

    pub fn unit() -> Self {
        TupleType::new(vec![])
    }

    pub fn is_unit(&self) -> bool {
        self.elems.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumType {
    pub symbol: chc::DatatypeSymbol,
}

impl EnumType {
    pub fn new(symbol: chc::DatatypeSymbol) -> Self {
        EnumType { symbol }
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
    String,
    Never,
    Pointer(PointerType),
    Function(FunctionType),
    Tuple(TupleType),
    Enum(EnumType),
}

impl From<FunctionType> for Type {
    fn from(t: FunctionType) -> Type {
        Type::Function(t)
    }
}

impl From<PointerType> for Type {
    fn from(t: PointerType) -> Type {
        Type::Pointer(t)
    }
}

impl From<TupleType> for Type {
    fn from(t: TupleType) -> Type {
        Type::Tuple(t)
    }
}

impl From<EnumType> for Type {
    fn from(t: EnumType) -> Type {
        Type::Enum(t)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Type
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Type::Int => allocator.text("int"),
            Type::Bool => allocator.text("bool"),
            Type::String => allocator.text("string"),
            Type::Never => allocator.text("!"),
            Type::Pointer(ty) => ty.pretty(allocator),
            Type::Function(ty) => ty.pretty(allocator),
            Type::Tuple(ty) => ty.pretty(allocator),
            Type::Enum(ty) => ty.symbol.pretty(allocator),
        }
    }
}

impl Type {
    fn pretty_atom<'a, D>(
        &self,
        allocator: &'a D,
    ) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec>
    where
        D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        match self {
            Type::Function { .. } | Type::Pointer { .. } => self.pretty(allocator).parens(),
            _ => self.pretty(allocator),
        }
    }

    pub fn unit() -> Self {
        Type::Tuple(TupleType::unit())
    }

    pub fn int() -> Self {
        Type::Int
    }

    pub fn bool() -> Self {
        Type::Bool
    }

    pub fn string() -> Self {
        Type::String
    }

    pub fn never() -> Self {
        Type::Never
    }

    pub fn function(ty: FunctionType) -> Self {
        Type::Function(ty)
    }

    pub fn deref(self) -> Type {
        if let Type::Pointer(ty) = self {
            *ty.elem
        } else {
            panic!("invalid deref");
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Type::Tuple(ty) if ty.is_unit())
    }

    pub fn as_function(&self) -> Option<&FunctionType> {
        match self {
            Type::Function(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn as_enum(&self) -> Option<&EnumType> {
        match self {
            Type::Enum(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn into_pointer(self) -> Option<PointerType> {
        match self {
            Type::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn into_tuple(self) -> Option<TupleType> {
        match self {
            Type::Tuple(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn is_mut(&self) -> bool {
        match self {
            Type::Pointer(ty) => ty.is_mut(),
            _ => false,
        }
    }

    pub fn is_own(&self) -> bool {
        match self {
            Type::Pointer(ty) => ty.is_own(),
            _ => false,
        }
    }

    pub fn to_sort(&self) -> chc::Sort {
        match self {
            Type::Int => chc::Sort::int(),
            Type::Bool => chc::Sort::bool(),
            // TODO: enable string reasoning
            //       currently String sort seems not available in HORN logic of Z3
            Type::String => chc::Sort::null(),
            Type::Never => chc::Sort::null(),
            Type::Pointer(ty) => {
                let elem_sort = ty.elem.to_sort();
                let sort = match ty.kind {
                    PointerKind::Ref(RefKind::Immut) | PointerKind::Own => {
                        chc::Sort::box_(elem_sort)
                    }
                    PointerKind::Ref(RefKind::Mut) => chc::Sort::mut_(elem_sort),
                };
                sort
            }
            Type::Function { .. } => chc::Sort::null(),
            Type::Tuple(ty) => {
                let elem_sorts = ty.elems.iter().map(|ty| ty.to_sort()).collect();
                chc::Sort::tuple(elem_sorts)
            }
            Type::Enum(ty) => chc::Sort::datatype(ty.symbol.clone()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Closed {}

impl std::fmt::Display for Closed {
    fn fmt(&self, _f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {}
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Closed
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, _allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match *self {}
    }
}

rustc_index::newtype_index! {
    #[debug_format = "e{}"]
    pub struct ExistentialVarIdx { }
}

impl std::fmt::Display for ExistentialVarIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "e{}", self.index())
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b ExistentialVarIdx
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefinedTypeVar<FV> {
    Value,
    Existential(ExistentialVarIdx),
    Free(FV),
}

impl<T> From<ExistentialVarIdx> for RefinedTypeVar<T> {
    fn from(v: ExistentialVarIdx) -> Self {
        RefinedTypeVar::Existential(v)
    }
}

impl<FV> std::fmt::Display for RefinedTypeVar<FV>
where
    FV: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RefinedTypeVar::Value => f.write_str("ν"),
            RefinedTypeVar::Existential(v) => v.fmt(f),
            RefinedTypeVar::Free(v) => v.fmt(f),
        }
    }
}

impl<'a, 'b, D, FV> Pretty<'a, D, termcolor::ColorSpec> for &'b RefinedTypeVar<FV>
where
    &'b FV: Pretty<'a, D, termcolor::ColorSpec>,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            RefinedTypeVar::Value => allocator.text("ν"),
            RefinedTypeVar::Existential(v) => v.pretty(allocator),
            RefinedTypeVar::Free(v) => v.pretty(allocator),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Refinement<FV = Closed> {
    pub existentials: IndexVec<ExistentialVarIdx, chc::Sort>,
    pub atoms: Vec<chc::Atom<RefinedTypeVar<FV>>>,
}

impl<FV> From<chc::Atom<RefinedTypeVar<FV>>> for Refinement<FV> {
    fn from(atom: chc::Atom<RefinedTypeVar<FV>>) -> Self {
        Refinement {
            existentials: IndexVec::new(),
            atoms: vec![atom],
        }
    }
}

impl<'a, 'b, D, FV> Pretty<'a, D, termcolor::ColorSpec> for &'b Refinement<FV>
where
    &'b FV: Pretty<'a, D, termcolor::ColorSpec>,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let existentials = allocator
            .intersperse(
                self.existentials
                    .iter_enumerated()
                    .map(|(v, s)| v.pretty(allocator).append(allocator.text(":")).append(s)),
                allocator.text(",").append(allocator.line()),
            )
            .group();
        let atoms = allocator.intersperse(
            &self.atoms,
            allocator
                .text("∧")
                .enclose(allocator.line(), allocator.space()),
        );
        if self.existentials.is_empty() {
            atoms
        } else {
            allocator
                .text("∃")
                .append(existentials.nest(2))
                .append(allocator.text("."))
                .append(allocator.line().append(atoms).nest(2))
                .group()
        }
    }
}

impl<FV> Refinement<FV> {
    pub fn new(
        existentials: IndexVec<ExistentialVarIdx, chc::Sort>,
        atoms: Vec<chc::Atom<RefinedTypeVar<FV>>>,
    ) -> Self {
        Refinement {
            existentials,
            atoms,
        }
    }

    pub fn has_existentials(&self) -> bool {
        !self.existentials.is_empty()
    }

    pub fn existentials(&self) -> impl Iterator<Item = (ExistentialVarIdx, &chc::Sort)> + '_ {
        self.existentials.iter_enumerated()
    }

    pub fn is_top(&self) -> bool {
        self.atoms.iter().all(|a| a.is_top())
    }

    pub fn top() -> Self {
        chc::Atom::top().into()
    }

    pub fn bottom() -> Self {
        chc::Atom::bottom().into()
    }

    pub fn subst_var<F, W>(self, mut f: F) -> Refinement<W>
    where
        F: FnMut(FV) -> chc::Term<W>,
    {
        Refinement {
            existentials: self.existentials,
            atoms: self
                .atoms
                .into_iter()
                .map(|a| {
                    a.subst_var(|v| match v {
                        RefinedTypeVar::Value => chc::Term::var(RefinedTypeVar::Value),
                        RefinedTypeVar::Existential(v) => {
                            chc::Term::var(RefinedTypeVar::Existential(v))
                        }
                        RefinedTypeVar::Free(v) => f(v).map_var(RefinedTypeVar::Free),
                    })
                })
                .collect(),
        }
    }

    pub fn subst_value_var<F>(self, mut f: F) -> Self
    where
        F: FnMut() -> chc::Term<RefinedTypeVar<FV>>,
    {
        Refinement {
            existentials: self.existentials,
            atoms: self
                .atoms
                .into_iter()
                .map(|a| {
                    a.subst_var(|v| match v {
                        RefinedTypeVar::Value => f(),
                        RefinedTypeVar::Existential(v) => {
                            chc::Term::var(RefinedTypeVar::Existential(v))
                        }
                        RefinedTypeVar::Free(v) => chc::Term::var(RefinedTypeVar::Free(v)),
                    })
                })
                .collect(),
        }
    }

    pub fn map_var<F, W>(self, mut f: F) -> Refinement<W>
    where
        F: FnMut(FV) -> W,
    {
        Refinement {
            existentials: self.existentials,
            atoms: self
                .atoms
                .into_iter()
                .map(|a| {
                    a.map_var(|v| match v {
                        RefinedTypeVar::Value => RefinedTypeVar::Value,
                        RefinedTypeVar::Existential(v) => RefinedTypeVar::Existential(v),
                        RefinedTypeVar::Free(v) => RefinedTypeVar::Free(f(v)),
                    })
                })
                .collect(),
        }
    }

    pub fn instantiate(self) -> Instantiator<FV> {
        Instantiator {
            value_var: None,
            existentials: HashMap::new(),
            refinement: self,
        }
    }

    fn into_free_atoms<F, T>(self, mut f: F) -> impl Iterator<Item = chc::Atom<T>>
    where
        F: FnMut(RefinedTypeVar<FV>) -> T,
    {
        self.atoms.into_iter().map(move |a| a.map_var(&mut f))
    }
}

#[derive(Debug, Clone)]
pub struct Instantiator<T> {
    value_var: Option<T>,
    existentials: HashMap<ExistentialVarIdx, T>,
    refinement: Refinement<T>,
}

impl<T> Instantiator<T> {
    pub fn value_var(&mut self, value_var: T) -> &mut Self {
        self.value_var = Some(value_var);
        self
    }

    pub fn existential(&mut self, v: ExistentialVarIdx, value: T) -> &mut Self {
        self.existentials.insert(v, value);
        self
    }

    pub fn into_atoms(self) -> impl Iterator<Item = chc::Atom<T>>
    where
        T: Clone,
    {
        let Instantiator {
            value_var,
            existentials,
            refinement,
        } = self;
        refinement.into_free_atoms(move |v| match v {
            RefinedTypeVar::Value => value_var.clone().unwrap(),
            RefinedTypeVar::Existential(v) => existentials[&v].clone(),
            RefinedTypeVar::Free(v) => v,
        })
    }
}

#[derive(Debug, Clone)]
pub struct RefinedType<FV = Closed> {
    pub ty: Type,
    pub refinement: Refinement<FV>,
}

impl<'a, 'b, D, FV> Pretty<'a, D, termcolor::ColorSpec> for &'b RefinedType<FV>
where
    &'b FV: Pretty<'a, D, termcolor::ColorSpec>,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        if self.refinement.is_top() {
            self.ty.pretty(allocator)
        } else {
            allocator
                .space()
                .append(&self.ty)
                .append(allocator.line())
                .append(allocator.text("|"))
                .append(allocator.space())
                .append(self.refinement.pretty(allocator))
                .append(allocator.line())
                .braces()
                .group()
        }
    }
}

impl<FV> RefinedType<FV> {
    pub fn new(ty: Type, refinement: Refinement<FV>) -> Self {
        RefinedType { ty, refinement }
    }

    pub fn refined_with_term(ty: Type, term: chc::Term<FV>) -> Self {
        let term = term.map_var(RefinedTypeVar::Free);
        let refinement = chc::Term::var(RefinedTypeVar::Value).equal_to(term);
        RefinedType::new(ty, refinement.into())
    }

    pub fn subst_var<F, W>(self, f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> chc::Term<W>,
    {
        RefinedType {
            ty: self.ty,
            refinement: self.refinement.subst_var(f),
        }
    }

    pub fn map_var<F, W>(self, f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> W,
    {
        RefinedType {
            ty: self.ty,
            refinement: self.refinement.map_var(f),
        }
    }

    pub fn is_refined(&self) -> bool {
        !self.refinement.is_top()
    }

    pub fn unrefined(ty: Type) -> Self {
        RefinedType::new(ty, chc::Atom::top().into())
    }
}

impl RefinedType<Closed> {
    pub fn vacuous<FV>(self) -> RefinedType<FV> {
        self.map_var(|v| match v {})
    }
}
