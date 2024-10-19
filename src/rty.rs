use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_target::abi::VariantIdx;

use crate::chc;

mod template;
pub use template::{Template, TemplateBuilder};

mod clause_builder;
pub use clause_builder::ClauseBuilderExt;

mod subtyping;
pub use subtyping::{relate_sub_closed_type, ClauseScope, Subtyping};

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

    pub fn into_closed_ty(self) -> Type<Closed> {
        Type::Function(self)
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
pub struct PointerType<T> {
    pub kind: PointerKind,
    pub elem: Box<RefinedType<T>>,
}

impl<'a, 'b, T, D> Pretty<'a, D, termcolor::ColorSpec> for &'b PointerType<T>
where
    T: chc::Var,
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

impl<T> PointerType<T> {
    pub fn mut_to(ty: Type<T>) -> Self {
        PointerType {
            kind: PointerKind::Ref(RefKind::Mut),
            elem: Box::new(RefinedType::unrefined(ty)),
        }
    }

    pub fn immut_to(ty: Type<T>) -> Self {
        PointerType {
            kind: PointerKind::Ref(RefKind::Immut),
            elem: Box::new(RefinedType::unrefined(ty)),
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

    pub fn own(ty: Type<T>) -> Self {
        PointerType {
            kind: PointerKind::Own,
            elem: Box::new(RefinedType::unrefined(ty)),
        }
    }

    pub fn subst_var<F, U>(self, f: F) -> PointerType<U>
    where
        F: FnMut(T) -> chc::Term<U>,
    {
        PointerType {
            kind: self.kind,
            elem: Box::new(self.elem.subst_var(f)),
        }
    }

    pub fn map_var<F, U>(self, f: F) -> PointerType<U>
    where
        F: FnMut(T) -> U,
    {
        PointerType {
            kind: self.kind,
            elem: Box::new(self.elem.map_var(f)),
        }
    }

    pub fn strip_refinement(self) -> PointerType<Closed> {
        PointerType {
            kind: self.kind,
            elem: Box::new(RefinedType::unrefined(self.elem.strip_refinement())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TupleType<T> {
    pub elems: Vec<RefinedType<T>>,
}

impl<'a, 'b, T, D> Pretty<'a, D, termcolor::ColorSpec> for &'b TupleType<T>
where
    T: chc::Var,
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

impl<T> TupleType<T> {
    pub fn new(elems: Vec<Type<T>>) -> Self {
        TupleType {
            elems: elems.into_iter().map(RefinedType::unrefined).collect(),
        }
    }

    pub fn unit() -> Self {
        TupleType::new(vec![])
    }

    pub fn is_unit(&self) -> bool {
        self.elems.is_empty()
    }

    pub fn subst_var<F, U>(self, mut f: F) -> TupleType<U>
    where
        F: FnMut(T) -> chc::Term<U>,
    {
        TupleType {
            elems: self
                .elems
                .into_iter()
                .map(|ty| ty.subst_var(&mut f))
                .collect(),
        }
    }

    pub fn map_var<F, U>(self, mut f: F) -> TupleType<U>
    where
        F: FnMut(T) -> U,
    {
        TupleType {
            elems: self
                .elems
                .into_iter()
                .map(|ty| ty.map_var(&mut f))
                .collect(),
        }
    }

    pub fn strip_refinement(self) -> TupleType<Closed> {
        TupleType {
            elems: self
                .elems
                .into_iter()
                .map(|ty| RefinedType::unrefined(ty.strip_refinement()))
                .collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct EnumVariantDef {
    pub name: chc::DatatypeSymbol,
    pub discr: u32,
    pub ty: Type<Closed>,
}

#[derive(Debug, Clone)]
pub struct EnumDatatypeDef {
    pub name: chc::DatatypeSymbol,
    pub variants: IndexVec<VariantIdx, EnumVariantDef>,

    // A predicate variable p with the following implications:
    // p(v1, v2, ..., vn, x) <= x = V1(v1)
    // p(v1, v2, ..., vn, x) <= x = V2(v2)
    // ...
    // p(v1, v2, ..., vn, x) <= x = Vn(vn)
    pub matcher_pred: chc::PredVarId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumType {
    pub symbol: chc::DatatypeSymbol,
}

impl EnumType {
    pub fn new(symbol: chc::DatatypeSymbol) -> Self {
        EnumType { symbol }
    }

    pub fn into_closed_ty(self) -> Type<Closed> {
        Type::Enum(self)
    }
}

#[derive(Debug, Clone)]
pub enum Type<T> {
    Int,
    Bool,
    String,
    Never,
    Pointer(PointerType<T>),
    Function(FunctionType),
    Tuple(TupleType<T>),
    Enum(EnumType),
}

impl<T> From<FunctionType> for Type<T> {
    fn from(t: FunctionType) -> Type<T> {
        Type::Function(t)
    }
}

impl<T> From<PointerType<T>> for Type<T> {
    fn from(t: PointerType<T>) -> Type<T> {
        Type::Pointer(t)
    }
}

impl<T> From<TupleType<T>> for Type<T> {
    fn from(t: TupleType<T>) -> Type<T> {
        Type::Tuple(t)
    }
}

impl<T> From<EnumType> for Type<T> {
    fn from(t: EnumType) -> Type<T> {
        Type::Enum(t)
    }
}

impl<'a, 'b, T, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Type<T>
where
    T: chc::Var,
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

impl<T> Type<T> {
    fn pretty_atom<'a, 'b, D>(
        &'b self,
        allocator: &'a D,
    ) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec>
    where
        T: chc::Var,
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

    pub fn deref(self) -> RefinedType<T> {
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

    pub fn into_enum(self) -> Option<EnumType> {
        match self {
            Type::Enum(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn into_pointer(self) -> Option<PointerType<T>> {
        match self {
            Type::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn into_tuple(self) -> Option<TupleType<T>> {
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
                let elem_sort = ty.elem.ty.to_sort();
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
                let elem_sorts = ty.elems.iter().map(|ty| ty.ty.to_sort()).collect();
                chc::Sort::tuple(elem_sorts)
            }
            Type::Enum(ty) => chc::Sort::datatype(ty.symbol.clone()),
        }
    }

    pub fn subst_var<F, U>(self, f: F) -> Type<U>
    where
        F: FnMut(T) -> chc::Term<U>,
    {
        match self {
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::String => Type::String,
            Type::Never => Type::Never,
            Type::Pointer(ty) => Type::Pointer(ty.subst_var(f)),
            Type::Function(ty) => Type::Function(ty),
            Type::Tuple(ty) => Type::Tuple(ty.subst_var(f)),
            Type::Enum(ty) => Type::Enum(ty),
        }
    }

    pub fn map_var<F, U>(self, f: F) -> Type<U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::String => Type::String,
            Type::Never => Type::Never,
            Type::Pointer(ty) => Type::Pointer(ty.map_var(f)),
            Type::Function(ty) => Type::Function(ty),
            Type::Tuple(ty) => Type::Tuple(ty.map_var(f)),
            Type::Enum(ty) => Type::Enum(ty),
        }
    }

    pub fn assert_closed(self) -> Type<Closed> {
        self.map_var(|_v| panic!("unexpected variable"))
    }

    pub fn strip_refinement(self) -> Type<Closed> {
        match self {
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::String => Type::String,
            Type::Never => Type::Never,
            Type::Pointer(ty) => Type::Pointer(ty.strip_refinement()),
            Type::Function(ty) => Type::Function(ty),
            Type::Tuple(ty) => Type::Tuple(ty.strip_refinement()),
            Type::Enum(ty) => Type::Enum(ty),
        }
    }
}

impl Type<Closed> {
    pub fn vacuous<FV>(self) -> Type<FV> {
        self.map_var(|v| match v {})
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
    FV: chc::Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            RefinedTypeVar::Value => allocator.text("ν"),
            RefinedTypeVar::Existential(v) => v.pretty(allocator),
            RefinedTypeVar::Free(v) => allocator.text(format!("{v:?}")),
        }
    }
}

impl<T> RefinedTypeVar<T> {
    pub fn shift_existential(self, offset: usize) -> Self {
        match self {
            RefinedTypeVar::Existential(v) => RefinedTypeVar::Existential(v + offset),
            v => v,
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
    FV: chc::Var,
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

    pub fn extend(&mut self, other: Refinement<FV>) {
        let Refinement {
            atoms,
            existentials,
        } = other;
        self.atoms.extend(
            atoms
                .into_iter()
                .map(|a| a.map_var(|v| v.shift_existential(self.existentials.len()))),
        );
        self.existentials.extend(existentials);
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
    pub ty: Type<FV>,
    pub refinement: Refinement<FV>,
}

impl<'a, 'b, D, FV> Pretty<'a, D, termcolor::ColorSpec> for &'b RefinedType<FV>
where
    FV: chc::Var,
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
    fn pretty_atom<'a, 'b, D>(
        &'b self,
        allocator: &'a D,
    ) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec>
    where
        FV: chc::Var,
        D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        if self.refinement.is_top() {
            self.ty.pretty_atom(allocator)
        } else {
            self.pretty(allocator)
        }
    }

    pub fn new(ty: Type<FV>, refinement: Refinement<FV>) -> Self {
        RefinedType { ty, refinement }
    }

    pub fn refined_with_term(ty: Type<FV>, term: chc::Term<FV>) -> Self {
        let term = term.map_var(RefinedTypeVar::Free);
        let refinement = chc::Term::var(RefinedTypeVar::Value).equal_to(term);
        RefinedType::new(ty, refinement.into())
    }

    pub fn subst_var<F, W>(self, mut f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> chc::Term<W>,
    {
        RefinedType {
            ty: self.ty.subst_var(&mut f),
            refinement: self.refinement.subst_var(&mut f),
        }
    }

    pub fn map_var<F, W>(self, mut f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> W,
    {
        RefinedType {
            ty: self.ty.map_var(Box::new(&mut f) as Box<dyn FnMut(FV) -> W>),
            refinement: self.refinement.map_var(&mut f),
        }
    }

    pub fn is_refined(&self) -> bool {
        !self.refinement.is_top()
    }

    pub fn unrefined(ty: Type<FV>) -> Self {
        RefinedType::new(ty, chc::Atom::top().into())
    }

    pub fn extend_refinement(&mut self, refinement: Refinement<FV>) {
        self.refinement.extend(refinement);
    }

    pub fn strip_refinement(self) -> Type<Closed> {
        self.ty.strip_refinement()
    }
}

impl RefinedType<Closed> {
    pub fn vacuous<FV>(self) -> RefinedType<FV> {
        self.map_var(|v| match v {})
    }
}
