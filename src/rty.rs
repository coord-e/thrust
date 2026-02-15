//! Data structures for refinement types.
//!
//! Thrust is a refinement type system, and so its analysis is about giving refinement types to
//! variables and terms. This module defines the data structures for representing refinement
//! types. The central data structure is [`RefinedType`], which is just [`Type`] plus [`Refinement`].
//!
//! Note that there are two notions of "variables" in this module. First is a type variable which is
//! a polymorphic type parameter which is represented by [`TypeParamIdx`], and forms one of valid type as [`ParamType`].
//! `T` in `struct S<T> { f: T }` is a type variable. See [`params`] module for the handling of type parameters.
//! Second is a logical variable which is a variable that can appear in logical predicates.
//! `x` and `y` in `{ x: int | x > y }` are logical variables.
//! The actual representation of logical variables varies by context and so it is often parameterized
//! as a type parameter in this module (`T` in `Type<T>`). In [`FunctionType`], logical variables are
//! function parameters (`Type<FunctionParamIdx`), and during the actual analysis, logical variables are
//! program variables bound in the environment (`Type<Var>`, see [`crate::refine::Var`]).
//! We have [`RefinedTypeVar<T>`] to denote logical variables in refinement predicates, which
//! accepts existential variables and a variable bound in the refinement type (`x` in `{ x: T | phi
//! }`) in addition to variables `T` from the outer scope. This module also contains [`Closed`] which is
//! used to denote a closed type, so `Type<Closed>` ensures no logical variables from the outer scope
//! appear in that type.
//!
//! We have distinct types for each variant of [`Type`], such as [`FunctionType`] and
//! [`PointerType`]. [`Type`], [`RefinedType`] and these variant types share some common operations:
//!
//! - `subst_var`: Substitutes logical variables with logical terms.
//! - `map_var`: Maps logical variables to other logical variables.
//! - `free_ty_params`: Collects free type parameters [`TypeParamIdx`] in the type.
//! - `subst_ty_params`: Substitutes type parameters with other types. Since this replaces
//!   type parameters with refinement types, [`Type`] does not implement this, and
//!   [`RefinedType::subst_ty_params`] handles the substitution logic instead.
//! - `strip_refinement`: Strips the refinements recursively and returns a [`Closed`] type.
//!
//! This module also implements several logics for manipulating refinement types and is extensively used in
//! upstream logic in the [`crate::refine`] and [`crate::analyze`] modules.
//!
//! - [`template`]: Generates "template" refinement types with unknown predicates to be inferred.
//! - [`subtyping`]: Generates CHC constraints [`crate::chc`] from subtyping relations between types.
//! - [`clause_builder`]: Helper to build [`crate::chc::Clause`] from the refinement types.

use std::collections::{HashMap, HashSet};

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

mod params;
pub use params::{RefinedTypeArgs, TypeParamIdx, TypeParamSubst};

rustc_index::newtype_index! {
    /// An index representing function parameter.
    ///
    /// We manage function parameters using indices that are unique in a function.
    /// [`FunctionType`] contains `IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>`
    /// that manages the indices and types of the function parameters.
    #[orderable]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum FunctionAbi {
    #[default]
    Rust,
    RustCall,
}

impl std::fmt::Display for FunctionAbi {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

impl FunctionAbi {
    pub fn name(&self) -> &'static str {
        match self {
            FunctionAbi::Rust => "rust",
            FunctionAbi::RustCall => "rust-call",
        }
    }

    pub fn is_rust(&self) -> bool {
        matches!(self, FunctionAbi::Rust)
    }

    pub fn is_rust_call(&self) -> bool {
        matches!(self, FunctionAbi::RustCall)
    }
}

/// A function type.
///
/// In Thrust, function types are closed. Because of that, function types, thus its parameters and
/// return type only refer to the parameters of the function itself using [`FunctionParamIdx`] and
/// do not accept other type of variables from the environment.
#[derive(Debug, Clone)]
pub struct FunctionType {
    pub params: IndexVec<FunctionParamIdx, RefinedType<FunctionParamIdx>>,
    pub ret: Box<RefinedType<FunctionParamIdx>>,
    pub abi: FunctionAbi,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b FunctionType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let abi = match self.abi {
            FunctionAbi::Rust => allocator.nil(),
            abi => allocator
                .text("extern")
                .append(allocator.space())
                .append(allocator.as_string(abi))
                .append(allocator.space()),
        };
        let separator = allocator.text(",").append(allocator.line());
        abi.append(
            allocator
                .intersperse(self.params.iter().map(|ty| ty.pretty(allocator)), separator)
                .parens(),
        )
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
            abi: FunctionAbi::Rust,
        }
    }

    pub fn with_abi(mut self, abi: FunctionAbi) -> Self {
        self.abi = abi;
        self
    }

    /// Because function types are always closed in Thrust, we can convert this into
    /// [`Type<Closed>`].
    pub fn into_closed_ty(self) -> Type<Closed> {
        Type::Function(self)
    }

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        self.params
            .iter()
            .flat_map(RefinedType::free_ty_params)
            .chain(self.ret.free_ty_params())
            .collect()
    }

    pub fn subst_ty_params(&mut self, subst: &TypeParamSubst<Closed>) {
        let subst = subst.clone().vacuous();
        for param in &mut self.params {
            param.subst_ty_params(&subst);
        }
        self.ret.subst_ty_params(&subst);
    }

    pub fn unify_ty_params(self, other: FunctionType) -> TypeParamSubst<FunctionParamIdx> {
        assert_eq!(self.params.len(), other.params.len());
        let mut tys1 = self.params;
        tys1.push(*self.ret);
        let mut tys2 = other.params;
        tys2.push(*other.ret);
        unify_tys_params(tys1, tys2)
    }
}

/// The kind of a reference, which is either mutable or immutable.
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

/// The kind of a pointer, which is either a reference or an owned pointer.
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

/// A pointer type.
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
    pub fn new(kind: PointerKind, elem: Type<T>) -> Self {
        PointerType {
            kind,
            elem: Box::new(RefinedType::unrefined(elem)),
        }
    }

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
        matches!(self.kind, PointerKind::Ref(RefKind::Mut))
    }

    pub fn is_own(&self) -> bool {
        matches!(self.kind, PointerKind::Own)
    }

    pub fn own(ty: Type<T>) -> Self {
        PointerType::own_refined(RefinedType::unrefined(ty))
    }

    pub fn own_refined(ty: RefinedType<T>) -> Self {
        PointerType {
            kind: PointerKind::Own,
            elem: Box::new(ty),
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

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        self.elem.free_ty_params()
    }

    pub fn subst_ty_params(&mut self, subst: &TypeParamSubst<T>)
    where
        T: chc::Var,
    {
        self.elem.subst_ty_params(subst)
    }

    pub fn unify_ty_params(self, other: PointerType<T>) -> TypeParamSubst<T>
    where
        T: chc::Var,
    {
        assert_eq!(self.kind, other.kind);
        self.elem.unify_ty_params(*other.elem)
    }
}

/// A tuple type.
///
/// Note that the current implementation uses tuples to represent structs. See
/// implementation in `crate::refine::template` module for details.
/// It is our TODO to improve the struct representation.
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

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        self.elems
            .iter()
            .flat_map(RefinedType::free_ty_params)
            .collect()
    }

    pub fn subst_ty_params(&mut self, subst: &TypeParamSubst<T>)
    where
        T: chc::Var,
    {
        for elem in &mut self.elems {
            elem.subst_ty_params(subst);
        }
    }

    pub fn unify_ty_params(self, other: TupleType<T>) -> TypeParamSubst<T>
    where
        T: chc::Var,
    {
        assert_eq!(self.elems.len(), other.elems.len());
        unify_tys_params(self.elems, other.elems)
    }
}

/// A definition of an enum variant, found in [`EnumDatatypeDef`].
#[derive(Debug, Clone)]
pub struct EnumVariantDef {
    pub name: chc::DatatypeSymbol,
    pub discr: u32,
    pub field_tys: Vec<Type<Closed>>,
}

/// A definition of an enum datatype.
#[derive(Debug, Clone)]
pub struct EnumDatatypeDef {
    pub name: chc::DatatypeSymbol,
    pub ty_params: usize,
    pub variants: IndexVec<VariantIdx, EnumVariantDef>,
}

impl EnumDatatypeDef {
    pub fn field_tys(&self) -> impl Iterator<Item = &Type<Closed>> {
        self.variants.iter().flat_map(|v| &v.field_tys)
    }
}

/// An enum type.
///
/// An enum type includes its type arguments and the argument types can refer to outer variables `T`.
#[derive(Debug, Clone)]
pub struct EnumType<T> {
    pub symbol: chc::DatatypeSymbol,
    pub args: IndexVec<TypeParamIdx, RefinedType<T>>,
}

impl<'a, 'b, D, V> Pretty<'a, D, termcolor::ColorSpec> for &'b EnumType<V>
where
    V: chc::Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let inner = allocator.intersperse(
            self.args.iter().map(|t| t.pretty(allocator)),
            allocator.text(",").append(allocator.line()),
        );
        let sym = self.symbol.pretty(allocator);
        if self.args.is_empty() {
            sym
        } else {
            sym.append(allocator.line())
                .append(inner.nest(2).angles())
                .group()
        }
    }
}

impl<T> EnumType<T> {
    pub fn new(symbol: chc::DatatypeSymbol, args: RefinedTypeArgs<T>) -> Self {
        EnumType { symbol, args }
    }

    pub fn symbol(&self) -> &chc::DatatypeSymbol {
        &self.symbol
    }

    pub fn arg_sorts(&self) -> Vec<chc::Sort> {
        self.args.iter().map(|ty| ty.ty.to_sort()).collect()
    }

    pub fn subst_var<F, U>(self, mut f: F) -> EnumType<U>
    where
        F: FnMut(T) -> chc::Term<U>,
    {
        EnumType {
            symbol: self.symbol,
            args: self
                .args
                .into_iter()
                .map(|ty| ty.subst_var(&mut f))
                .collect(),
        }
    }

    pub fn map_var<F, U>(self, mut f: F) -> EnumType<U>
    where
        F: FnMut(T) -> U,
    {
        EnumType {
            symbol: self.symbol,
            args: self.args.into_iter().map(|ty| ty.map_var(&mut f)).collect(),
        }
    }

    pub fn strip_refinement(self) -> EnumType<Closed> {
        EnumType {
            symbol: self.symbol,
            args: self
                .args
                .into_iter()
                .map(|ty| RefinedType::unrefined(ty.strip_refinement()))
                .collect(),
        }
    }

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        self.args
            .iter()
            .flat_map(RefinedType::free_ty_params)
            .collect()
    }

    pub fn subst_ty_params(&mut self, subst: &TypeParamSubst<T>)
    where
        T: chc::Var,
    {
        for arg in &mut self.args {
            arg.subst_ty_params(subst);
        }
    }

    pub fn unify_ty_params(self, other: EnumType<T>) -> TypeParamSubst<T>
    where
        T: chc::Var,
    {
        assert_eq!(self.symbol, other.symbol);
        unify_tys_params(self.args, other.args)
    }
}

/// A type parameter.
#[derive(Debug, Clone)]
pub struct ParamType {
    pub idx: TypeParamIdx,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b ParamType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        self.idx.pretty(allocator)
    }
}

impl ParamType {
    pub fn new(idx: TypeParamIdx) -> Self {
        ParamType { idx }
    }

    pub fn index(&self) -> TypeParamIdx {
        self.idx
    }

    pub fn into_closed_ty(self) -> Type<Closed> {
        Type::Param(self)
    }
}

/// An array type.
#[derive(Debug, Clone)]
pub struct ArrayType<T> {
    pub index: Box<RefinedType<T>>,
    pub elem: Box<RefinedType<T>>,
}

impl<'a, 'b, T, D> Pretty<'a, D, termcolor::ColorSpec> for &'b ArrayType<T>
where
    T: chc::Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.text("Array").append(
            self.index
                .pretty(allocator)
                .append(allocator.text(", "))
                .append(self.elem.pretty(allocator))
                .angles(),
        )
    }
}

impl<T> ArrayType<T> {
    pub fn new(index: Type<T>, elem: Type<T>) -> Self {
        ArrayType {
            index: Box::new(RefinedType::unrefined(index)),
            elem: Box::new(RefinedType::unrefined(elem)),
        }
    }

    pub fn subst_var<F, U>(self, mut f: F) -> ArrayType<U>
    where
        F: FnMut(T) -> chc::Term<U>,
    {
        ArrayType {
            index: Box::new(self.index.subst_var(&mut f)),
            elem: Box::new(self.elem.subst_var(&mut f)),
        }
    }

    pub fn map_var<F, U>(self, mut f: F) -> ArrayType<U>
    where
        F: FnMut(T) -> U,
    {
        ArrayType {
            index: Box::new(self.index.map_var(&mut f)),
            elem: Box::new(self.elem.map_var(&mut f)),
        }
    }

    pub fn strip_refinement(self) -> ArrayType<Closed> {
        ArrayType {
            index: Box::new(RefinedType::unrefined(self.index.strip_refinement())),
            elem: Box::new(RefinedType::unrefined(self.elem.strip_refinement())),
        }
    }

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        self.index
            .free_ty_params()
            .into_iter()
            .chain(self.elem.free_ty_params())
            .collect()
    }

    pub fn subst_ty_params(&mut self, subst: &TypeParamSubst<T>)
    where
        T: chc::Var,
    {
        self.index.subst_ty_params(subst);
        self.elem.subst_ty_params(subst);
    }

    pub fn unify_ty_params(self, other: ArrayType<T>) -> TypeParamSubst<T>
    where
        T: chc::Var,
    {
        unify_tys_params([*self.index, *self.elem], [*other.index, *other.elem])
    }
}

/// An underlying type of a refinement type.
#[derive(Debug, Clone)]
pub enum Type<T> {
    Int,
    Bool,
    String,
    Never,
    Param(ParamType),
    Pointer(PointerType<T>),
    Function(FunctionType),
    Tuple(TupleType<T>),
    Array(ArrayType<T>),
    Enum(EnumType<T>),
}

impl<T> From<ParamType> for Type<T> {
    fn from(t: ParamType) -> Type<T> {
        Type::Param(t)
    }
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

impl<T> From<ArrayType<T>> for Type<T> {
    fn from(t: ArrayType<T>) -> Type<T> {
        Type::Array(t)
    }
}

impl<T> From<EnumType<T>> for Type<T> {
    fn from(t: EnumType<T>) -> Type<T> {
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
            Type::Param(ty) => ty.pretty(allocator),
            Type::Pointer(ty) => ty.pretty(allocator),
            Type::Function(ty) => ty.pretty(allocator),
            Type::Tuple(ty) => ty.pretty(allocator),
            Type::Array(ty) => ty.pretty(allocator),
            Type::Enum(ty) => ty.pretty(allocator),
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

    pub fn as_pointer(&self) -> Option<&PointerType<T>> {
        match self {
            Type::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn as_enum(&self) -> Option<&EnumType<T>> {
        match self {
            Type::Enum(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn as_tuple(&self) -> Option<&TupleType<T>> {
        match self {
            Type::Tuple(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn into_enum(self) -> Option<EnumType<T>> {
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
            Type::Param(ty) => chc::Sort::param(ty.index().into()),
            Type::Pointer(ty) => {
                let elem_sort = ty.elem.ty.to_sort();

                match ty.kind {
                    PointerKind::Ref(RefKind::Immut) | PointerKind::Own => {
                        chc::Sort::box_(elem_sort)
                    }
                    PointerKind::Ref(RefKind::Mut) => chc::Sort::mut_(elem_sort),
                }
            }
            Type::Function { .. } => chc::Sort::null(),
            Type::Tuple(ty) => {
                let elem_sorts = ty.elems.iter().map(|ty| ty.ty.to_sort()).collect();
                chc::Sort::tuple(elem_sorts)
            }
            Type::Array(ty) => {
                let index_sort = ty.index.ty.to_sort();
                let elem_sort = ty.elem.ty.to_sort();
                chc::Sort::array(index_sort, elem_sort)
            }
            Type::Enum(ty) => {
                let arg_sorts = ty.args.iter().map(|ty| ty.ty.to_sort()).collect();
                chc::Sort::datatype(ty.symbol.clone(), arg_sorts)
            }
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
            Type::Param(ty) => Type::Param(ty),
            Type::Pointer(ty) => Type::Pointer(ty.subst_var(f)),
            Type::Function(ty) => Type::Function(ty),
            Type::Tuple(ty) => Type::Tuple(ty.subst_var(f)),
            Type::Array(ty) => Type::Array(ty.subst_var(f)),
            Type::Enum(ty) => Type::Enum(ty.subst_var(f)),
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
            Type::Param(ty) => Type::Param(ty),
            Type::Pointer(ty) => Type::Pointer(ty.map_var(f)),
            Type::Function(ty) => Type::Function(ty),
            Type::Tuple(ty) => Type::Tuple(ty.map_var(f)),
            Type::Array(ty) => Type::Array(ty.map_var(f)),
            Type::Enum(ty) => Type::Enum(ty.map_var(f)),
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
            Type::Param(ty) => Type::Param(ty),
            Type::Pointer(ty) => Type::Pointer(ty.strip_refinement()),
            Type::Function(ty) => Type::Function(ty),
            Type::Tuple(ty) => Type::Tuple(ty.strip_refinement()),
            Type::Array(ty) => Type::Array(ty.strip_refinement()),
            Type::Enum(ty) => Type::Enum(ty.strip_refinement()),
        }
    }

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        match self {
            Type::Int | Type::Bool | Type::String | Type::Never => Default::default(),
            Type::Param(ty) => std::iter::once(ty.index()).collect(),
            Type::Pointer(ty) => ty.free_ty_params(),
            Type::Function(ty) => ty.free_ty_params(),
            Type::Tuple(ty) => ty.free_ty_params(),
            Type::Array(ty) => ty.free_ty_params(),
            Type::Enum(ty) => ty.free_ty_params(),
        }
    }
}

impl Type<Closed> {
    pub fn vacuous<FV>(self) -> Type<FV> {
        self.map_var(|v| match v {})
    }
}

/// A marker type for closed types.
///
/// Because the value of `Closed` can never exist, `Type<Closed>` ensures that no
/// logical variables from outer scope appear in the type.
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
    /// An index representing existential variables.
    ///
    /// We manage existential variables using indices that are unique in a [`Formula`].
    /// [`Formula`] contains `IndexVec<ExistentialVarIdx, chc::Sort>` that manages the indices
    /// and sorts of the existential variables.
    #[orderable]
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

pub trait ShiftExistential {
    fn shift_existential(self, offset: usize) -> Self;
}

/// A logical variable in a refinement predicate.
///
/// Given a refinement type `{ v: T | ∃e. φ }`, there are three cases of logical variables
/// occurring in the predicate `φ`:
///
/// - `RefinedTypeVar::Value`: a variable `v` representing the value of the type
/// - `RefinedTypeVar::Existential`: an existential variable `e`
/// - `RefinedTypeVar::Free`: a variable from the outer scope, such as function parameters or
///    variables bound in the environment
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<T> std::fmt::Debug for RefinedTypeVar<T>
where
    T: std::fmt::Debug,
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

impl<T> ShiftExistential for RefinedTypeVar<T> {
    fn shift_existential(self, offset: usize) -> Self {
        match self {
            RefinedTypeVar::Existential(v) => RefinedTypeVar::Existential(v + offset),
            v => v,
        }
    }
}

/// A formula, potentially equipped with an existential quantifier.
///
/// Note: This is not to be confused with [`crate::chc::Formula`] in the [`crate::chc`] module, which is a different notion.
#[derive(Debug, Clone)]
pub struct Formula<V> {
    pub existentials: IndexVec<ExistentialVarIdx, chc::Sort>,
    pub body: chc::Body<V>,
}

impl<V> Default for Formula<V> {
    fn default() -> Self {
        Formula {
            existentials: Default::default(),
            body: Default::default(),
        }
    }
}

impl<V> From<chc::Body<V>> for Formula<V> {
    fn from(body: chc::Body<V>) -> Self {
        Formula {
            existentials: IndexVec::new(),
            body,
        }
    }
}

impl<V> From<chc::Atom<V>> for Formula<V> {
    fn from(atom: chc::Atom<V>) -> Self {
        Formula {
            existentials: IndexVec::new(),
            body: chc::Body::new(vec![atom], chc::Formula::top()),
        }
    }
}

impl<V> From<chc::Formula<V>> for Formula<V> {
    fn from(formula: chc::Formula<V>) -> Self {
        Formula {
            existentials: IndexVec::new(),
            body: chc::Body::new(vec![], formula),
        }
    }
}

impl<V> Extend<Formula<V>> for Formula<V>
where
    V: ShiftExistential,
{
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = Formula<V>>,
    {
        for formula in iter {
            self.push_conj(formula);
        }
        self.body.simplify();
    }
}

impl<V> FromIterator<Formula<V>> for Formula<V>
where
    V: ShiftExistential,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Formula<V>>,
    {
        let mut result = Formula::default();
        result.extend(iter);
        result
    }
}

impl<'a, 'b, D, V> Pretty<'a, D, termcolor::ColorSpec> for &'b Formula<V>
where
    V: chc::Var,
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
        let body = self.body.pretty(allocator);
        if self.existentials.is_empty() {
            body
        } else {
            allocator
                .text("∃")
                .append(existentials.nest(2))
                .append(allocator.text("."))
                .append(allocator.line().append(body).nest(2))
                .group()
        }
    }
}

impl<V> Formula<V> {
    pub fn new(existentials: IndexVec<ExistentialVarIdx, chc::Sort>, body: chc::Body<V>) -> Self {
        Formula { existentials, body }
    }

    pub fn has_existentials(&self) -> bool {
        !self.existentials.is_empty()
    }

    pub fn existentials(&self) -> impl Iterator<Item = (ExistentialVarIdx, &chc::Sort)> + '_ {
        self.existentials.iter_enumerated()
    }

    pub fn is_top(&self) -> bool {
        self.body.is_top()
    }

    pub fn is_bottom(&self) -> bool {
        self.body.is_bottom()
    }

    pub fn top() -> Self {
        Formula::new(IndexVec::new(), chc::Body::top())
    }

    pub fn bottom() -> Self {
        Formula::new(IndexVec::new(), chc::Body::bottom())
    }
}

impl<V> Formula<V>
where
    V: chc::Var,
{
    pub fn guarded(self, guard: chc::Formula<V>) -> Self {
        let Formula { existentials, body } = self;
        Formula {
            existentials,
            body: body.guarded(guard),
        }
    }
}

impl<V> Formula<V>
where
    V: ShiftExistential,
{
    pub fn push_conj(&mut self, other: Self) {
        let Formula { existentials, body } = other;
        self.body
            .push_conj(body.map_var(|v| v.shift_existential(self.existentials.len())));
        self.existentials.extend(existentials);
        self.body.simplify();
    }
}

/// A refinement predicate in a refinement type.
///
/// This is a [`Formula`], but gives an explicit representation of the kinds of variables that can appear in
/// the refinement predicates. See [`RefinedTypeVar`] for details.
pub type Refinement<FV = Closed> = Formula<RefinedTypeVar<FV>>;

impl<FV> Refinement<FV> {
    pub fn subst_var<F, W>(self, mut f: F) -> Refinement<W>
    where
        F: FnMut(FV) -> chc::Term<W>,
    {
        Refinement {
            existentials: self.existentials,
            body: self.body.subst_var(|v| match v {
                RefinedTypeVar::Value => chc::Term::var(RefinedTypeVar::Value),
                RefinedTypeVar::Existential(v) => chc::Term::var(RefinedTypeVar::Existential(v)),
                RefinedTypeVar::Free(v) => f(v).map_var(RefinedTypeVar::Free),
            }),
        }
    }

    pub fn subst_value_var<F>(self, mut f: F) -> Self
    where
        F: FnMut() -> chc::Term<RefinedTypeVar<FV>>,
    {
        Refinement {
            existentials: self.existentials,
            body: self.body.subst_var(|v| match v {
                RefinedTypeVar::Value => f(),
                RefinedTypeVar::Existential(v) => chc::Term::var(RefinedTypeVar::Existential(v)),
                RefinedTypeVar::Free(v) => chc::Term::var(RefinedTypeVar::Free(v)),
            }),
        }
    }

    pub fn map_var<F, W>(self, mut f: F) -> Refinement<W>
    where
        F: FnMut(FV) -> W,
    {
        Refinement {
            existentials: self.existentials,
            body: self.body.map_var(|v| match v {
                RefinedTypeVar::Value => RefinedTypeVar::Value,
                RefinedTypeVar::Existential(v) => RefinedTypeVar::Existential(v),
                RefinedTypeVar::Free(v) => RefinedTypeVar::Free(f(v)),
            }),
        }
    }

    pub fn instantiate(self) -> Instantiator<FV> {
        Instantiator {
            value_var: None,
            existentials: HashMap::new(),
            refinement: self,
        }
    }

    pub fn subst_ty_params_in_sorts<T>(&mut self, subst: &TypeParamSubst<T>) {
        for sort in &mut self.existentials {
            subst_ty_params_in_sort(sort, subst);
        }
        subst_ty_params_in_body(&mut self.body, subst);
    }
}

/// A helper type to map logical variables in a refinement at once.
///
/// This is essentially just calling `Refinement::map_var`, but provides a convenient interface to
/// construct the mapping of the variables.
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

    pub fn instantiate(self) -> chc::Body<T>
    where
        T: Clone,
    {
        let Instantiator {
            value_var,
            existentials,
            refinement,
        } = self;
        refinement.body.map_var(move |v| match v {
            RefinedTypeVar::Value => value_var.clone().unwrap(),
            RefinedTypeVar::Existential(v) => existentials[&v].clone(),
            RefinedTypeVar::Free(v) => v,
        })
    }
}

/// A refinement type.
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

    pub fn boxed(self) -> Self {
        let RefinedType {
            ty: inner_ty,
            refinement: inner_refinement,
        } = self;
        let ty = PointerType::own(inner_ty).into();
        let refinement = inner_refinement
            .subst_value_var(|| chc::Term::var(RefinedTypeVar::Value).box_current());
        RefinedType { ty, refinement }
    }

    pub fn guarded(self, guard: chc::Formula<FV>) -> Self
    where
        FV: chc::Var,
    {
        let RefinedType { ty, refinement } = self;
        let refinement = refinement.guarded(guard.map_var(RefinedTypeVar::Free));
        RefinedType { ty, refinement }
    }

    /// Returns a dereferenced type of the immutable reference or owned pointer.
    ///
    /// e.g. `{ v: Box<T> | φ }  -->  { v: T | φ[box v/v] }`
    pub fn deref(self) -> Self {
        let RefinedType {
            ty,
            refinement: outer_refinement,
        } = self;
        let inner_ty = ty.into_pointer().expect("invalid deref");
        if inner_ty.is_mut() {
            // losing info about proph
            panic!("invalid deref");
        }
        let RefinedType {
            ty: inner_ty,
            refinement: mut inner_refinement,
        } = *inner_ty.elem;
        inner_refinement.push_conj(
            outer_refinement.subst_value_var(|| chc::Term::var(RefinedTypeVar::Value).boxed()),
        );
        RefinedType {
            ty: inner_ty,
            refinement: inner_refinement,
        }
    }

    pub fn subst_var<F, W>(self, mut f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> chc::Term<W>,
    {
        RefinedType {
            ty: self
                .ty
                .subst_var(Box::new(&mut f) as Box<dyn FnMut(FV) -> chc::Term<W>>),
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
        self.refinement.push_conj(refinement);
    }

    pub fn strip_refinement(self) -> Type<Closed> {
        self.ty.strip_refinement()
    }

    pub fn free_ty_params(&self) -> HashSet<TypeParamIdx> {
        self.ty.free_ty_params()
    }

    pub fn subst_ty_params(&mut self, subst: &TypeParamSubst<FV>)
    where
        FV: chc::Var,
    {
        self.refinement.subst_ty_params_in_sorts(subst);
        match &mut self.ty {
            Type::Int | Type::Bool | Type::String | Type::Never => {}
            Type::Param(ty) => {
                if let Some(rty) = subst.get(ty.index()) {
                    let RefinedType {
                        ty: replacement_ty,
                        refinement,
                    } = rty.clone();
                    self.refinement.push_conj(refinement);
                    self.ty = replacement_ty;
                }
            }
            Type::Pointer(ty) => ty.subst_ty_params(subst),
            Type::Function(ty) => {
                let subst = subst.clone().strip_refinement();
                ty.subst_ty_params(&subst)
            }
            Type::Tuple(ty) => ty.subst_ty_params(subst),
            Type::Array(ty) => ty.subst_ty_params(subst),
            Type::Enum(ty) => ty.subst_ty_params(subst),
        }
    }

    pub fn instantiate_ty_params(&mut self, params: RefinedTypeArgs<FV>)
    where
        FV: chc::Var,
    {
        self.subst_ty_params(&params.into());
    }

    pub fn unify_ty_params(self, other: RefinedType<FV>) -> TypeParamSubst<FV>
    where
        FV: chc::Var,
    {
        match (self.ty, other.ty) {
            (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::String, Type::String)
            | (Type::Never, Type::Never) => Default::default(),
            (Type::Param(pty), ty) if !ty.free_ty_params().contains(&pty.index()) => {
                TypeParamSubst::singleton(
                    pty.index(),
                    RefinedType::new(ty.clone(), other.refinement.clone()),
                )
            }
            (ty, Type::Param(pty)) if !ty.free_ty_params().contains(&pty.index()) => {
                TypeParamSubst::singleton(
                    pty.index(),
                    RefinedType::new(ty.clone(), self.refinement.clone()),
                )
            }
            (Type::Pointer(ty1), Type::Pointer(ty2)) => ty1.unify_ty_params(ty2),
            (Type::Function(ty1), Type::Function(ty2)) => {
                // TODO: what should we do for in-function refinement substs?
                ty1.unify_ty_params(ty2).strip_refinement().vacuous()
            }
            (Type::Tuple(ty1), Type::Tuple(ty2)) => ty1.unify_ty_params(ty2),
            (Type::Array(ty1), Type::Array(ty2)) => ty1.unify_ty_params(ty2),
            (Type::Enum(ty1), Type::Enum(ty2)) => ty1.unify_ty_params(ty2),
            (t1, t2) => panic!("unify_ty_params: mismatched types t1={:?}, t2={:?}", t1, t2),
        }
    }
}

impl RefinedType<Closed> {
    pub fn vacuous<FV>(self) -> RefinedType<FV> {
        self.map_var(|v| match v {})
    }
}

/// Substitutes type parameters in a sort.
fn subst_ty_params_in_sort<T>(sort: &mut chc::Sort, subst: &TypeParamSubst<T>) {
    match sort {
        chc::Sort::Null | chc::Sort::Int | chc::Sort::Bool | chc::Sort::String => {}
        chc::Sort::Param(idx) => {
            let type_param_idx = TypeParamIdx::from_usize(*idx);
            if let Some(rty) = subst.get(type_param_idx) {
                *sort = rty.ty.to_sort();
            }
        }
        chc::Sort::Box(s) | chc::Sort::Mut(s) => {
            subst_ty_params_in_sort(s, subst);
        }
        chc::Sort::Tuple(sorts) => {
            for s in sorts {
                subst_ty_params_in_sort(s, subst);
            }
        }
        chc::Sort::Array(s1, s2) => {
            subst_ty_params_in_sort(s1, subst);
            subst_ty_params_in_sort(s2, subst);
        }
        chc::Sort::Datatype(dt_sort) => {
            for s in dt_sort.args_mut() {
                subst_ty_params_in_sort(s, subst);
            }
        }
    }
}

/// Substitutes type parameters in all sorts appearing in a body.
fn subst_ty_params_in_body<T, V>(body: &mut chc::Body<V>, subst: &TypeParamSubst<T>) {
    for atom in &mut body.atoms {
        subst_ty_params_in_atom(atom, subst);
    }
    subst_ty_params_in_formula(&mut body.formula, subst);
}

/// Substitutes type parameters in all sorts appearing in an atom.
fn subst_ty_params_in_atom<T, V>(atom: &mut chc::Atom<V>, subst: &TypeParamSubst<T>) {
    if let Some(guard) = &mut atom.guard {
        subst_ty_params_in_formula(guard, subst);
    }
    for term in &mut atom.args {
        subst_ty_params_in_term(term, subst);
    }
}

/// Substitutes type parameters in all sorts appearing in a formula.
fn subst_ty_params_in_formula<T, V>(formula: &mut chc::Formula<V>, subst: &TypeParamSubst<T>) {
    match formula {
        chc::Formula::Atom(atom) => subst_ty_params_in_atom(atom, subst),
        chc::Formula::Not(f) => subst_ty_params_in_formula(f, subst),
        chc::Formula::And(fs) | chc::Formula::Or(fs) => {
            for f in fs {
                subst_ty_params_in_formula(f, subst);
            }
        }
        chc::Formula::Exists(vars, f) => {
            for (_, sort) in vars {
                subst_ty_params_in_sort(sort, subst);
            }
            subst_ty_params_in_formula(f, subst);
        }
    }
}

/// Substitutes type parameters in all sorts appearing in a term.
fn subst_ty_params_in_term<T, V>(term: &mut chc::Term<V>, subst: &TypeParamSubst<T>) {
    match term {
        chc::Term::Null
        | chc::Term::Var(_)
        | chc::Term::Bool(_)
        | chc::Term::Int(_)
        | chc::Term::String(_) => {}
        chc::Term::Box(t)
        | chc::Term::BoxCurrent(t)
        | chc::Term::MutCurrent(t)
        | chc::Term::MutFinal(t)
        | chc::Term::TupleProj(t, _)
        | chc::Term::DatatypeDiscr(_, t) => {
            subst_ty_params_in_term(t, subst);
        }
        chc::Term::Mut(t1, t2) => {
            subst_ty_params_in_term(t1, subst);
            subst_ty_params_in_term(t2, subst);
        }
        chc::Term::App(_, args) | chc::Term::Tuple(args) => {
            for arg in args {
                subst_ty_params_in_term(arg, subst);
            }
        }
        chc::Term::DatatypeCtor(s, _, args) => {
            for arg in s.args_mut() {
                subst_ty_params_in_sort(arg, subst);
            }
            for arg in args {
                subst_ty_params_in_term(arg, subst);
            }
        }
        chc::Term::FormulaExistentialVar(sort, _) => {
            subst_ty_params_in_sort(sort, subst);
        }
    }
}

pub fn unify_tys_params<I1, I2, T>(tys1: I1, tys2: I2) -> TypeParamSubst<T>
where
    T: chc::Var,
    I1: IntoIterator<Item = RefinedType<T>>,
    I2: IntoIterator<Item = RefinedType<T>>,
{
    tys1.into_iter()
        .zip(tys2)
        .fold(Default::default(), |s1, (mut t1, mut t2)| {
            t1.subst_ty_params(&s1);
            t2.subst_ty_params(&s1);
            let mut s2 = t1.unify_ty_params(t2);
            s2.compose(s1);
            s2
        })
}
