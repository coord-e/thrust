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

    pub fn is_unit(&self) -> bool {
        self.elems.is_empty()
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Unit,
    Int,
    Bool,
    String,
    Never,
    Pointer(PointerType),
    Function(FunctionType),
    Tuple(TupleType),
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

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Type
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            Type::Unit => allocator.text("()"),
            Type::Int => allocator.text("int"),
            Type::Bool => allocator.text("bool"),
            Type::String => allocator.text("string"),
            Type::Never => allocator.text("!"),
            Type::Pointer(ty) => ty.pretty(allocator),
            Type::Function(ty) => ty.pretty(allocator),
            Type::Tuple(ty) => ty.pretty(allocator),
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
        Type::Unit
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
        matches!(self, Type::Unit)
    }

    pub fn as_function(&self) -> Option<&FunctionType> {
        match self {
            Type::Function(ty) => Some(ty),
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
            Type::Unit => chc::Sort::null(),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RefinedTypeVar<FV> {
    Value,
    Free(FV),
}

impl<FV> std::fmt::Display for RefinedTypeVar<FV>
where
    FV: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RefinedTypeVar::Value => f.write_str("ν"),
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
            RefinedTypeVar::Free(v) => v.pretty(allocator),
        }
    }
}

pub type Refinement<FV = Closed> = chc::Atom<RefinedTypeVar<FV>>;

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
                .append(&self.refinement)
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
        RefinedType::new(ty, refinement)
    }

    pub fn subst_var<F, W>(self, mut f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> chc::Term<W>,
    {
        RefinedType {
            ty: self.ty,
            refinement: self.refinement.subst_var(|v| match v {
                RefinedTypeVar::Value => chc::Term::var(RefinedTypeVar::Value),
                RefinedTypeVar::Free(v) => f(v).map_var(RefinedTypeVar::Free),
            }),
        }
    }

    pub fn map_var<F, W>(self, mut f: F) -> RefinedType<W>
    where
        F: FnMut(FV) -> W,
    {
        RefinedType {
            ty: self.ty,
            refinement: self.refinement.map_var(|v| match v {
                RefinedTypeVar::Value => RefinedTypeVar::Value,
                RefinedTypeVar::Free(v) => RefinedTypeVar::Free(f(v)),
            }),
        }
    }

    pub fn to_free_refinement<F>(&self, value_var_fn: F) -> chc::Atom<FV>
    where
        FV: Clone,
        F: Fn() -> FV,
    {
        self.refinement.clone().map_var(|v| match v {
            RefinedTypeVar::Value => value_var_fn(),
            RefinedTypeVar::Free(v) => v,
        })
    }

    pub fn is_refined(&self) -> bool {
        !self.refinement.is_top()
    }
}

impl RefinedType<Closed> {
    pub fn unrefined(ty: Type) -> Self {
        RefinedType::new(ty, chc::Atom::top())
    }

    pub fn vacuous<FV>(self) -> RefinedType<FV> {
        self.map_var(|v| match v {})
    }
}
