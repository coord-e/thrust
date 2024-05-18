use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;

use crate::chc;

mod template;
pub use template::{Template, TemplateBuilder};

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
pub enum Type {
    Unit,
    Int,
    Bool,
    Pointer(PointerType),
    Function(FunctionType),
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
            Type::Pointer(ty) => ty.pretty(allocator),
            Type::Function(ty) => ty.pretty(allocator),
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

    pub fn deref(self) -> Type {
        if let Type::Pointer(ty) = self {
            *ty.elem
        } else {
            panic!("invalid deref");
        }
    }

    pub fn as_function(&self) -> Option<&FunctionType> {
        match self {
            Type::Function(ty) => Some(ty),
            _ => None,
        }
    }

    // XXX: this is something like 'logically meaningful to reason about'
    // and better naming is needed
    pub fn to_sort(&self) -> Option<chc::Sort> {
        match self {
            Type::Unit => None,
            Type::Int => Some(chc::Sort::int()),
            Type::Bool => Some(chc::Sort::bool()),
            Type::Pointer(ty) => {
                let elem_sort = ty.elem.to_sort()?;
                let sort = match ty.kind {
                    PointerKind::Ref(RefKind::Immut) | PointerKind::Own => {
                        chc::Sort::box_(elem_sort)
                    }
                    PointerKind::Ref(RefKind::Mut) => chc::Sort::pair(elem_sort.clone(), elem_sort),
                };
                Some(sort)
            }
            Type::Function { .. } => None,
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
