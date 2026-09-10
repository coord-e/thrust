//! Data structures for type parameters and substitutions.

use std::collections::BTreeMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;

use super::{Closed, RefinedType};

rustc_index::newtype_index! {
    /// An index representing a type parameter.
    ///
    /// ## Note on indexing of type parameters
    ///
    /// The index of [`rustc_middle::ty::ParamTy`] is based on all generic parameters in
    /// the definition, including lifetimes. Given the following definition:
    ///
    /// ```rust
    /// struct X<'a, T> { f: &'a T }
    /// ```
    ///
    /// The type of field `f` is `&T1` (not `&T0`) in MIR. However, in Thrust, we ignore lifetime
    /// parameters and the index of [`rty::ParamType`](super::ParamType) is based on type parameters only, giving `f`
    /// the type `&T0`. [`TypeBuilder`](crate::refine::TypeBuilder) takes care of this difference when translating MIR
    /// types to Thrust types.
    #[orderable]
    #[debug_format = "T{}"]
    pub struct TypeParamIdx { }
}

impl std::fmt::Display for TypeParamIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "T{}", self.index())
    }
}

impl<'a, D> Pretty<'a, D, termcolor::ColorSpec> for &TypeParamIdx
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator
            .as_string(self)
            .annotate(TypeParamIdx::color_spec())
    }
}

impl TypeParamIdx {
    fn color_spec() -> termcolor::ColorSpec {
        termcolor::ColorSpec::new()
    }
}

pub type RefinedTypeArgs<T = Closed> = IndexVec<TypeParamIdx, RefinedType<T>>;

/// A substitution for type parameters that maps type parameters to refinement types.
#[derive(Debug, Clone)]
pub struct TypeParamSubst<T> {
    subst: BTreeMap<TypeParamIdx, RefinedType<T>>,
}

impl<T> Default for TypeParamSubst<T> {
    fn default() -> Self {
        Self {
            subst: Default::default(),
        }
    }
}

impl<T> From<RefinedTypeArgs<T>> for TypeParamSubst<T> {
    fn from(params: RefinedTypeArgs<T>) -> Self {
        let subst = params.into_iter_enumerated().collect();
        Self { subst }
    }
}

impl<T> std::ops::Index<TypeParamIdx> for TypeParamSubst<T> {
    type Output = RefinedType<T>;

    fn index(&self, idx: TypeParamIdx) -> &Self::Output {
        &self.subst[&idx]
    }
}

impl<T> TypeParamSubst<T> {
    pub fn get(&self, idx: TypeParamIdx) -> Option<&RefinedType<T>> {
        self.subst.get(&idx)
    }

    pub fn strip_refinement(self) -> TypeParamSubst<Closed> {
        TypeParamSubst {
            subst: self
                .subst
                .into_iter()
                .map(|(idx, ty)| (idx, RefinedType::unrefined(ty.strip_refinement())))
                .collect(),
        }
    }
}

impl TypeParamSubst<Closed> {
    pub fn vacuous<T>(self) -> TypeParamSubst<T> {
        TypeParamSubst {
            subst: self
                .subst
                .into_iter()
                .map(|(idx, ty)| (idx, ty.vacuous()))
                .collect(),
        }
    }
}
