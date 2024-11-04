use std::collections::BTreeMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;

use crate::chc;

use super::{Closed, RefinedType};

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "T{}"]
    pub struct TypeParamIdx { }
}

impl std::fmt::Display for TypeParamIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "T{}", self.index())
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b TypeParamIdx
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

pub type TypeParams<T> = IndexVec<TypeParamIdx, RefinedType<T>>;

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

impl<T> From<TypeParams<T>> for TypeParamSubst<T> {
    fn from(params: TypeParams<T>) -> Self {
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
    pub fn singleton(idx: TypeParamIdx, ty: RefinedType<T>) -> Self {
        let mut subst = BTreeMap::default();
        subst.insert(idx, ty);
        Self { subst }
    }

    pub fn compose(&mut self, other: Self)
    where
        T: chc::Var,
    {
        for (idx, mut t1) in other.subst {
            t1.subst_ty_params(self);
            if let Some(t2) = self.subst.remove(&idx) {
                t1.refinement.extend(t2.refinement);
            }
            self.subst.insert(idx, t1);
        }
    }

    pub fn into_params<F>(mut self, expected_len: usize, mut default: F) -> TypeParams<T>
    where
        T: chc::Var,
        F: FnMut(TypeParamIdx) -> RefinedType<T>,
    {
        let mut params = TypeParams::new();
        for idx in 0..expected_len {
            let ty = self
                .subst
                .remove(&idx.into())
                .unwrap_or_else(|| default(idx.into()));
            params.push(ty);
        }
        params
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
