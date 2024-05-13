use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, Local, Operand, Place, PlaceElem};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty;

rustc_index::newtype_index! {
    #[debug_format = "t{}"]
    pub struct TempVarIdx { }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Var {
    Local(Local),
    Temp(TempVarIdx),
}

impl From<TempVarIdx> for Var {
    fn from(idx: TempVarIdx) -> Self {
        Var::Temp(idx)
    }
}

impl From<Local> for Var {
    fn from(local: Local) -> Self {
        Var::Local(local)
    }
}

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Local(local) => local.fmt(f),
            Var::Temp(idx) => idx.fmt(f),
        }
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b Var
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        allocator.as_string(self).annotate(Var::color_spec())
    }
}

impl Var {
    fn color_spec() -> termcolor::ColorSpec {
        termcolor::ColorSpec::new()
    }
}

#[derive(Debug, Clone, Copy)]
enum MutLocalBinding {
    Mut(TempVarIdx, TempVarIdx),
    Box(TempVarIdx),
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    locals: HashMap<Local, rty::RefinedType<Var>>,
    tmp_vars: IndexVec<TempVarIdx, rty::Type>,
    unbound_assumptions: Vec<chc::Atom<Var>>,

    mut_locals: HashMap<Local, MutLocalBinding>,
}

impl Env {
    pub fn clone_with_assumptions(&self, assumptions: Vec<chc::Atom<Var>>) -> Self {
        let mut env = self.clone();
        env.unbound_assumptions.extend(assumptions);
        env
    }

    pub fn clone_with_assumption(&self, assumption: chc::Atom<Var>) -> Self {
        let mut env = self.clone();
        env.unbound_assumptions.push(assumption);
        env
    }

    fn bind_own(&mut self, local: Local, ty: rty::PointerType, refinement: rty::Refinement<Var>) {
        let current = self.tmp_vars.push(*ty.elem);
        let assumption = refinement.subst_var(|v| match v {
            rty::RefinedTypeVar::Value => chc::Term::box_(chc::Term::var(current.into())),
            rty::RefinedTypeVar::Free(v) => chc::Term::var(v),
        });
        self.unbound_assumptions.push(assumption);
        self.mut_locals.insert(local, MutLocalBinding::Box(current));
    }

    fn bind_mut(&mut self, local: Local, ty: rty::PointerType, refinement: rty::Refinement<Var>) {
        let current = self.tmp_vars.push(*ty.elem.clone());
        let final_ = self.tmp_vars.push(*ty.elem);
        let assumption = refinement.subst_var(|v| match v {
            rty::RefinedTypeVar::Value => chc::Term::pair(
                chc::Term::var(current.into()),
                chc::Term::var(final_.into()),
            ),
            rty::RefinedTypeVar::Free(v) => chc::Term::var(v),
        });
        self.unbound_assumptions.push(assumption);
        self.mut_locals
            .insert(local, MutLocalBinding::Mut(current, final_));
    }

    pub fn bind(&mut self, local: Local, rty: rty::RefinedType<Var>) {
        tracing::debug!(local = ?local, rty = %rty.display(), "bind");
        match rty.ty {
            rty::Type::Pointer(ty) if ty.is_own() => self.bind_own(local, ty, rty.refinement),
            rty::Type::Pointer(ty) if ty.is_mut() => self.bind_mut(local, ty, rty.refinement),
            _ => {
                self.locals.insert(local, rty);
            }
        }
    }

    pub fn dependencies(&self) -> impl Iterator<Item = (Var, chc::Sort)> + '_ {
        // TODO: consider cloning here again
        self.locals
            .iter()
            .map(|(local, rty)| (Var::Local(*local), &rty.ty))
            .chain(
                self.tmp_vars
                    .iter_enumerated()
                    .map(|(idx, ty)| (Var::Temp(idx), ty)),
            )
            .filter_map(|(v, ty)| ty.clone().to_sort().map(|sort| (v, sort)))
    }

    pub fn assumptions(&self) -> impl Iterator<Item = chc::Atom<Var>> + '_ {
        self.locals
            .iter()
            .filter_map(|(local, rty)| {
                rty.is_refined()
                    .then(|| rty.to_free_refinement(Var::Local(*local)))
            })
            .chain(self.unbound_assumptions.iter().cloned())
    }

    pub fn build_clause(&self) -> chc::ClauseBuilder {
        let mut builder = chc::ClauseBuilder::default();
        for (v, sort) in self.dependencies() {
            builder.add_dependency(rty::RefinedTypeVar::Free(v), sort);
        }
        for assumption in self.assumptions() {
            // TODO: can't we remove this map_var?
            let assumption = assumption.map_var(|v| rty::RefinedTypeVar::Free(v));
            builder.add_body(assumption);
        }
        builder
    }

    pub fn contains_local(&self, local: Local) -> bool {
        self.locals.contains_key(&local) || self.mut_locals.contains_key(&local)
    }

    pub fn local_type(&self, local: Local) -> (rty::Type, chc::Term<Var>) {
        // TODO: should this driven by type?
        match self.mut_locals.get(&local).copied() {
            Some(MutLocalBinding::Mut(current, final_)) => {
                let inner_ty = self.tmp_vars[current].clone();
                let term = chc::Term::pair(
                    chc::Term::var(current.into()),
                    chc::Term::var(final_.into()),
                );
                (rty::PointerType::mut_to(inner_ty).into(), term)
            }
            Some(MutLocalBinding::Box(current)) => {
                let inner_ty = self.tmp_vars[current].clone();
                let term = chc::Term::box_(chc::Term::var(current.into()));
                (rty::PointerType::own(inner_ty).into(), term)
            }
            None => {
                let rty = self.locals.get(&local).expect("unbound local");
                (rty.ty.clone(), chc::Term::var(Var::Local(local)))
            }
        }
    }

    pub fn place_type(&self, place: Place) -> (rty::Type, chc::Term<Var>) {
        let (inner_ty, inner_term) = self.local_type(place.local);
        place
            .projection
            .iter()
            .fold((inner_ty, inner_term), |(ty, term), proj| {
                if !matches!(proj, PlaceElem::Deref) {
                    unimplemented!();
                }
                (ty.deref(), term.proj(0))
            })
    }

    pub fn operand_type(&self, operand: Operand<'_>) -> (rty::Type, chc::Term<Var>) {
        use mir::{interpret::Scalar, Const, ConstValue};
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_type(place),
            Operand::Constant(operand) => {
                let Const::Val(ConstValue::Scalar(Scalar::Int(val)), _) = operand.const_ else {
                    unimplemented!();
                };
                (rty::Type::Int, chc::Term::int(val.try_to_i64().unwrap()))
            }
        }
    }
}
