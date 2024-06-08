use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, Local, Operand, Place, PlaceElem};
use rustc_middle::ty as mir_ty;

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
enum FlowLocalBinding {
    Mut(TempVarIdx, TempVarIdx),
    Box(TempVarIdx),
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    locals: HashMap<Local, rty::RefinedType<Var>>,
    tmp_vars: IndexVec<TempVarIdx, rty::Type>,
    unbound_assumptions: Vec<chc::Atom<Var>>,

    flow_locals: HashMap<Local, FlowLocalBinding>,
}

impl Env {
    pub fn push_temp_var(&mut self, ty: rty::Type) -> TempVarIdx {
        self.tmp_vars.push(ty)
    }

    fn bind_own(&mut self, local: Local, ty: rty::PointerType, refinement: rty::Refinement<Var>) {
        let current = self.push_temp_var(*ty.elem);
        let assumption = refinement.subst_var(|v| match v {
            rty::RefinedTypeVar::Value => chc::Term::box_(chc::Term::var(current.into())),
            rty::RefinedTypeVar::Free(v) => chc::Term::var(v),
        });
        self.assume(assumption);
        self.flow_locals
            .insert(local, FlowLocalBinding::Box(current));
    }

    fn bind_mut(&mut self, local: Local, ty: rty::PointerType, refinement: rty::Refinement<Var>) {
        let current = self.push_temp_var(*ty.elem.clone());
        let final_ = self.push_temp_var(*ty.elem);
        let assumption = refinement.subst_var(|v| match v {
            rty::RefinedTypeVar::Value => chc::Term::mut_(
                chc::Term::var(current.into()),
                chc::Term::var(final_.into()),
            ),
            rty::RefinedTypeVar::Free(v) => chc::Term::var(v),
        });
        self.assume(assumption);
        self.flow_locals
            .insert(local, FlowLocalBinding::Mut(current, final_));
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

    pub fn assume(&mut self, assumption: chc::Atom<Var>) {
        tracing::debug!(assumption = %assumption.display(), "assume");
        self.unbound_assumptions.push(assumption);
    }

    pub fn extend_assumptions(&mut self, assumptions: Vec<chc::Atom<Var>>) {
        self.unbound_assumptions.extend(assumptions);
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
                    .then(|| rty.to_free_refinement(|| Var::Local(*local)))
            })
            .chain(self.unbound_assumptions.iter().cloned())
    }

    pub fn build_clause(&self) -> chc::ClauseBuilder {
        let mut builder = chc::ClauseBuilder::default();
        for (v, sort) in self.dependencies() {
            builder.add_mapped_var(v, sort);
        }
        for assumption in self.assumptions() {
            builder.add_body(assumption.map_var(|v| builder.mapped_var(v)));
        }
        builder
    }

    pub fn contains_local(&self, local: Local) -> bool {
        self.locals.contains_key(&local) || self.flow_locals.contains_key(&local)
    }

    pub fn local_type(&self, local: Local) -> (rty::Type, chc::Term<Var>) {
        // TODO: should this driven by type?
        match self.flow_locals.get(&local).copied() {
            Some(FlowLocalBinding::Mut(current, final_)) => {
                let inner_ty = self.tmp_vars[current].clone();
                let term = chc::Term::mut_(
                    chc::Term::var(current.into()),
                    chc::Term::var(final_.into()),
                );
                (rty::PointerType::mut_to(inner_ty).into(), term)
            }
            Some(FlowLocalBinding::Box(current)) => {
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
                let ty = ty.into_pointer().unwrap();
                (*ty.elem, ty.kind.deref_term(term))
            })
    }

    pub fn operand_type(&self, operand: Operand<'_>) -> (rty::Type, chc::Term<Var>) {
        use mir::{interpret::Scalar, Const, ConstValue, Mutability};
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_type(place),
            Operand::Constant(operand) => {
                let Const::Val(val, ty) = operand.const_ else {
                    unimplemented!("const: {:?}", operand.const_);
                };
                match (ty.kind(), val) {
                    (mir_ty::TyKind::Int(_), ConstValue::Scalar(Scalar::Int(val))) => {
                        (rty::Type::int(), chc::Term::int(val.try_to_i64().unwrap()))
                    }
                    (
                        mir_ty::TyKind::Ref(_, elem, Mutability::Not),
                        ConstValue::Slice { data, meta },
                    ) if matches!(elem.kind(), mir_ty::TyKind::Str) => {
                        let end = meta.try_into().unwrap();
                        let content = data
                            .inner()
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..end);
                        let content = std::str::from_utf8(content).unwrap();
                        (
                            rty::PointerType::immut_to(rty::Type::string()).into(),
                            chc::Term::box_(chc::Term::string(content.to_owned())),
                        )
                    }
                    _ => unimplemented!("const: {:?}, ty: {:?}", val, ty),
                }
            }
        }
    }

    pub fn borrow_local(
        &mut self,
        local: Local,
        prophecy_var: TempVarIdx,
    ) -> (rty::Type, chc::Term<Var>) {
        match self.flow_locals[&local] {
            FlowLocalBinding::Box(x) => {
                self.flow_locals
                    .insert(local, FlowLocalBinding::Box(prophecy_var));
                let term = chc::Term::mut_(
                    chc::Term::var(x.into()),
                    chc::Term::var(prophecy_var.into()),
                );
                (
                    rty::PointerType::mut_to(self.tmp_vars[x].clone()).into(),
                    term,
                )
            }
            FlowLocalBinding::Mut(x1, x2) => {
                self.flow_locals
                    .insert(local, FlowLocalBinding::Mut(prophecy_var, x2));
                let term = chc::Term::mut_(
                    chc::Term::var(x1.into()),
                    chc::Term::var(prophecy_var.into()),
                );
                (
                    rty::PointerType::mut_to(self.tmp_vars[x1].clone()).into(),
                    term,
                )
            }
        }
    }
}
