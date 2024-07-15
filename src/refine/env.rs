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

    pub fn is_temp(&self) -> bool {
        matches!(self, Var::Temp(_))
    }
}

#[derive(Debug, Clone, Copy)]
enum FlowBinding {
    Mut(TempVarIdx, TempVarIdx),
    Box(TempVarIdx),
}

impl std::fmt::Display for FlowBinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FlowBinding::Mut(current, final_) => write!(f, "mut <{:?}, {:?}>", current, final_),
            FlowBinding::Box(current) => write!(f, "box <{:?}>", current),
        }
    }
}

#[derive(Debug, Clone)]
enum TempVarBinding {
    Flow(FlowBinding),
    Type(rty::RefinedType<Var>),
}

impl TempVarBinding {
    fn to_flow(&self) -> Option<FlowBinding> {
        match self {
            TempVarBinding::Flow(binding) => Some(*binding),
            _ => None,
        }
    }

    fn as_type(&self) -> Option<&rty::RefinedType<Var>> {
        match self {
            TempVarBinding::Type(rty) => Some(rty),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    locals: HashMap<Local, rty::RefinedType<Var>>,
    flow_locals: HashMap<Local, FlowBinding>,
    temp_vars: IndexVec<TempVarIdx, TempVarBinding>,
    unbound_assumptions: Vec<chc::Atom<Var>>,
}

impl Env {
    pub fn push_temp_var(&mut self, ty: rty::Type) -> TempVarIdx {
        self.temp_vars.push(TempVarBinding::Type(
            rty::RefinedType::unrefined(ty).vacuous(),
        ))
    }

    // when var = Var::Temp(idx), idx must be temp_vars.next_index() in bind_{own,mut,var}
    fn bind_own(&mut self, var: Var, ty: rty::PointerType, refinement: rty::Refinement<Var>) {
        // note that the given var is unbound here, so be careful of using indices around temp_vars
        let current_refinement = refinement.subst_var(|v| match v {
            rty::RefinedTypeVar::Value => {
                chc::Term::box_(chc::Term::var(rty::RefinedTypeVar::Value))
            }
            rty::RefinedTypeVar::Free(v) => chc::Term::var(rty::RefinedTypeVar::Free(v)),
        });
        let current = match var {
            Var::Local(local) => {
                let current = self.temp_vars.next_index();
                self.flow_locals.insert(local, FlowBinding::Box(current));
                current
            }
            Var::Temp(temp) => {
                // next_index must be `temp`
                let current = self.temp_vars.next_index() + 1;
                let binding = FlowBinding::Box(current);
                assert_eq!(temp, self.temp_vars.push(TempVarBinding::Flow(binding)));
                current
            }
        };
        self.bind_var(
            current.into(),
            rty::RefinedType::new((*ty.elem).into(), current_refinement),
        );
    }

    fn bind_mut(&mut self, var: Var, ty: rty::PointerType, refinement: rty::Refinement<Var>) {
        // note that the given var is unbound here, so be careful of using indices around temp_vars
        let next_index = self.temp_vars.next_index();
        let (final_, current) = if var.is_temp() {
            (next_index + 1, next_index + 2)
        } else {
            (next_index, next_index + 1)
        };
        let current_refinement = refinement.subst_var(|v| match v {
            rty::RefinedTypeVar::Value => chc::Term::mut_(
                chc::Term::var(rty::RefinedTypeVar::Value),
                chc::Term::var(rty::RefinedTypeVar::Free(final_.into())),
            ),
            rty::RefinedTypeVar::Free(v) => chc::Term::var(rty::RefinedTypeVar::Free(v)),
        });
        let binding = FlowBinding::Mut(current, final_);
        match var {
            Var::Local(local) => {
                self.flow_locals.insert(local, binding);
            }
            Var::Temp(temp) => {
                assert_eq!(temp, self.temp_vars.push(TempVarBinding::Flow(binding)));
            }
        };
        assert_eq!(
            final_,
            self.temp_vars.push(TempVarBinding::Type(
                rty::RefinedType::unrefined(*ty.elem.clone()).vacuous()
            ))
        );
        self.bind_var(
            current.into(),
            rty::RefinedType::new((*ty.elem).into(), current_refinement),
        );
    }

    fn bind_var(&mut self, var: Var, rty: rty::RefinedType<Var>) {
        match rty.ty {
            rty::Type::Pointer(ty) if ty.is_own() => self.bind_own(var, ty, rty.refinement),
            rty::Type::Pointer(ty) if ty.is_mut() => self.bind_mut(var, ty, rty.refinement),
            _ => match var {
                Var::Local(local) => {
                    self.locals.insert(local, rty);
                }
                Var::Temp(temp) => {
                    assert_eq!(temp, self.temp_vars.push(TempVarBinding::Type(rty)));
                }
            },
        }
    }

    pub fn bind(&mut self, local: Local, rty: rty::RefinedType<Var>) {
        let rty_disp = rty.clone();
        self.bind_var(local.into(), rty);
        tracing::debug!(local = ?local, rty = %rty_disp.display(), term = %self.local_type(local).1.display(), "bind");
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
                self.temp_vars
                    .iter_enumerated()
                    .filter_map(|(idx, b)| b.as_type().map(|rty| (Var::Temp(idx), &rty.ty))),
            )
            .map(|(v, ty)| (v, ty.to_sort()))
    }

    pub fn assumptions(&self) -> impl Iterator<Item = chc::Atom<Var>> + '_ {
        self.locals
            .iter()
            .map(|(local, rty)| (Var::Local(*local), rty))
            .chain(
                self.temp_vars
                    .iter_enumerated()
                    .filter_map(|(idx, b)| b.as_type().map(|rty| (Var::Temp(idx), rty))),
            )
            .filter_map(|(var, rty)| rty.is_refined().then(|| rty.to_free_refinement(|| var)))
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

    fn flow_binding(&self, var: Var) -> Option<FlowBinding> {
        match var {
            Var::Local(local) => self.flow_locals.get(&local).copied(),
            Var::Temp(temp) => self.temp_vars[temp].to_flow(),
        }
    }

    fn insert_flow_binding(&mut self, var: Var, binding: FlowBinding) {
        match var {
            Var::Local(local) => {
                self.flow_locals.insert(local, binding);
            }
            Var::Temp(temp) => {
                self.temp_vars[temp] = TempVarBinding::Flow(binding);
            }
        }
    }

    fn var(&self, var: Var) -> Option<&rty::RefinedType<Var>> {
        match var {
            Var::Local(local) => self.locals.get(&local),
            Var::Temp(temp) => self.temp_vars[temp].as_type(),
        }
    }

    fn var_type(&self, var: Var) -> (rty::Type, chc::Term<Var>) {
        // TODO: should this driven by type as the rule does?
        match self.flow_binding(var) {
            Some(FlowBinding::Box(current)) => {
                let (current_ty, current_term) = self.var_type(current.into());
                let term = chc::Term::box_(current_term);
                (rty::PointerType::own(current_ty).into(), term)
            }
            Some(FlowBinding::Mut(current, final_)) => {
                let (current_ty, current_term) = self.var_type(current.into());
                let (_final_ty, final_term) = self.var_type(final_.into());
                // TODO: check current_ty = final_ty

                let term = chc::Term::mut_(current_term, final_term);
                (rty::PointerType::mut_to(current_ty).into(), term)
            }
            None => {
                let rty = self.var(var).expect("unbound var");
                (rty.ty.clone(), chc::Term::var(var))
            }
        }
    }

    pub fn local_type(&self, local: Local) -> (rty::Type, chc::Term<Var>) {
        self.var_type(local.into())
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

    fn borrow_var(&mut self, var: Var, prophecy: TempVarIdx) -> (rty::Type, chc::Term<Var>) {
        match self.flow_binding(var).expect("borrowing unbound var") {
            FlowBinding::Box(x) => {
                let (inner_ty, inner_term) = self.var_type(x.into());
                self.insert_flow_binding(var, FlowBinding::Box(prophecy));
                let term = chc::Term::mut_(inner_term, chc::Term::var(prophecy.into()));
                (rty::PointerType::mut_to(inner_ty).into(), term)
            }
            FlowBinding::Mut(x1, x2) => {
                // TODO: check x2 ty
                let (inner_ty, x1_term) = self.var_type(x1.into());
                self.insert_flow_binding(var, FlowBinding::Mut(prophecy, x2));
                let term = chc::Term::mut_(x1_term, chc::Term::var(prophecy.into()));
                (rty::PointerType::mut_to(inner_ty).into(), term)
            }
        }
    }

    fn locate_place(&self, place: Place<'_>) -> Var {
        let mut var = place.local.into();

        for elem in place.projection {
            if !matches!(elem, PlaceElem::Deref) {
                unimplemented!();
            }

            var = match self.flow_binding(var).expect("deref unbound var") {
                FlowBinding::Box(x) => x.into(),
                FlowBinding::Mut(x, _) => x.into(),
            };
        }

        var
    }

    pub fn borrow_place(
        &mut self,
        place: Place<'_>,
        prophecy_var: TempVarIdx,
    ) -> (rty::Type, chc::Term<Var>) {
        let var = self.locate_place(place);
        self.borrow_var(var, prophecy_var)
    }
}

#[derive(Debug, Clone)]
enum Path {
    Local(Local),
    Deref(Box<Path>),
}

impl<'tcx> From<Place<'tcx>> for Path {
    fn from(place: Place<'tcx>) -> Self {
        place
            .projection
            .into_iter()
            .fold(Path::Local(place.local), |path, elem| match elem {
                PlaceElem::Deref => Path::Deref(Box::new(path)),
                _ => unimplemented!(),
            })
    }
}

impl Path {
    fn deref(self) -> Self {
        Path::Deref(Box::new(self))
    }
}

impl Env {
    fn path_type(&self, path: &Path) -> (rty::Type, chc::Term<Var>) {
        match path {
            Path::Local(local) => self.local_type(*local),
            Path::Deref(path) => {
                let (ty, term) = self.path_type(path);
                let ty = ty.into_pointer().unwrap();
                (*ty.elem, ty.kind.deref_term(term))
            }
        }
    }

    pub fn place_type(&self, place: Place) -> (rty::Type, chc::Term<Var>) {
        self.path_type(&place.into())
    }

    fn drop_path(&mut self, path: &Path) {
        let (ty, term) = self.path_type(path);
        if ty.is_mut() {
            self.assume(term.clone().mut_final().equal_to(term.mut_current()));
        } else if ty.is_own() {
            self.drop_path(&path.clone().deref())
        }
    }

    pub fn drop_local(&mut self, local: Local) {
        self.drop_path(&Path::Local(local))
    }
}
