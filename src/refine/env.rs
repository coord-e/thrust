use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, Local, Operand, Place, PlaceElem};
use rustc_middle::ty as mir_ty;
use rustc_target::abi::VariantIdx;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty;

const BIND_EXPANSION_DEPTH_LIMIT: usize = 10;

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

#[derive(Debug, Clone)]
enum FlowBinding {
    Mut(TempVarIdx, TempVarIdx),
    Box(TempVarIdx),
    Tuple(Vec<TempVarIdx>),
    Enum {
        discr: TempVarIdx,
        variants: IndexVec<VariantIdx, TempVarIdx>,
        sym: chc::DatatypeSymbol,
        matcher_pred: chc::PredVarId,
    },
}

impl std::fmt::Display for FlowBinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FlowBinding::Mut(current, final_) => write!(f, "mut <{:?}, {:?}>", current, final_),
            FlowBinding::Box(current) => write!(f, "box <{:?}>", current),
            FlowBinding::Tuple(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i == 0 && ts.len() != 1 {
                        write!(f, "{:?}", t)?;
                    } else {
                        write!(f, ", {:?}", t)?;
                    }
                }
                write!(f, ")")
            }
            FlowBinding::Enum {
                discr,
                variants,
                sym,
                ..
            } => {
                write!(f, "#{:?} ", discr)?;
                for (i, v) in variants.iter_enumerated() {
                    if i.index() == 0 {
                        write!(f, "{}::{:?}({:?})", sym, i, v)?;
                    } else {
                        write!(f, " | {}::{:?}({:?})", sym, i, v)?;
                    }
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
enum TempVarBinding {
    Flow(FlowBinding),
    Type(rty::RefinedType<Var>),
}

impl TempVarBinding {
    fn as_flow(&self) -> Option<&FlowBinding> {
        match self {
            TempVarBinding::Flow(binding) => Some(binding),
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum PlaceTypeVar {
    Var(Var),
    Existential(rty::ExistentialVarIdx),
}

impl From<Var> for PlaceTypeVar {
    fn from(v: Var) -> Self {
        PlaceTypeVar::Var(v)
    }
}

impl From<TempVarIdx> for PlaceTypeVar {
    fn from(idx: TempVarIdx) -> Self {
        PlaceTypeVar::Var(Var::Temp(idx))
    }
}

impl From<rty::ExistentialVarIdx> for PlaceTypeVar {
    fn from(ev: rty::ExistentialVarIdx) -> Self {
        PlaceTypeVar::Existential(ev)
    }
}

impl From<PlaceTypeVar> for rty::RefinedTypeVar<Var> {
    fn from(v: PlaceTypeVar) -> Self {
        match v {
            PlaceTypeVar::Var(v) => rty::RefinedTypeVar::Free(v),
            PlaceTypeVar::Existential(ev) => rty::RefinedTypeVar::Existential(ev),
        }
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b PlaceTypeVar
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        match self {
            PlaceTypeVar::Var(v) => v.pretty(allocator),
            PlaceTypeVar::Existential(ev) => ev.pretty(allocator),
        }
    }
}

impl PlaceTypeVar {
    pub fn into_var(self) -> Option<Var> {
        match self {
            PlaceTypeVar::Var(v) => Some(v),
            _ => None,
        }
    }

    pub fn shift_existential(self, amount: usize) -> Self {
        match self {
            PlaceTypeVar::Var(v) => PlaceTypeVar::Var(v),
            PlaceTypeVar::Existential(ev) => PlaceTypeVar::Existential(ev + amount),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PlaceType {
    pub ty: rty::Type<Var>,
    pub existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
    pub term: chc::Term<PlaceTypeVar>,
    pub conds: Vec<chc::Atom<PlaceTypeVar>>,
}

impl From<PlaceType> for rty::RefinedType<Var> {
    fn from(ty: PlaceType) -> Self {
        let PlaceType {
            ty,
            existentials,
            term,
            conds,
        } = ty;
        let mut atoms: Vec<_> = conds.into_iter().map(|a| a.map_var(Into::into)).collect();
        atoms.push(chc::Term::var(rty::RefinedTypeVar::Value).equal_to(term.map_var(Into::into)));
        let refinement = rty::Refinement::new(existentials, atoms);
        rty::RefinedType::new(ty, refinement)
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b PlaceType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let ty = self
            .ty
            .pretty(allocator)
            .append(self.term.pretty(allocator).brackets());
        let ty_and_atoms = if self.conds.is_empty() {
            ty
        } else {
            let atoms = allocator.intersperse(
                &self.conds,
                allocator
                    .text("∧")
                    .enclose(allocator.line(), allocator.space()),
            );
            ty.append(allocator.line())
                .append(allocator.text("|"))
                .append(allocator.space())
                .append(atoms)
        };
        if self.existentials.is_empty() {
            if self.conds.is_empty() {
                ty_and_atoms.group()
            } else {
                ty_and_atoms.braces().group()
            }
        } else {
            let existentials = allocator
                .intersperse(
                    self.existentials
                        .iter_enumerated()
                        .map(|(v, s)| v.pretty(allocator).append(allocator.text(":")).append(s)),
                    allocator.text(",").append(allocator.line()),
                )
                .group();
            allocator
                .text("∃")
                .append(existentials.nest(2))
                .append(allocator.text("."))
                .append(allocator.line().append(ty_and_atoms).nest(2))
                .braces()
                .group()
        }
    }
}

impl PlaceType {
    pub fn with_ty_and_term(ty: rty::Type<Var>, term: chc::Term<Var>) -> Self {
        PlaceType {
            ty,
            existentials: IndexVec::new(),
            term: term.map_var(PlaceTypeVar::Var),
            conds: Vec::new(),
        }
    }

    pub fn into_assumption<F>(self, term_to_atom: F) -> UnboundAssumption
    where
        F: FnOnce(chc::Term<PlaceTypeVar>) -> chc::Atom<PlaceTypeVar>,
    {
        let PlaceType {
            ty: _,
            existentials,
            term,
            mut conds,
        } = self;
        conds.push(term_to_atom(term));
        UnboundAssumption {
            existentials,
            conds,
        }
    }

    pub fn deref(self) -> PlaceType {
        let PlaceType {
            ty: inner_ty,
            mut existentials,
            term: inner_term,
            mut conds,
        } = self;
        let inner_ty = inner_ty.into_pointer().unwrap();
        let rty::RefinedType { ty, refinement } = *inner_ty.elem;
        let rty::Refinement {
            existentials: inner_existentials,
            atoms: inner_atoms,
        } = refinement;
        let value_var_ex = existentials.push(ty.to_sort());
        let term = chc::Term::var(value_var_ex.into());
        conds.push(term.clone().equal_to(inner_ty.kind.deref_term(inner_term)));
        conds.extend(inner_atoms.into_iter().map(|a| {
            a.map_var(|v| match v {
                rty::RefinedTypeVar::Value => PlaceTypeVar::Existential(value_var_ex),
                rty::RefinedTypeVar::Existential(ev) => {
                    PlaceTypeVar::Existential(ev + existentials.len())
                }
                rty::RefinedTypeVar::Free(v) => PlaceTypeVar::Var(v),
            })
        }));
        existentials.extend(inner_existentials);
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn tuple_proj(self, idx: usize) -> PlaceType {
        let PlaceType {
            ty: inner_ty,
            mut existentials,
            term: inner_term,
            mut conds,
        } = self;
        let inner_ty = inner_ty.into_tuple().unwrap();
        let rty::RefinedType { ty, refinement } = inner_ty.elems[idx].clone();
        let rty::Refinement {
            existentials: inner_existentials,
            atoms: inner_atoms,
        } = refinement;
        let value_var_ex = existentials.push(ty.to_sort());
        let term = chc::Term::var(value_var_ex.into());
        conds.push(term.clone().equal_to(inner_term.tuple_proj(idx)));
        conds.extend(inner_atoms.into_iter().map(|a| {
            a.map_var(|v| match v {
                rty::RefinedTypeVar::Value => PlaceTypeVar::Existential(value_var_ex),
                rty::RefinedTypeVar::Existential(ev) => {
                    PlaceTypeVar::Existential(ev + existentials.len())
                }
                rty::RefinedTypeVar::Free(v) => PlaceTypeVar::Var(v),
            })
        }));
        existentials.extend(inner_existentials);
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn downcast(
        self,
        idx: VariantIdx,
        enum_defs: &HashMap<chc::DatatypeSymbol, rty::EnumDatatypeDef>,
    ) -> PlaceType {
        let PlaceType {
            ty: inner_ty,
            mut existentials,
            term: inner_term,
            mut conds,
        } = self;
        let inner_ty = inner_ty.into_enum().unwrap();
        let def = &enum_defs[&inner_ty.symbol];
        let variant = &def.variants[idx];
        let value_var_ex = existentials.push(variant.ty.to_sort());
        conds.push(
            chc::Term::datatype_ctor(
                def.name.clone(),
                variant.name.clone(),
                vec![chc::Term::var(value_var_ex.into())],
            )
            .equal_to(inner_term),
        );
        let ty = variant.ty.clone().vacuous();
        let term = chc::Term::var(value_var_ex.into());
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn boxed(self) -> PlaceType {
        let PlaceType {
            ty: inner_ty,
            existentials,
            term: inner_term,
            conds,
        } = self;
        let term = chc::Term::box_(inner_term);
        let ty = rty::PointerType::own(inner_ty).into();
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn replace<F>(self, f: F) -> PlaceType
    where
        F: FnOnce(
            rty::Type<Var>,
            chc::Term<PlaceTypeVar>,
        ) -> (rty::Type<Var>, chc::Term<PlaceTypeVar>),
    {
        let PlaceType {
            ty,
            existentials,
            term,
            conds,
        } = self;
        let (ty, term) = f(ty, term);
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn merge_into_assumption<F>(self, other: PlaceType, f: F) -> UnboundAssumption
    where
        F: FnOnce(chc::Term<PlaceTypeVar>, chc::Term<PlaceTypeVar>) -> chc::Atom<PlaceTypeVar>,
    {
        let PlaceType {
            ty: _ty1,
            mut existentials,
            term: term1,
            mut conds,
        } = self;
        let PlaceType {
            ty: _ty2,
            existentials: evs2,
            term: term2,
            conds: conds2,
        } = other;
        let atom = f(
            term1,
            term2.map_var(|v| v.shift_existential(existentials.len())),
        );
        conds.extend(
            conds2
                .into_iter()
                .map(|c| c.map_var(|v| v.shift_existential(existentials.len()))),
        );
        conds.push(atom);
        existentials.extend(evs2);
        UnboundAssumption {
            existentials,
            conds,
        }
    }

    pub fn merge<F>(self, other: PlaceType, f: F) -> PlaceType
    where
        F: FnOnce(
            (rty::Type<Var>, chc::Term<PlaceTypeVar>),
            (rty::Type<Var>, chc::Term<PlaceTypeVar>),
        ) -> (rty::Type<Var>, chc::Term<PlaceTypeVar>),
    {
        let PlaceType {
            ty: ty1,
            mut existentials,
            term: term1,
            mut conds,
        } = self;
        let PlaceType {
            ty: ty2,
            existentials: evs2,
            term: term2,
            conds: conds2,
        } = other;
        let (ty, term) = f(
            (ty1, term1),
            (
                ty2,
                term2.map_var(|v| v.shift_existential(existentials.len())),
            ),
        );
        conds.extend(
            conds2
                .into_iter()
                .map(|c| c.map_var(|v| v.shift_existential(existentials.len()))),
        );
        existentials.extend(evs2);
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn mut_with_proph_term(self, proph: chc::Term<Var>) -> PlaceType {
        let ty = self.ty.clone();
        self.mut_with(PlaceType::with_ty_and_term(ty, proph))
    }

    pub fn mut_with(self, proph: PlaceType) -> PlaceType {
        self.merge(proph, |(ty1, term1), (_, term2)|
            // TODO: check ty1 = ty2
            (rty::PointerType::mut_to(ty1).into(), chc::Term::mut_(term1, term2)))
    }

    pub fn tuple(tys: Vec<PlaceType>) -> PlaceType {
        #[derive(Default)]
        struct State {
            tys: Vec<rty::Type<Var>>,
            terms: Vec<chc::Term<PlaceTypeVar>>,
            existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
            conds: Vec<chc::Atom<PlaceTypeVar>>,
        }
        let State {
            tys,
            terms,
            existentials,
            conds,
        } = tys
            .into_iter()
            .fold(Default::default(), |mut st: State, ty| {
                let PlaceType {
                    ty,
                    existentials,
                    term,
                    conds,
                } = ty;
                st.tys.push(ty);
                st.terms
                    .push(term.map_var(|v| v.shift_existential(st.existentials.len())));
                st.conds.extend(
                    conds
                        .into_iter()
                        .map(|c| c.map_var(|v| v.shift_existential(st.existentials.len()))),
                );
                st.existentials.extend(existentials);
                st
            });
        let ty = rty::TupleType::new(tys).into();
        let term = chc::Term::tuple(terms);
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn enum_(
        discr: TempVarIdx,
        sym: chc::DatatypeSymbol,
        tys: IndexVec<VariantIdx, PlaceType>,
        matcher_pred: chc::PredVarId,
    ) -> PlaceType {
        #[derive(Default)]
        struct State {
            existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
            terms: Vec<chc::Term<PlaceTypeVar>>,
            conds: Vec<chc::Atom<PlaceTypeVar>>,
        }
        let State {
            mut existentials,
            terms,
            mut conds,
        } = tys
            .into_iter()
            .fold(Default::default(), |mut st: State, ty| {
                let PlaceType {
                    ty: _,
                    existentials,
                    term,
                    conds,
                } = ty;
                st.terms
                    .push(term.map_var(|v| v.shift_existential(st.existentials.len())));
                st.conds.extend(
                    conds
                        .into_iter()
                        .map(|c| c.map_var(|v| v.shift_existential(st.existentials.len()))),
                );
                st.existentials.extend(existentials);
                st
            });
        let ty: rty::Type<_> = rty::EnumType::new(sym.clone()).into();
        let value_var_ev = existentials.push(ty.to_sort());
        let term = chc::Term::var(value_var_ev.into());
        let mut pred_args = terms;
        pred_args.push(chc::Term::var(value_var_ev.into()));
        conds.push(chc::Atom::new(matcher_pred.into(), pred_args));
        conds.push(
            chc::Term::var(discr.into()).equal_to(chc::Term::datatype_discr(
                sym,
                chc::Term::var(value_var_ev.into()),
            )),
        );
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }
}

#[derive(Debug, Clone)]
pub struct UnboundAssumption {
    pub existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
    pub conds: Vec<chc::Atom<PlaceTypeVar>>,
}

impl From<chc::Atom<Var>> for UnboundAssumption {
    fn from(atom: chc::Atom<Var>) -> Self {
        let existentials = IndexVec::new();
        let conds = vec![atom.map_var(Into::into)];
        UnboundAssumption {
            existentials,
            conds,
        }
    }
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b UnboundAssumption
where
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
            &self.conds,
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

impl UnboundAssumption {
    pub fn new(
        existentials: IndexVec<rty::ExistentialVarIdx, chc::Sort>,
        conds: Vec<chc::Atom<PlaceTypeVar>>,
    ) -> Self {
        UnboundAssumption {
            existentials,
            conds,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Env {
    locals: HashMap<Local, rty::RefinedType<Var>>,
    flow_locals: HashMap<Local, FlowBinding>,
    temp_vars: IndexVec<TempVarIdx, TempVarBinding>,
    unbound_assumptions: Vec<UnboundAssumption>,

    enum_defs: HashMap<chc::DatatypeSymbol, rty::EnumDatatypeDef>,
}

impl rty::ClauseScope for Env {
    fn build_clause(&self) -> chc::ClauseBuilder {
        let mut builder = chc::ClauseBuilder::default();
        for (v, sort) in self.dependencies() {
            builder.add_mapped_var(v, sort);
        }
        for (var, rty) in self.vars() {
            let mut instantiator = rty
                .refinement
                .clone()
                .map_var(|v| builder.mapped_var(v))
                .instantiate();
            for (ev, sort) in rty.refinement.existentials() {
                let tv = builder.add_var(sort.clone());
                instantiator.existential(ev, tv);
            }
            instantiator.value_var(builder.mapped_var(var));
            for atom in instantiator.into_atoms() {
                builder.add_body(atom);
            }
        }
        for assumption in &self.unbound_assumptions {
            let mut evs = HashMap::new();
            for (ev, sort) in assumption.existentials.iter_enumerated() {
                let tv = builder.add_var(sort.clone());
                evs.insert(ev, tv);
            }
            for atom in &assumption.conds {
                builder.add_body(atom.clone().map_var(|v| match v {
                    PlaceTypeVar::Var(v) => builder.mapped_var(v),
                    PlaceTypeVar::Existential(ev) => evs[&ev],
                }));
            }
        }
        builder
    }
}

impl Env {
    pub fn new(enum_defs: HashMap<chc::DatatypeSymbol, rty::EnumDatatypeDef>) -> Self {
        Env {
            locals: HashMap::new(),
            flow_locals: HashMap::new(),
            temp_vars: IndexVec::new(),
            unbound_assumptions: Vec::new(),
            enum_defs,
        }
    }

    pub fn push_temp_var(&mut self, ty: rty::Type<Var>) -> TempVarIdx {
        self.temp_vars
            .push(TempVarBinding::Type(rty::RefinedType::unrefined(ty)))
    }

    // when var = Var::Temp(idx), idx must be temp_vars.next_index() in bind_*
    fn bind_own(
        &mut self,
        var: Var,
        ty: rty::PointerType<Var>,
        refinement: rty::Refinement<Var>,
        depth: usize,
    ) {
        // note that the given var is unbound here, so be careful of using indices around temp_vars
        let current_refinement = refinement
            .subst_value_var(|| chc::Term::box_(chc::Term::var(rty::RefinedTypeVar::Value)));
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
        let mut inner_ty = *ty.elem;
        inner_ty.extend_refinement(current_refinement);
        self.bind_impl(current.into(), inner_ty, depth + 1);
    }

    fn bind_mut(
        &mut self,
        var: Var,
        ty: rty::PointerType<Var>,
        refinement: rty::Refinement<Var>,
        depth: usize,
    ) {
        // note that the given var is unbound here, so be careful of using indices around temp_vars
        let next_index = self.temp_vars.next_index();
        let (final_, current) = if var.is_temp() {
            (next_index + 1, next_index + 2)
        } else {
            (next_index, next_index + 1)
        };
        let current_refinement = refinement.subst_value_var(|| {
            chc::Term::mut_(
                chc::Term::var(rty::RefinedTypeVar::Value),
                chc::Term::var(rty::RefinedTypeVar::Free(final_.into())),
            )
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
            self.temp_vars.push(TempVarBinding::Type(*ty.elem.clone()))
        );
        let mut inner_ty = *ty.elem;
        inner_ty.extend_refinement(current_refinement);
        self.bind_impl(current.into(), inner_ty, depth + 1);
    }

    fn bind_tuple(
        &mut self,
        var: Var,
        ty: rty::TupleType<Var>,
        refinement: rty::Refinement<Var>,
        depth: usize,
    ) {
        if let Var::Temp(temp) = var {
            // XXX: allocate `temp` once to invoke bind_var recursively
            let dummy = FlowBinding::Tuple(Vec::new());
            assert_eq!(temp, self.temp_vars.push(TempVarBinding::Flow(dummy)));
        }

        let mut xs = Vec::new();
        for elem in &ty.elems {
            let x = self.temp_vars.next_index();
            xs.push(x);
            self.bind_impl(x.into(), elem.clone(), depth + 1);
        }
        let assumption = {
            let tuple_ty = PlaceType::tuple(
                xs.iter()
                    .copied()
                    .map(|x| self.var_type(x.into()))
                    .collect(),
            );
            let mut existentials = tuple_ty.existentials;
            let conds = refinement
                .atoms
                .into_iter()
                .map(|a| {
                    a.subst_var(|v| match v {
                        rty::RefinedTypeVar::Value => tuple_ty.term.clone(),
                        rty::RefinedTypeVar::Free(v) => chc::Term::var(PlaceTypeVar::Var(v)),
                        rty::RefinedTypeVar::Existential(ev) => {
                            chc::Term::var(PlaceTypeVar::Existential(ev + existentials.len()))
                        }
                    })
                })
                .chain(tuple_ty.conds)
                .collect();
            existentials.extend(refinement.existentials);
            UnboundAssumption {
                existentials,
                conds,
            }
        };
        self.assume(assumption);
        let binding = FlowBinding::Tuple(xs.clone());
        match var {
            Var::Local(local) => {
                self.flow_locals.insert(local, binding);
            }
            Var::Temp(temp) => {
                self.temp_vars[temp] = TempVarBinding::Flow(binding);
            }
        }
    }

    fn bind_enum(
        &mut self,
        var: Var,
        ty: rty::EnumType,
        refinement: rty::Refinement<Var>,
        depth: usize,
    ) {
        if let Var::Temp(temp) = var {
            // XXX: allocate `temp` once to invoke bind_var recursively
            let dummy = FlowBinding::Tuple(Vec::new());
            assert_eq!(temp, self.temp_vars.push(TempVarBinding::Flow(dummy)));
        }

        let def = self.enum_defs[&ty.symbol].clone();

        let mut variants = IndexVec::new();
        for v in &def.variants {
            let x = self.temp_vars.next_index();
            variants.push(x);
            self.bind_impl(
                x.into(),
                rty::RefinedType::unrefined(v.ty.clone()).vacuous(),
                depth + 1,
            );
        }

        let mut existentials = refinement.existentials;
        let value_var_ev = existentials.push(ty.into_closed_ty().to_sort());
        let mut assumption = UnboundAssumption {
            existentials,
            conds: refinement
                .atoms
                .into_iter()
                .map(|a| {
                    a.map_var(|v| match v {
                        rty::RefinedTypeVar::Value => PlaceTypeVar::Existential(value_var_ev),
                        rty::RefinedTypeVar::Free(v) => PlaceTypeVar::Var(v),
                        rty::RefinedTypeVar::Existential(ev) => PlaceTypeVar::Existential(ev),
                    })
                })
                .collect(),
        };
        let mut pred_args: Vec<_> =
            variants
                .iter()
                .map(|&v| {
                    let ty = self.var_type(v.into());
                    assumption.conds.extend(ty.conds.into_iter().map(|a| {
                        a.map_var(|v| v.shift_existential(assumption.existentials.len()))
                    }));
                    assumption.existentials.extend(ty.existentials);
                    ty.term
                })
                .collect();
        pred_args.push(chc::Term::var(value_var_ev.into()));
        assumption
            .conds
            .push(chc::Atom::new(def.matcher_pred.into(), pred_args));
        let discr_var = self
            .temp_vars
            .push(TempVarBinding::Type(rty::RefinedType::unrefined(
                rty::Type::int(),
            )));
        assumption
            .conds
            .push(
                chc::Term::var(discr_var.into()).equal_to(chc::Term::datatype_discr(
                    def.name.clone(),
                    chc::Term::var(value_var_ev.into()),
                )),
            );
        self.assume(assumption);

        let binding = FlowBinding::Enum {
            discr: discr_var,
            variants,
            sym: def.name.clone(),
            matcher_pred: def.matcher_pred,
        };
        match var {
            Var::Local(local) => {
                self.flow_locals.insert(local, binding);
            }
            Var::Temp(temp) => {
                self.temp_vars[temp] = TempVarBinding::Flow(binding);
            }
        }
    }

    fn bind_var(&mut self, var: Var, rty: rty::RefinedType<Var>) {
        match var {
            Var::Local(local) => {
                self.locals.insert(local, rty);
            }
            Var::Temp(temp) => {
                assert_eq!(temp, self.temp_vars.push(TempVarBinding::Type(rty)));
            }
        }
    }

    fn bind_impl(&mut self, var: Var, rty: rty::RefinedType<Var>, depth: usize) {
        if depth > BIND_EXPANSION_DEPTH_LIMIT {
            self.bind_var(var, rty);
            return;
        }
        match rty.ty {
            rty::Type::Pointer(ty) if ty.is_own() => self.bind_own(var, ty, rty.refinement, depth),
            rty::Type::Pointer(ty) if ty.is_mut() => self.bind_mut(var, ty, rty.refinement, depth),
            rty::Type::Tuple(ty) if !ty.is_unit() => {
                self.bind_tuple(var, ty, rty.refinement, depth)
            }
            rty::Type::Enum(ty) => self.bind_enum(var, ty, rty.refinement, depth),
            _ => self.bind_var(var, rty),
        }
    }

    pub fn bind(&mut self, local: Local, rty: rty::RefinedType<Var>) {
        let rty_disp = rty.clone();
        self.bind_impl(local.into(), rty, 0);
        tracing::debug!(local = ?local, rty = %rty_disp.display(), place_type = %self.local_type(local).display(), "bind");
    }

    pub fn assume(&mut self, assumption: impl Into<UnboundAssumption>) {
        let assumption = assumption.into();
        tracing::debug!(assumption = %assumption.display(), "assume");
        self.unbound_assumptions.push(assumption);
    }

    pub fn extend_assumptions(&mut self, assumptions: Vec<impl Into<UnboundAssumption>>) {
        self.unbound_assumptions
            .extend(assumptions.into_iter().map(Into::into));
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

    fn vars(&self) -> impl Iterator<Item = (Var, &rty::RefinedType<Var>)> + '_ {
        self.locals
            .iter()
            .map(|(local, rty)| (Var::Local(*local), rty))
            .chain(
                self.temp_vars
                    .iter_enumerated()
                    .filter_map(|(idx, b)| b.as_type().map(|rty| (Var::Temp(idx), rty))),
            )
            .filter(|(_var, rty)| rty.is_refined())
    }

    pub fn contains_local(&self, local: Local) -> bool {
        self.locals.contains_key(&local) || self.flow_locals.contains_key(&local)
    }

    fn flow_binding(&self, var: Var) -> Option<&FlowBinding> {
        match var {
            Var::Local(local) => self.flow_locals.get(&local),
            Var::Temp(temp) => self.temp_vars[temp].as_flow(),
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

    fn var_type(&self, var: Var) -> PlaceType {
        // TODO: should this driven by type as the rule does?
        match self.flow_binding(var) {
            Some(&FlowBinding::Box(current)) => self.var_type(current.into()).boxed(),
            Some(&FlowBinding::Mut(current, final_)) => {
                let current_ty = self.var_type(current.into());
                let final_ty = self.var_type(final_.into());
                current_ty.mut_with(final_ty)
            }
            Some(FlowBinding::Tuple(vs)) => {
                let tys = vs.iter().map(|&v| self.var_type(v.into())).collect();
                PlaceType::tuple(tys)
            }
            Some(FlowBinding::Enum {
                discr,
                variants,
                sym,
                matcher_pred,
            }) => {
                let tys = variants.iter().map(|&v| self.var_type(v.into())).collect();
                PlaceType::enum_(*discr, sym.clone(), tys, *matcher_pred)
            }
            None => {
                let rty = self.var(var).expect("unbound var");
                PlaceType::with_ty_and_term(rty.ty.clone(), chc::Term::var(var))
            }
        }
    }

    pub fn local_type(&self, local: Local) -> PlaceType {
        self.var_type(local.into())
    }

    pub fn operand_type(&self, operand: Operand<'_>) -> PlaceType {
        use mir::{interpret::Scalar, Const, ConstValue, Mutability};
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_type(place),
            Operand::Constant(operand) => {
                let Const::Val(val, ty) = operand.const_ else {
                    unimplemented!("const: {:?}", operand.const_);
                };
                match (ty.kind(), val) {
                    (mir_ty::TyKind::Int(_), ConstValue::Scalar(Scalar::Int(val))) => {
                        let val = val.try_to_int(val.size()).unwrap();
                        PlaceType::with_ty_and_term(
                            rty::Type::int(),
                            chc::Term::int(val.try_into().unwrap()),
                        )
                    }
                    (mir_ty::TyKind::Bool, ConstValue::Scalar(Scalar::Int(val))) => {
                        PlaceType::with_ty_and_term(
                            rty::Type::bool(),
                            chc::Term::bool(val.try_to_bool().unwrap()),
                        )
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
                        PlaceType::with_ty_and_term(
                            rty::PointerType::immut_to(rty::Type::string()).into(),
                            chc::Term::box_(chc::Term::string(content.to_owned())),
                        )
                    }
                    _ => unimplemented!("const: {:?}, ty: {:?}", val, ty),
                }
            }
        }
    }

    fn borrow_var(&mut self, var: Var, prophecy: TempVarIdx) -> PlaceType {
        match self.flow_binding(var).expect("borrowing unbound var") {
            &FlowBinding::Box(x) => {
                let inner_ty = self.var_type(x.into());
                self.insert_flow_binding(var, FlowBinding::Box(prophecy));
                inner_ty.mut_with_proph_term(chc::Term::var(prophecy.into()))
            }
            &FlowBinding::Mut(x1, x2) => {
                let inner_ty = self.var_type(x1.into());
                self.insert_flow_binding(var, FlowBinding::Mut(prophecy, x2));
                inner_ty.mut_with_proph_term(chc::Term::var(prophecy.into()))
            }
            _ => panic!("invalid borrow"),
        }
    }

    fn locate_place(&self, place: Place<'_>) -> Var {
        let mut var = place.local.into();

        for elem in place.projection {
            var = match (elem, self.flow_binding(var).expect("deref unbound var")) {
                (PlaceElem::Deref, &FlowBinding::Box(x)) => x.into(),
                (PlaceElem::Deref, &FlowBinding::Mut(x, _)) => x.into(),
                (PlaceElem::Field(idx, _), FlowBinding::Tuple(xs)) => xs[idx.as_usize()].into(),
                (PlaceElem::Downcast(_, idx), FlowBinding::Enum { variants, .. }) => {
                    variants[idx].into()
                }
                _ => unimplemented!("elem={:?}", elem),
            };
        }

        var
    }

    pub fn borrow_place(&mut self, place: Place<'_>, prophecy_var: TempVarIdx) -> PlaceType {
        let var = self.locate_place(place);
        self.borrow_var(var, prophecy_var)
    }
}

#[derive(Debug, Clone)]
enum Path {
    Local(Local),
    Deref(Box<Path>),
    TupleProj(Box<Path>, usize),
    Downcast(Box<Path>, VariantIdx),
}

impl<'tcx> From<Place<'tcx>> for Path {
    fn from(place: Place<'tcx>) -> Self {
        place
            .projection
            .into_iter()
            .fold(Path::Local(place.local), |path, elem| match elem {
                PlaceElem::Deref => Path::Deref(Box::new(path)),
                PlaceElem::Field(idx, _) => Path::TupleProj(Box::new(path), idx.as_usize()),
                PlaceElem::Downcast(_, idx) => Path::Downcast(Box::new(path), idx),
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
    fn path_type(&self, path: &Path) -> PlaceType {
        match path {
            Path::Local(local) => self.local_type(*local),
            Path::Deref(path) => self.path_type(path).deref(),
            Path::TupleProj(path, idx) => self.path_type(path).tuple_proj(*idx),
            Path::Downcast(path, idx) => self.path_type(path).downcast(*idx, &self.enum_defs),
        }
    }

    pub fn place_type(&self, place: Place) -> PlaceType {
        self.path_type(&place.into())
    }

    fn drop_path(&mut self, path: &Path) {
        let ty = self.path_type(path);
        if ty.ty.is_mut() {
            self.assume(ty.into_assumption(|term| {
                let term = term.map_var(Into::into);
                term.clone().mut_final().equal_to(term.mut_current())
            }));
        } else if ty.ty.is_own() {
            self.drop_path(&path.clone().deref())
        }
    }

    pub fn drop_local(&mut self, local: Local) {
        self.drop_path(&Path::Local(local))
    }
}
