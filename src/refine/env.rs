use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, Local, Operand, Place, PlaceElem};
use rustc_middle::ty as mir_ty;
use rustc_target::abi::{FieldIdx, VariantIdx};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine;
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

#[derive(Debug, Clone)]
struct FlowBindingVariant {
    pub fields: IndexVec<FieldIdx, TempVarIdx>,
}

#[derive(Debug, Clone)]
enum FlowBinding {
    Mut(TempVarIdx, TempVarIdx),
    Box(TempVarIdx),
    Tuple(Vec<TempVarIdx>),
    Enum {
        discr: TempVarIdx,
        variants: IndexVec<VariantIdx, FlowBindingVariant>,
        sym: chc::DatatypeSymbol,
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
                    if i.index() != 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}::{:?}(", sym, i)?;
                    for (field_idx, field) in v.fields.iter().enumerate() {
                        if field_idx != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", field)?;
                    }
                    write!(f, ")")?;
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

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
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

impl std::fmt::Debug for PlaceTypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            PlaceTypeVar::Var(v) => v.fmt(f),
            PlaceTypeVar::Existential(v) => v.fmt(f),
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
        variant_idx: VariantIdx,
        field_idx: FieldIdx,
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
        let variant = &def.variants[variant_idx];

        let mut field_terms = Vec::new();
        let mut field_tys = Vec::new();
        for field_ty in variant.field_tys.clone() {
            let mut rty = rty::RefinedType::unrefined(field_ty.vacuous());
            rty.instantiate_ty_params(inner_ty.args.clone());
            let rty::RefinedType { ty, refinement } = rty;

            let field_ex_var = existentials.push(ty.to_sort());
            field_terms.push(chc::Term::var(field_ex_var.into()));
            field_tys.push(ty);

            conds.extend(refinement.atoms.into_iter().map(|a| {
                a.map_var(|v| match v {
                    rty::RefinedTypeVar::Value => PlaceTypeVar::Existential(field_ex_var),
                    rty::RefinedTypeVar::Existential(ev) => {
                        PlaceTypeVar::Existential(ev + existentials.len())
                    }
                    rty::RefinedTypeVar::Free(v) => PlaceTypeVar::Var(v),
                })
            }));
            existentials.extend(refinement.existentials);
        }

        conds.push(
            chc::Term::datatype_ctor(
                def.name.clone(),
                inner_ty.arg_sorts(),
                variant.name.clone(),
                field_terms.clone(),
            )
            .equal_to(inner_term),
        );

        let ty = field_tys[field_idx.index()].clone();
        let term = field_terms[field_idx.index()].clone();
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

    pub fn aggregate<I, F, G>(ptys: I, make_ty: F, make_term: G) -> PlaceType
    where
        I: IntoIterator<Item = PlaceType>,
        F: FnOnce(Vec<rty::Type<Var>>) -> rty::Type<Var>,
        G: FnOnce(Vec<chc::Term<PlaceTypeVar>>) -> chc::Term<PlaceTypeVar>,
    {
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
        } = ptys
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
        let ty = make_ty(tys);
        let term = make_term(terms);
        PlaceType {
            ty,
            existentials,
            term,
            conds,
        }
    }

    pub fn tuple(tys: Vec<PlaceType>) -> PlaceType {
        PlaceType::aggregate(tys, |tys| rty::TupleType::new(tys).into(), chc::Term::tuple)
    }

    pub fn enum_(
        enum_ty: rty::EnumType<Var>,
        matcher_pred: chc::PredVarId,
        discr: TempVarIdx,
        field_tys: Vec<PlaceType>,
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
        } = field_tys
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
        let ty: rty::Type<_> = enum_ty.clone().into();
        let value_var_ev = existentials.push(ty.to_sort());
        let term = chc::Term::var(value_var_ev.into());
        let mut pred_args = terms;
        pred_args.push(chc::Term::var(value_var_ev.into()));
        conds.push(chc::Atom::new(matcher_pred.into(), pred_args));
        conds.push(
            chc::Term::var(discr.into()).equal_to(chc::Term::datatype_discr(
                enum_ty.symbol.clone(),
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

#[derive(Debug, Clone, Default)]
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

    matcher_preds: Rc<RefCell<refine::MatcherPredCache>>,
    enum_defs: HashMap<chc::DatatypeSymbol, rty::EnumDatatypeDef>,

    enum_expansion_depth_limit: usize,
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
            if !rty.ty.to_sort().is_singleton() {
                instantiator.value_var(builder.mapped_var(var));
            }
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

impl refine::TemplateScope<Var> for Env {
    fn build_template(&self) -> rty::TemplateBuilder<Var> {
        let mut builder = rty::TemplateBuilder::default();
        for (v, sort) in self.dependencies() {
            builder.add_dependency(v, sort);
        }
        builder
    }
}

impl Env {
    pub fn new(
        enum_defs: HashMap<chc::DatatypeSymbol, rty::EnumDatatypeDef>,
        matcher_preds: Rc<RefCell<refine::MatcherPredCache>>,
    ) -> Self {
        Env {
            locals: HashMap::new(),
            flow_locals: HashMap::new(),
            temp_vars: IndexVec::new(),
            unbound_assumptions: Vec::new(),
            matcher_preds,
            enum_defs,
            enum_expansion_depth_limit: std::env::var("THRUST_ENUM_EXPANSION_DEPTH_LIMIT")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(2),
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
        self.bind_impl(current.into(), inner_ty, depth);
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
        self.bind_impl(current.into(), inner_ty, depth);
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
            self.bind_impl(x.into(), elem.clone(), depth);
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
        ty: rty::EnumType<Var>,
        refinement: rty::Refinement<Var>,
        depth: usize,
    ) {
        if let Var::Temp(temp) = var {
            // XXX: allocate `temp` once to invoke bind_var recursively
            let dummy = FlowBinding::Tuple(Vec::new());
            assert_eq!(temp, self.temp_vars.push(TempVarBinding::Flow(dummy)));
        }

        let def = self.enum_defs[&ty.symbol].clone();
        let matcher_pred = self
            .matcher_preds
            .borrow_mut()
            .get_or_create(&ty.symbol, &ty.arg_sorts());

        let mut variants = IndexVec::new();
        for variant_def in &def.variants {
            let mut fields = IndexVec::new();
            for field_ty in &variant_def.field_tys {
                let x = self.temp_vars.next_index();
                fields.push(x);
                let mut field_ty = rty::RefinedType::unrefined(field_ty.clone().vacuous());
                field_ty.instantiate_ty_params(ty.args.clone());
                self.bind_impl(x.into(), field_ty, depth);
            }
            variants.push(FlowBindingVariant { fields });
        }

        let mut existentials = refinement.existentials;
        let value_var_ev = existentials.push(rty::Type::Enum(ty.clone()).to_sort());
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
                .flat_map(|v| &v.fields)
                .map(|&x| {
                    let ty = self.var_type(x.into());
                    assumption.conds.extend(ty.conds.into_iter().map(|a| {
                        a.map_var(|v| v.shift_existential(assumption.existentials.len()))
                    }));
                    let term = ty
                        .term
                        .map_var(|v| v.shift_existential(assumption.existentials.len()));
                    assumption.existentials.extend(ty.existentials);
                    term
                })
                .collect();
        pred_args.push(chc::Term::var(value_var_ev.into()));
        assumption
            .conds
            .push(chc::Atom::new(matcher_pred.into(), pred_args));
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
        if depth >= self.enum_expansion_depth_limit {
            self.bind_var(var, rty);
            return;
        }
        match rty.ty {
            rty::Type::Pointer(ty) if ty.is_own() => self.bind_own(var, ty, rty.refinement, depth),
            rty::Type::Pointer(ty) if ty.is_mut() => self.bind_mut(var, ty, rty.refinement, depth),
            rty::Type::Tuple(ty) if !ty.is_unit() => {
                self.bind_tuple(var, ty, rty.refinement, depth)
            }
            rty::Type::Enum(ty) => self.bind_enum(var, ty, rty.refinement, depth + 1),
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
            .filter(|(_, s)| !s.is_singleton())
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
            }) => {
                let field_tys: Vec<_> = variants
                    .iter()
                    .flat_map(|v| &v.fields)
                    .map(|&v| self.var_type(v.into()))
                    .collect();

                let arg_rtys = {
                    let def = &self.enum_defs[&sym];
                    let expected_tys = def
                        .field_tys()
                        .map(|ty| rty::RefinedType::unrefined(ty.clone().vacuous()));
                    let got_tys = field_tys.iter().map(|ty| ty.clone().into());
                    rty::unify_tys_params(expected_tys, got_tys).into_params(def.ty_params, |_| {
                        panic!("var_type: should unify all params")
                    })
                };

                let enum_ty = rty::EnumType::new(sym.clone(), arg_rtys);
                let matcher_pred = self
                    .matcher_preds
                    .borrow_mut()
                    .get_or_create(&sym, &enum_ty.arg_sorts());
                PlaceType::enum_(enum_ty, matcher_pred, *discr, field_tys)
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

        let mut it = place.projection.into_iter();
        loop {
            let Some(elem) = it.next() else {
                break;
            };
            var = match (elem, self.flow_binding(var).expect("deref unbound var")) {
                (PlaceElem::Deref, &FlowBinding::Box(x)) => x.into(),
                (PlaceElem::Deref, &FlowBinding::Mut(x, _)) => x.into(),
                (PlaceElem::Field(idx, _), FlowBinding::Tuple(xs)) => xs[idx.as_usize()].into(),
                (PlaceElem::Downcast(_, variant_idx), FlowBinding::Enum { variants, .. }) => {
                    let Some(PlaceElem::Field(field_idx, _)) = it.next() else {
                        panic!("downcast not followed by field")
                    };
                    variants[variant_idx].fields[field_idx].into()
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
    Downcast(Box<Path>, VariantIdx, FieldIdx),
}

impl<'tcx> From<Place<'tcx>> for Path {
    fn from(place: Place<'tcx>) -> Self {
        let mut it = place.projection.into_iter();
        let mut path = Path::Local(place.local);
        loop {
            path = match it.next() {
                Some(PlaceElem::Deref) => Path::Deref(Box::new(path)),
                Some(PlaceElem::Field(idx, _)) => Path::TupleProj(Box::new(path), idx.as_usize()),
                Some(PlaceElem::Downcast(_, variant_idx)) => {
                    let Some(PlaceElem::Field(field_idx, _)) = it.next() else {
                        panic!("downcast not followed by field")
                    };
                    Path::Downcast(Box::new(path), variant_idx, field_idx)
                }
                None => break,
                _ => unimplemented!(),
            };
        }
        path
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
            Path::Downcast(path, variant_idx, field_idx) => {
                self.path_type(path)
                    .downcast(*variant_idx, *field_idx, &self.enum_defs)
            }
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
