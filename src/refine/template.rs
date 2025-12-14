use std::collections::HashMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Mutability};
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

use super::basic_block::BasicBlockType;
use crate::chc;
use crate::refine;
use crate::rty;

pub trait TemplateRegistry {
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V>;
}

impl<T> TemplateRegistry for &mut T
where
    T: TemplateRegistry + ?Sized,
{
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        T::register_template(self, tmpl)
    }
}

/// [`TemplateScope`] with no variables in scope.
#[derive(Clone, Default)]
pub struct EmptyTemplateScope;

impl TemplateScope for EmptyTemplateScope {
    type Var = rty::Closed;
    fn build_template(&self) -> rty::TemplateBuilder<Self::Var> {
        rty::TemplateBuilder::default()
    }
}

pub trait TemplateScope {
    type Var: chc::Var;
    fn build_template(&self) -> rty::TemplateBuilder<Self::Var>;
}

impl<T> TemplateScope for &T
where
    T: TemplateScope,
{
    type Var = T::Var;
    fn build_template(&self) -> rty::TemplateBuilder<Self::Var> {
        T::build_template(self)
    }
}

impl<T> TemplateScope for rty::TemplateBuilder<T>
where
    T: chc::Var,
{
    type Var = T;
    fn build_template(&self) -> rty::TemplateBuilder<T> {
        self.clone()
    }
}

/// Translates [`mir_ty::Ty`] to [`rty::Type`].
///
/// This struct implements a translation from Rust MIR types to Thrust types.
/// Thrust types may contain refinement predicates which do not exist in MIR types,
/// and [`TypeBuilder`] solely builds types with null refinement (true) in
/// [`TypeBuilder::build`]. This also provides [`TypeBuilder::for_template`] to build
/// refinement types by filling unknown predicates with templates with predicate variables.
#[derive(Clone)]
pub struct TypeBuilder<'tcx> {
    tcx: mir_ty::TyCtxt<'tcx>,
    /// Maps index in [`mir_ty::ParamTy`] to [`rty::TypeParamIdx`].
    /// These indices may differ because we skip lifetime parameters and they always need to be
    /// mapped when we translate a [`mir_ty::ParamTy`] to [`rty::ParamType`].
    /// See [`rty::TypeParamIdx`] for more details.
    param_idx_mapping: HashMap<u32, rty::TypeParamIdx>,
}

impl<'tcx> TypeBuilder<'tcx> {
    pub fn new(tcx: mir_ty::TyCtxt<'tcx>, def_id: DefId) -> Self {
        let generics = tcx.generics_of(def_id);
        let mut param_idx_mapping: HashMap<u32, rty::TypeParamIdx> = Default::default();
        for i in 0..generics.count() {
            let generic_param = generics.param_at(i, tcx);
            match generic_param.kind {
                mir_ty::GenericParamDefKind::Lifetime => {}
                mir_ty::GenericParamDefKind::Type { .. } => {
                    param_idx_mapping.insert(i as u32, param_idx_mapping.len().into());
                }
                mir_ty::GenericParamDefKind::Const { .. } => {}
            }
        }
        Self {
            tcx,
            param_idx_mapping,
        }
    }

    fn translate_param_type(&self, ty: &mir_ty::ParamTy) -> rty::Type<rty::Closed> {
        let index = *self
            .param_idx_mapping
            .get(&ty.index)
            .expect("unknown type param idx");
        rty::ParamType::new(index).into()
    }

    // TODO: consolidate two impls
    pub fn build(&self, ty: mir_ty::Ty<'tcx>) -> rty::Type<rty::Closed> {
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Uint(_) | mir_ty::TyKind::Int(_) => rty::Type::int(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
                let elem_ty = self.build(*elem_ty);
                match mutbl {
                    mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                    mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
                }
            }
            mir_ty::TyKind::Tuple(ts) => {
                // elaboration: all fields are boxed
                let elems = ts
                    .iter()
                    .map(|ty| rty::PointerType::own(self.build(ty)).into())
                    .collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
            mir_ty::TyKind::Param(ty) => self.translate_param_type(ty),
            mir_ty::TyKind::FnPtr(sig) => {
                // TODO: justification for skip_binder
                let sig = sig.skip_binder();
                let params = sig
                    .inputs()
                    .iter()
                    .map(|ty| rty::RefinedType::unrefined(self.build(*ty)).vacuous())
                    .collect();
                let ret = rty::RefinedType::unrefined(self.build(sig.output()));
                rty::FunctionType::new(params, ret.vacuous()).into()
            }
            mir_ty::TyKind::Adt(def, params) if def.is_box() => {
                rty::PointerType::own(self.build(params.type_at(0))).into()
            }
            mir_ty::TyKind::Adt(def, params) => {
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.tcx, def.did());
                    let args: IndexVec<_, _> = params
                        .types()
                        .map(|ty| rty::RefinedType::unrefined(self.build(ty)))
                        .collect();
                    rty::EnumType::new(sym, args).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.tcx, params);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.build(ty)).into()
                        })
                        .collect();
                    rty::TupleType::new(elem_tys).into()
                } else {
                    unimplemented!("unsupported ADT: {:?}", ty);
                }
            }
            kind => unimplemented!("unrefined_ty: {:?}", kind),
        }
    }

    pub fn for_template<'a, R>(
        &self,
        registry: &'a mut R,
    ) -> TemplateTypeBuilder<'tcx, 'a, R, EmptyTemplateScope> {
        TemplateTypeBuilder {
            inner: self.clone(),
            registry,
            scope: Default::default(),
        }
    }

    pub fn for_function_template<'a, R>(
        &self,
        registry: &'a mut R,
        sig: mir_ty::FnSig<'tcx>,
    ) -> FunctionTemplateTypeBuilder<'tcx, 'a, R> {
        FunctionTemplateTypeBuilder {
            inner: self.clone(),
            registry,
            param_tys: sig
                .inputs()
                .iter()
                .map(|ty| mir_ty::TypeAndMut {
                    ty: *ty,
                    mutbl: Mutability::Not,
                })
                .collect(),
            ret_ty: sig.output(),
            param_rtys: Default::default(),
            param_refinement: None,
            ret_rty: None,
        }
    }
}

/// Translates [`mir_ty::Ty`] to [`rty::Type`] using templates for refinements.
///
/// [`rty::Template`] is a refinement type in the form of `{ T | P(x1, ..., xn) }` where `P` is a
/// predicate variable. When constructing a template, we need to know which variables can affect the
/// predicate of the template (dependencies, `x1, ..., xn`), and they are provided by the
/// [`TemplateScope`]. No variables are in scope by default and you can provide a scope using
/// [`TemplateTypeBuilder::with_scope`].
pub struct TemplateTypeBuilder<'tcx, 'a, R, S> {
    inner: TypeBuilder<'tcx>,
    // XXX: this can't be simply `R` because monomorphization instantiates types recursively
    registry: &'a mut R,
    scope: S,
}

impl<'tcx, 'a, R, S> TemplateTypeBuilder<'tcx, 'a, R, S> {
    pub fn with_scope<T>(self, scope: T) -> TemplateTypeBuilder<'tcx, 'a, R, T> {
        TemplateTypeBuilder {
            inner: self.inner,
            registry: self.registry,
            scope,
        }
    }
}

impl<'tcx, 'a, R, S> TemplateTypeBuilder<'tcx, 'a, R, S>
where
    R: TemplateRegistry,
    S: TemplateScope,
{
    pub fn build(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::Type<S::Var> {
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Uint(_) | mir_ty::TyKind::Int(_) => rty::Type::int(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
                let elem_ty = self.build(*elem_ty);
                match mutbl {
                    mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                    mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
                }
            }
            mir_ty::TyKind::Tuple(ts) => {
                // elaboration: all fields are boxed
                let elems = ts
                    .iter()
                    .map(|ty| rty::PointerType::own(self.build(ty)).into())
                    .collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
            mir_ty::TyKind::Param(ty) => self.inner.translate_param_type(ty).vacuous(),
            mir_ty::TyKind::FnPtr(sig) => {
                // TODO: justification for skip_binder
                let sig = sig.skip_binder();
                let ty = self.inner.for_function_template(self.registry, sig).build();
                rty::Type::function(ty)
            }
            mir_ty::TyKind::Adt(def, params) if def.is_box() => {
                rty::PointerType::own(self.build(params.type_at(0))).into()
            }
            mir_ty::TyKind::Adt(def, params) => {
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.inner.tcx, def.did());
                    let args: IndexVec<_, _> =
                        params.types().map(|ty| self.build_refined(ty)).collect();
                    rty::EnumType::new(sym, args).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.inner.tcx, params);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.build(ty)).into()
                        })
                        .collect();
                    rty::TupleType::new(elem_tys).into()
                } else {
                    unimplemented!("unsupported ADT: {:?}", ty);
                }
            }
            kind => unimplemented!("ty: {:?}", kind),
        }
    }

    pub fn build_refined(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::RefinedType<S::Var> {
        // TODO: consider building ty with scope
        let ty = self.inner.for_template(self.registry).build(ty).vacuous();
        let tmpl = self.scope.build_template().build(ty);
        self.registry.register_template(tmpl)
    }

    pub fn build_basic_block<I>(
        &mut self,
        live_locals: I,
        ret_ty: mir_ty::Ty<'tcx>,
    ) -> BasicBlockType
    where
        I: IntoIterator<Item = (Local, mir_ty::TypeAndMut<'tcx>)>,
    {
        let mut locals = IndexVec::<rty::FunctionParamIdx, _>::new();
        let mut tys = Vec::new();
        // TODO: avoid two iteration and assumption of FunctionParamIdx match between locals and ty
        for (local, ty) in live_locals {
            locals.push((local, ty.mutbl));
            tys.push(ty);
        }
        let ty = FunctionTemplateTypeBuilder {
            inner: self.inner.clone(),
            registry: self.registry,
            param_tys: tys,
            ret_ty,
            param_rtys: Default::default(),
            param_refinement: None,
            ret_rty: None,
        }
        .build();
        BasicBlockType { ty, locals }
    }
}

/// A builder for function template types.
pub struct FunctionTemplateTypeBuilder<'tcx, 'a, R> {
    inner: TypeBuilder<'tcx>,
    registry: &'a mut R,
    param_tys: Vec<mir_ty::TypeAndMut<'tcx>>,
    ret_ty: mir_ty::Ty<'tcx>,
    param_refinement: Option<rty::Refinement<rty::FunctionParamIdx>>,
    param_rtys: HashMap<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    ret_rty: Option<rty::RefinedType<rty::FunctionParamIdx>>,
}

impl<'tcx, 'a, R> FunctionTemplateTypeBuilder<'tcx, 'a, R> {
    pub fn param_refinement(
        &mut self,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        let rty::Refinement { existentials, body } = refinement;
        let refinement = rty::Refinement {
            existentials,
            body: body.map_var(|v| match v {
                rty::RefinedTypeVar::Free(idx) if idx.index() == self.param_tys.len() - 1 => {
                    rty::RefinedTypeVar::Value
                }
                v => v,
            }),
        };
        self.param_refinement = Some(refinement);
        self
    }

    pub fn param_rty(
        &mut self,
        idx: rty::FunctionParamIdx,
        ty: rty::RefinedType<rty::FunctionParamIdx>,
    ) -> &mut Self {
        self.param_rtys.insert(idx, ty);
        self
    }

    pub fn ret_refinement(
        &mut self,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        let ty = self.inner.build(self.ret_ty);
        self.ret_rty = Some(rty::RefinedType::new(ty.vacuous(), refinement));
        self
    }

    pub fn ret_rty(&mut self, rty: rty::RefinedType<rty::FunctionParamIdx>) -> &mut Self {
        self.ret_rty = Some(rty);
        self
    }
}

impl<'tcx, 'a, R> FunctionTemplateTypeBuilder<'tcx, 'a, R>
where
    R: TemplateRegistry,
{
    pub fn build(&mut self) -> rty::FunctionType {
        let mut builder = rty::TemplateBuilder::default();
        let mut param_rtys = IndexVec::<rty::FunctionParamIdx, _>::new();
        for (idx, param_ty) in self.param_tys.iter().enumerate() {
            let param_rty = self
                .param_rtys
                .get(&idx.into())
                .cloned()
                .unwrap_or_else(|| {
                    if idx == self.param_tys.len() - 1 {
                        if let Some(param_refinement) = &self.param_refinement {
                            let ty = self.inner.build(param_ty.ty);
                            rty::RefinedType::new(ty.vacuous(), param_refinement.clone())
                        } else {
                            self.inner
                                .for_template(self.registry)
                                .with_scope(&builder)
                                .build_refined(param_ty.ty)
                        }
                    } else {
                        rty::RefinedType::unrefined(
                            self.inner
                                .for_template(self.registry)
                                .with_scope(&builder)
                                .build(param_ty.ty),
                        )
                    }
                });
            let param_rty = if param_ty.mutbl.is_mut() {
                // elaboration: treat mutabully declared variables as own
                param_rty.boxed()
            } else {
                param_rty
            };
            let param_sort = param_rty.ty.to_sort();
            let param_idx = param_rtys.push(param_rty);
            builder.add_dependency(param_idx, param_sort);
        }

        // elaboration: we need at least one predicate variable in parameter
        if self.param_tys.is_empty() {
            let param_rty = if let Some(param_refinement) = &self.param_refinement {
                rty::RefinedType::new(rty::Type::unit(), param_refinement.clone())
            } else {
                let unit_ty = mir_ty::Ty::new_unit(self.inner.tcx);
                self.inner
                    .for_template(self.registry)
                    .with_scope(&builder)
                    .build_refined(unit_ty)
            };
            param_rtys.push(param_rty);
        }

        let ret_rty = self.ret_rty.clone().unwrap_or_else(|| {
            self.inner
                .for_template(self.registry)
                .with_scope(&builder)
                .build_refined(self.ret_ty)
        });
        rty::FunctionType::new(param_rtys, ret_rty)
    }
}
