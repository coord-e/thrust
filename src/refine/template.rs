use std::collections::HashMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Mutability};
use rustc_middle::ty as mir_ty;

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

#[derive(Clone)]
pub struct TypeBuilder<'tcx> {
    tcx: mir_ty::TyCtxt<'tcx>,
}

impl<'tcx> TypeBuilder<'tcx> {
    pub fn new(tcx: mir_ty::TyCtxt<'tcx>) -> Self {
        Self { tcx }
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
            mir_ty::TyKind::Param(ty) => rty::ParamType::new(ty.index.into()).into(),
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
            tcx: self.tcx,
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
            tcx: self.tcx,
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

pub struct TemplateTypeBuilder<'tcx, 'a, R, S> {
    tcx: mir_ty::TyCtxt<'tcx>,
    registry: &'a mut R,
    scope: S,
}

impl<'tcx, 'a, R, S> TemplateTypeBuilder<'tcx, 'a, R, S> {
    pub fn with_scope<T>(self, scope: T) -> TemplateTypeBuilder<'tcx, 'a, R, T> {
        TemplateTypeBuilder {
            tcx: self.tcx,
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
            mir_ty::TyKind::Param(ty) => rty::ParamType::new(ty.index.into()).into(),
            mir_ty::TyKind::FnPtr(sig) => {
                // TODO: justification for skip_binder
                let sig = sig.skip_binder();
                let ty = TypeBuilder::new(self.tcx)
                    .for_function_template(self.registry, sig)
                    .build();
                rty::Type::function(ty)
            }
            mir_ty::TyKind::Adt(def, params) if def.is_box() => {
                rty::PointerType::own(self.build(params.type_at(0))).into()
            }
            mir_ty::TyKind::Adt(def, params) => {
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.tcx, def.did());
                    let args: IndexVec<_, _> =
                        params.types().map(|ty| self.build_refined(ty)).collect();
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
            kind => unimplemented!("ty: {:?}", kind),
        }
    }

    pub fn build_refined(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::RefinedType<S::Var> {
        // TODO: consider building ty with scope
        let ty = TypeBuilder::new(self.tcx)
            .for_template(self.registry)
            .build(ty)
            .vacuous();
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
            tcx: self.tcx,
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

pub struct FunctionTemplateTypeBuilder<'tcx, 'a, R> {
    tcx: mir_ty::TyCtxt<'tcx>,
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
        let ty = TypeBuilder::new(self.tcx).build(self.ret_ty);
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
                            let ty = TypeBuilder::new(self.tcx).build(param_ty.ty);
                            rty::RefinedType::new(ty.vacuous(), param_refinement.clone())
                        } else {
                            TypeBuilder::new(self.tcx)
                                .for_template(self.registry)
                                .with_scope(&builder)
                                .build_refined(param_ty.ty)
                        }
                    } else {
                        rty::RefinedType::unrefined(
                            TypeBuilder::new(self.tcx)
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
                let unit_ty = mir_ty::Ty::new_unit(self.tcx);
                TypeBuilder::new(self.tcx)
                    .for_template(self.registry)
                    .with_scope(&builder)
                    .build_refined(unit_ty)
            };
            param_rtys.push(param_rty);
        }

        let ret_rty = self.ret_rty.clone().unwrap_or_else(|| {
            TypeBuilder::new(self.tcx)
                .for_template(self.registry)
                .with_scope(&builder)
                .build_refined(self.ret_ty)
        });
        rty::FunctionType::new(param_rtys, ret_rty)
    }
}
