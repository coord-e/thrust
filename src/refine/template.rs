use std::collections::HashMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Mutability};
use rustc_middle::ty as mir_ty;

use super::basic_block::BasicBlockType;
use crate::chc;
use crate::refine;
use crate::rty;

pub trait TemplateScope<T> {
    fn build_template(&self) -> rty::TemplateBuilder<T>;
}

impl<T, U> TemplateScope<T> for &U
where
    U: TemplateScope<T>,
{
    fn build_template(&self) -> rty::TemplateBuilder<T> {
        U::build_template(self)
    }
}

impl<T> TemplateScope<T> for rty::TemplateBuilder<T>
where
    T: chc::Var,
{
    fn build_template(&self) -> rty::TemplateBuilder<T> {
        self.clone()
    }
}

pub trait TemplateTypeGenerator<'tcx> {
    fn tcx(&self) -> mir_ty::TyCtxt<'tcx>;
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V>;

    fn build_template_ty_with_scope<T, V>(&mut self, scope: T) -> TemplateTypeBuilder<Self, T, V> {
        TemplateTypeBuilder {
            gen: self,
            scope,
            _marker: std::marker::PhantomData,
        }
    }

    fn build_template_ty<V>(&mut self) -> TemplateTypeBuilder<Self, rty::TemplateBuilder<V>, V> {
        TemplateTypeBuilder {
            gen: self,
            scope: Default::default(),
            _marker: std::marker::PhantomData,
        }
    }

    fn build_function_template_ty(
        &mut self,
        sig: mir_ty::FnSig<'tcx>,
    ) -> FunctionTemplateTypeBuilder<'_, 'tcx, Self> {
        FunctionTemplateTypeBuilder {
            gen: self,
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

    fn build_basic_block_template_ty<I>(
        &mut self,
        live_locals: I,
        ret_ty: mir_ty::Ty<'tcx>,
    ) -> BasicBlockTemplateTypeBuilder<'_, 'tcx, Self>
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
        let inner = FunctionTemplateTypeBuilder {
            gen: self,
            param_tys: tys,
            ret_ty,
            param_rtys: Default::default(),
            param_refinement: None,
            ret_rty: None,
        };
        BasicBlockTemplateTypeBuilder { inner, locals }
    }

    fn basic_block_template_ty<I>(
        &mut self,
        live_locals: I,
        ret_ty: mir_ty::Ty<'tcx>,
    ) -> BasicBlockType
    where
        I: IntoIterator<Item = (Local, mir_ty::TypeAndMut<'tcx>)>,
    {
        self.build_basic_block_template_ty(live_locals, ret_ty)
            .build()
    }

    fn function_template_ty(&mut self, sig: mir_ty::FnSig<'tcx>) -> rty::FunctionType {
        self.build_function_template_ty(sig).build()
    }
}

impl<'tcx, T> TemplateTypeGenerator<'tcx> for &mut T
where
    T: TemplateTypeGenerator<'tcx> + ?Sized,
{
    fn tcx(&self) -> mir_ty::TyCtxt<'tcx> {
        T::tcx(self)
    }

    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        T::register_template(self, tmpl)
    }
}

#[derive(Debug)]
pub struct FunctionTemplateTypeBuilder<'a, 'tcx, T: ?Sized> {
    // can't use T: TemplateTypeGenerator<'tcx> directly because of recursive instantiation
    gen: &'a mut T,
    param_tys: Vec<mir_ty::TypeAndMut<'tcx>>,
    ret_ty: mir_ty::Ty<'tcx>,
    param_refinement: Option<rty::Refinement<rty::FunctionParamIdx>>,
    param_rtys: HashMap<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    ret_rty: Option<rty::RefinedType<rty::FunctionParamIdx>>,
}

impl<'a, 'tcx, T> FunctionTemplateTypeBuilder<'a, 'tcx, T>
where
    T: TemplateTypeGenerator<'tcx> + ?Sized,
{
    pub fn param_refinement(
        &mut self,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        let refinement = rty::Refinement {
            existentials: refinement.existentials,
            atoms: refinement
                .atoms
                .into_iter()
                .map(|a| {
                    a.map_var(|v| match v {
                        rty::RefinedTypeVar::Free(idx)
                            if idx.index() == self.param_tys.len() - 1 =>
                        {
                            rty::RefinedTypeVar::Value
                        }
                        v => v,
                    })
                })
                .collect(),
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
        let ty = UnrefinedTypeGeneratorWrapper(&mut self.gen).unrefined_ty(self.ret_ty);
        self.ret_rty = Some(rty::RefinedType::new(ty.vacuous(), refinement));
        self
    }

    pub fn ret_rty(&mut self, rty: rty::RefinedType<rty::FunctionParamIdx>) -> &mut Self {
        self.ret_rty = Some(rty);
        self
    }

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
                            let ty = UnrefinedTypeGeneratorWrapper(&mut self.gen)
                                .unrefined_ty(param_ty.ty);
                            rty::RefinedType::new(ty.vacuous(), param_refinement.clone())
                        } else {
                            self.gen
                                .build_template_ty_with_scope(&builder)
                                .refined_ty(param_ty.ty)
                        }
                    } else {
                        rty::RefinedType::unrefined(
                            self.gen
                                .build_template_ty_with_scope(&builder)
                                .ty(param_ty.ty),
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
                let unit_ty = mir_ty::Ty::new_unit(self.gen.tcx());
                self.gen
                    .build_template_ty_with_scope(&builder)
                    .refined_ty(unit_ty)
            };
            param_rtys.push(param_rty);
        }

        let ret_rty = self.ret_rty.clone().unwrap_or_else(|| {
            self.gen
                .build_template_ty_with_scope(&builder)
                .refined_ty(self.ret_ty)
        });
        rty::FunctionType::new(param_rtys, ret_rty)
    }
}

#[derive(Debug)]
pub struct BasicBlockTemplateTypeBuilder<'a, 'tcx, T: ?Sized> {
    inner: FunctionTemplateTypeBuilder<'a, 'tcx, T>,
    locals: IndexVec<rty::FunctionParamIdx, (Local, mir_ty::Mutability)>,
}

impl<'a, 'tcx, T> BasicBlockTemplateTypeBuilder<'a, 'tcx, T>
where
    T: TemplateTypeGenerator<'tcx> + ?Sized,
{
    #[allow(dead_code)]
    pub fn param_refinement(
        &mut self,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        self.inner.param_refinement(refinement);
        self
    }

    #[allow(dead_code)]
    pub fn ret_rty(&mut self, rty: rty::RefinedType<rty::FunctionParamIdx>) -> &mut Self {
        self.inner.ret_rty(rty);
        self
    }

    pub fn build(&mut self) -> BasicBlockType {
        let ty = self.inner.build();
        BasicBlockType {
            ty,
            locals: self.locals.clone(),
        }
    }
}

#[derive(Debug)]
pub struct TemplateTypeBuilder<'a, T: ?Sized, U, V> {
    // can't use T: TemplateTypeGenerator<'tcx> directly because of recursive instantiation
    gen: &'a mut T,
    scope: U,
    _marker: std::marker::PhantomData<fn() -> V>,
}

impl<'a, 'tcx, T, U, V> TemplateTypeBuilder<'a, T, U, V>
where
    T: TemplateTypeGenerator<'tcx> + ?Sized,
    U: TemplateScope<V>,
    V: chc::Var,
{
    pub fn ty(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::Type<V> {
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Uint(_) | mir_ty::TyKind::Int(_) => rty::Type::int(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
                let elem_ty = self.ty(*elem_ty);
                match mutbl {
                    mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                    mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
                }
            }
            mir_ty::TyKind::Tuple(ts) => {
                // elaboration: all fields are boxed
                let elems = ts
                    .iter()
                    .map(|ty| rty::PointerType::own(self.ty(ty)).into())
                    .collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
            mir_ty::TyKind::Param(ty) => rty::ParamType::new(ty.index.into()).into(),
            mir_ty::TyKind::FnPtr(sig) => {
                // TODO: justification for skip_binder
                let sig = sig.skip_binder();
                let ty = self.gen.function_template_ty(sig);
                rty::Type::function(ty)
            }
            mir_ty::TyKind::Adt(def, params) if def.is_box() => {
                rty::PointerType::own(self.ty(params.type_at(0))).into()
            }
            mir_ty::TyKind::Adt(def, params) => {
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.gen.tcx(), def.did());
                    let args: IndexVec<_, _> =
                        params.types().map(|ty| self.refined_ty(ty)).collect();
                    rty::EnumType::new(sym, args).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.gen.tcx(), params);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.ty(ty)).into()
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

    pub fn refined_ty(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::RefinedType<V> {
        // TODO: consider building ty with scope
        let ty = self.gen.build_template_ty().ty(ty);
        let tmpl = self.scope.build_template().build(ty);
        self.gen.register_template(tmpl)
    }
}

pub trait UnrefinedTypeGenerator<'tcx> {
    fn tcx(&self) -> mir_ty::TyCtxt<'tcx>;

    // TODO: consolidate two defs
    fn unrefined_ty(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::Type<rty::Closed> {
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Uint(_) | mir_ty::TyKind::Int(_) => rty::Type::int(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
                let elem_ty = self.unrefined_ty(*elem_ty);
                match mutbl {
                    mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                    mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
                }
            }
            mir_ty::TyKind::Tuple(ts) => {
                // elaboration: all fields are boxed
                let elems = ts
                    .iter()
                    .map(|ty| rty::PointerType::own(self.unrefined_ty(ty)).into())
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
                    .map(|ty| rty::RefinedType::unrefined(self.unrefined_ty(*ty)).vacuous())
                    .collect();
                let ret = rty::RefinedType::unrefined(self.unrefined_ty(sig.output()));
                rty::FunctionType::new(params, ret.vacuous()).into()
            }
            mir_ty::TyKind::Adt(def, params) if def.is_box() => {
                rty::PointerType::own(self.unrefined_ty(params.type_at(0))).into()
            }
            mir_ty::TyKind::Adt(def, params) => {
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.tcx(), def.did());
                    let args: IndexVec<_, _> = params
                        .types()
                        .map(|ty| rty::RefinedType::unrefined(self.unrefined_ty(ty)))
                        .collect();
                    rty::EnumType::new(sym, args).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.tcx(), params);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.unrefined_ty(ty)).into()
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
}

struct UnrefinedTypeGeneratorWrapper<T>(T);

impl<'tcx, T> UnrefinedTypeGenerator<'tcx> for UnrefinedTypeGeneratorWrapper<T>
where
    T: TemplateTypeGenerator<'tcx>,
{
    fn tcx(&self) -> mir_ty::TyCtxt<'tcx> {
        self.0.tcx()
    }
}
