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

fn function_ty_impl<'a, 'tcx, T>(
    g: &'a mut T,
    params: Vec<mir_ty::TypeAndMut<'tcx>>,
    ret_ty: mir_ty::Ty<'tcx>,
) -> rty::FunctionType
where
    T: TemplateTypeGenerator<'tcx> + ?Sized,
{
    let mut builder = rty::TemplateBuilder::default();
    let mut param_rtys = IndexVec::<rty::FunctionParamIdx, _>::new();
    for (idx, param_ty) in params.iter().enumerate() {
        let param_rty = if idx == params.len() - 1 {
            g.build_template_ty(&builder).refined_ty(param_ty.ty)
        } else {
            rty::RefinedType::unrefined(g.build_template_ty(&builder).ty(param_ty.ty))
        };
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
    if params.is_empty() {
        let unit_ty = mir_ty::Ty::new_unit(g.tcx());
        let param_rty = g.build_template_ty(&builder).refined_ty(unit_ty);
        param_rtys.push(param_rty);
    }

    let ret_rty = g.build_template_ty(&builder).refined_ty(ret_ty);
    rty::FunctionType::new(param_rtys, ret_rty)
}

pub trait TemplateTypeGenerator<'tcx> {
    fn tcx(&self) -> mir_ty::TyCtxt<'tcx>;
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V>;

    fn build_template_ty<T, V>(&mut self, scope: T) -> TemplateTypeBuilder<Self, T, V> {
        TemplateTypeBuilder {
            gen: self,
            scope,
            _marker: std::marker::PhantomData,
        }
    }

    fn basic_block_template_ty<I>(
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
        let ty = function_ty_impl(self, tys, ret_ty);
        BasicBlockType { ty, locals }
    }

    fn function_template_ty(&mut self, sig: mir_ty::FnSig<'tcx>) -> rty::FunctionType {
        function_ty_impl(
            self,
            sig.inputs()
                .iter()
                .map(|ty| mir_ty::TypeAndMut {
                    ty: *ty,
                    mutbl: Mutability::Not,
                })
                .collect(),
            sig.output(),
        )
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
            mir_ty::TyKind::Int(_) => rty::Type::int(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
                let elem_ty = self.ty(*elem_ty);
                match mutbl {
                    mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                    mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
                }
            }
            mir_ty::TyKind::Tuple(ts) => {
                let elems = ts.iter().map(|ty| self.ty(ty)).collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
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
                    rty::EnumType::new(sym).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.gen.tcx(), params);
                            self.ty(ty)
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
        let ty = self.ty(ty);
        let tmpl = self.scope.build_template().build(ty);
        self.gen.register_template(tmpl)
    }
}

// TODO: consolidate two defs
pub fn unrefined_ty<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> rty::Type<rty::Closed> {
    match ty.kind() {
        mir_ty::TyKind::Bool => rty::Type::bool(),
        mir_ty::TyKind::Int(_) => rty::Type::int(),
        mir_ty::TyKind::Str => rty::Type::string(),
        mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
            let elem_ty = unrefined_ty(tcx, *elem_ty);
            match mutbl {
                mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
            }
        }
        mir_ty::TyKind::Tuple(ts) => {
            let elems = ts.iter().map(|ty| unrefined_ty(tcx, ty)).collect();
            rty::TupleType::new(elems).into()
        }
        mir_ty::TyKind::Never => rty::Type::never(),
        mir_ty::TyKind::FnPtr(sig) => {
            // TODO: justification for skip_binder
            let sig = sig.skip_binder();
            let params = sig
                .inputs()
                .iter()
                .map(|ty| rty::RefinedType::unrefined(unrefined_ty(tcx, *ty)).vacuous())
                .collect();
            let ret = rty::RefinedType::unrefined(unrefined_ty(tcx, sig.output()));
            rty::FunctionType::new(params, ret.vacuous()).into()
        }
        mir_ty::TyKind::Adt(def, params) if def.is_box() => {
            rty::PointerType::own(unrefined_ty(tcx, params.type_at(0))).into()
        }
        mir_ty::TyKind::Adt(def, params) => {
            if def.is_enum() {
                let sym = refine::datatype_symbol(tcx, def.did());
                rty::EnumType::new(sym).into()
            } else if def.is_struct() {
                let elem_tys = def
                    .all_fields()
                    .map(|field| {
                        let ty = field.ty(tcx, params);
                        unrefined_ty(tcx, ty)
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
