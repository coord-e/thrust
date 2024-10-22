use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Mutability};
use rustc_middle::ty as mir_ty;

use super::basic_block::BasicBlockType;
use crate::chc;
use crate::refine;
use crate::rty;

pub trait PredVarGenerator {
    fn generate_pred_var(&mut self, pred_sig: chc::PredSig) -> chc::PredVarId;
}

fn mir_function_ty_impl<'tcx, T, I>(
    g: &mut T,
    params: I,
    ret_ty: rty::Type<rty::Closed>,
) -> rty::FunctionType
where
    T: TemplateTypeGenerator<'tcx> + ?Sized,
    I: IntoIterator<Item = mir_ty::TypeAndMut<'tcx>>,
{
    let param_tys: Vec<_> = params
        .into_iter()
        .map(|param_ty| {
            // elaboration: treat mutabully declared variables as own
            if param_ty.mutbl.is_mut() {
                rty::PointerType::own(g.mir_ty(param_ty.ty)).into()
            } else {
                g.mir_ty(param_ty.ty)
            }
        })
        .collect();

    let mut builder = rty::TemplateBuilder::default();
    let mut param_rtys = IndexVec::<rty::FunctionParamIdx, _>::new();
    if let Some(param_ty) = param_tys.last() {
        for param_ty in param_tys.iter().take(param_tys.len() - 1) {
            let param_idx =
                param_rtys.push(rty::RefinedType::unrefined(param_ty.clone()).vacuous());
            builder.add_dependency(param_idx.into(), param_ty.to_sort());
        }
        let tmpl = builder.clone().build(param_ty.clone().vacuous());
        let param_rty = g.register_template(tmpl);
        let param_idx = param_rtys.push(param_rty);
        builder.add_dependency(param_idx.into(), param_ty.to_sort());
    } else {
        // elaboration: we need at least one predicate variable in parameter
        let tmpl = builder.clone().build(rty::Type::unit());
        let param_rty = g.register_template(tmpl);
        param_rtys.push(param_rty);
    }

    let tmpl = builder.build(ret_ty.vacuous());
    let ret_rty = g.register_template(tmpl);
    rty::FunctionType::new(param_rtys, ret_rty)
}

pub trait TemplateTypeGenerator<'tcx>: PredVarGenerator {
    fn tcx(&self) -> mir_ty::TyCtxt<'tcx>;

    fn register_template<FV>(&mut self, tmpl: rty::Template<FV>) -> rty::RefinedType<FV> {
        tmpl.into_refined_type(|pred_sig| self.generate_pred_var(pred_sig))
    }

    fn mir_ty(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::Type<rty::Closed> {
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Int(_) => rty::Type::int(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mutbl) => {
                let elem_ty = self.mir_ty(*elem_ty);
                match mutbl {
                    mir_ty::Mutability::Mut => rty::PointerType::mut_to(elem_ty).into(),
                    mir_ty::Mutability::Not => rty::PointerType::immut_to(elem_ty).into(),
                }
            }
            mir_ty::TyKind::Tuple(ts) => {
                let elems = ts.iter().map(|ty| self.mir_ty(ty)).collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
            mir_ty::TyKind::FnPtr(sig) => {
                // TODO: justification for skip_binder
                let sig = sig.skip_binder();
                let ty = self.mir_function_ty(sig);
                rty::Type::function(ty)
            }
            mir_ty::TyKind::Adt(def, params) if def.is_box() => {
                rty::PointerType::own(self.mir_ty(params.type_at(0))).into()
            }
            mir_ty::TyKind::Adt(def, params) => {
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.tcx(), def.did());
                    rty::EnumType::new(sym).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.tcx(), params);
                            self.mir_ty(ty)
                        })
                        .collect();
                    rty::TupleType::new(elem_tys).into()
                } else {
                    unimplemented!("unsupported ADT: {:?}", ty);
                }
            }
            kind => unimplemented!("mir_ty: {:?}", kind),
        }
    }

    fn mir_basic_block_ty<I>(&mut self, live_locals: I, ret_ty: mir_ty::Ty<'tcx>) -> BasicBlockType
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
        let ret_ty = self.mir_ty(ret_ty);
        let ty = mir_function_ty_impl(self, tys, ret_ty);
        BasicBlockType { ty, locals }
    }

    fn mir_function_ty(&mut self, sig: mir_ty::FnSig<'tcx>) -> rty::FunctionType {
        let ret_ty = self.mir_ty(sig.output());
        mir_function_ty_impl(
            self,
            sig.inputs().iter().map(|ty| mir_ty::TypeAndMut {
                ty: *ty,
                mutbl: Mutability::Not,
            }),
            ret_ty,
        )
    }
}
