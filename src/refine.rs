use std::collections::HashMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Mutability};
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty;

mod basic_block;
pub use basic_block::{BasicBlockType, RefineBasicBlockCtxt};

mod env;
pub use env::{Env, TempVarIdx, Var};

mod body;
pub use body::RefineBodyCtxt;

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

#[derive(Debug, Clone, Default)]
pub struct RefineCtxt {
    /// Collection of refined known def types.
    defs: HashMap<DefId, rty::RefinedType>,

    /// Resulting CHC system.
    system: chc::System,
}

impl RefineCtxt {
    pub fn system(&self) -> &chc::System {
        &self.system
    }

    pub fn add_clause(&mut self, clause: chc::Clause) {
        tracing::debug!(clause = %clause.display(), id = ?self.system.clauses.next_index(), "add_clause");
        self.system.clauses.push(clause);
    }

    pub fn mir_ty(&mut self, ty: mir_ty::Ty<'_>) -> rty::Type {
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
            mir_ty::TyKind::Tuple(ts) if ts.is_empty() => rty::Type::unit(),
            mir_ty::TyKind::Never => rty::Type::never(),
            kind => unimplemented!("mir_ty: {:?}", kind),
        }
    }

    pub fn register_template<FV>(&mut self, tmpl: rty::Template<FV>) -> rty::RefinedType<FV> {
        tmpl.into_refined_type(|pred_sig| self.system.new_pred_var(pred_sig))
    }

    fn mir_function_ty_impl<'tcx, I>(&mut self, params: I, ret_ty: rty::Type) -> rty::FunctionType
    where
        I: IntoIterator<Item = mir_ty::TypeAndMut<'tcx>>,
    {
        let mut param_rtys = IndexVec::<rty::FunctionParamIdx, _>::new();
        let mut builder = rty::TemplateBuilder::default();
        for param_ty in params.into_iter() {
            // elaboration: treat mutabully declared variables as own
            let param_ty = if param_ty.mutbl.is_mut() {
                rty::PointerType::own(self.mir_ty(param_ty.ty)).into()
            } else {
                self.mir_ty(param_ty.ty)
            };
            let tmpl = builder.clone().build(param_ty.clone());
            let param_rty = self.register_template(tmpl);
            let param_idx = param_rtys.push(param_rty);

            if let Some(param_sort) = param_ty.to_sort() {
                builder.add_dependency(param_idx.into(), param_sort);
            }
        }
        if param_rtys.is_empty() {
            // elaboration: we need at least one predicate variable in parameter
            let tmpl = builder.clone().build(rty::Type::unit());
            let param_rty = self.register_template(tmpl);
            param_rtys.push(param_rty);
        }

        let tmpl = builder.build(ret_ty);
        let ret_rty = self.register_template(tmpl);
        rty::FunctionType::new(param_rtys, ret_rty)
    }

    pub fn mir_basic_block_ty<'tcx, I>(
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
        let ret_ty = self.mir_ty(ret_ty);
        let ty = self.mir_function_ty_impl(tys, ret_ty);
        BasicBlockType { ty, locals }
    }

    pub fn mir_function_ty(&mut self, sig: mir_ty::FnSig<'_>) -> rty::FunctionType {
        let ret_ty = self.mir_ty(sig.output());
        self.mir_function_ty_impl(
            sig.inputs().iter().map(|ty| mir_ty::TypeAndMut {
                ty: *ty,
                mutbl: Mutability::Not,
            }),
            ret_ty,
        )
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        tracing::debug!(def_id = ?def_id, rty = %rty.display(), "register_def");
        self.defs.insert(def_id, rty);
    }

    pub fn def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.defs.get(&def_id)
    }

    pub fn body_ctxt(&mut self) -> RefineBodyCtxt<'_> {
        RefineBodyCtxt::new(self)
    }
}
