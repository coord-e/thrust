use crate::chc;
use crate::error::Result;
use crate::refine::RefineCtxt;
use crate::rty::{self, ClauseBuilderExt as _, RefinedType};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;

mod function;
pub use function::FunctionAnalyzer;

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    // currently contains only local-def templates,
    // but will be extended to contain externally known def's refinement types
    // (at least for every defs referenced by local def bodies)
    rcx: RefineCtxt,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let rcx = RefineCtxt::default();
        Self { tcx, rcx }
    }

    fn refine_local_defs(&mut self) {
        for local_def_id in self.tcx.mir_keys(()) {
            self.refine_def(local_def_id.to_def_id());
        }
    }

    fn refine_def(&mut self, def_id: DefId) {
        let sig = self.tcx.fn_sig(def_id);
        let sig = sig.instantiate_identity().skip_binder(); // TODO: is it OK?
        let rty = self.rcx.mir_function_ty(sig);
        let rty = RefinedType::unrefined(rty.into());
        self.rcx.register_def(def_id, rty);
    }

    pub fn run(&mut self) -> Result<()> {
        self.refine_local_defs();

        for local_def_id in self.tcx.mir_keys(()) {
            let body = self.tcx.optimized_mir(local_def_id.to_def_id());
            let expected = self.rcx.def_ty(local_def_id.to_def_id()).unwrap().clone();
            let _span = tracing::span!(
                tracing::Level::INFO, "def",
                def = %self.tcx.def_path_str(local_def_id.to_def_id()),
            )
            .entered();
            if let rty::Type::Function(expected) = expected.ty {
                FunctionAnalyzer::new(self.tcx, &mut self.rcx, body).run(&expected)?;
            } else {
                unimplemented!()
            }
        }

        if let Some((def_id, _)) = self.tcx.entry_fn(()) {
            // we want to assert entry function is safe to execute without any assumption
            // TODO: replace code here with relate_* in Env + Refine context (created with empty env)
            let entry_ty = self
                .rcx
                .def_ty(def_id)
                .unwrap()
                .ty
                .as_function()
                .unwrap()
                .clone();
            let mut builder = chc::ClauseBuilder::default();
            for (param_idx, param_ty) in entry_ty.params.iter_enumerated() {
                if let Some(sort) = param_ty.ty.to_sort() {
                    builder.add_mapped_var(param_idx, sort);
                }
            }
            builder.add_body(chc::Atom::top());
            for param_ty in entry_ty.params {
                let clause = builder
                    .clone()
                    .with_value_var(&param_ty.ty)
                    .head(param_ty.refinement);
                self.rcx.add_clause(clause);
            }
        }

        self.rcx.system().solve()?;
        Ok(())
    }
}
