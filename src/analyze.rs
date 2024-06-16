use std::collections::HashMap;

use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, LocalDefId};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{BasicBlockType, RefineCtxt};
use crate::rty::{self, ClauseBuilderExt as _};

mod annot;
mod basic_block;
mod crate_;
mod local_def;

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    // currently contains only local-def templates,
    // but will be extended to contain externally known def's refinement types
    // (at least for every defs referenced by local def bodies)
    rcx: RefineCtxt,

    basic_blocks: HashMap<LocalDefId, HashMap<BasicBlock, BasicBlockType>>,
}

impl<'tcx> crate::refine::PredVarGenerator for Analyzer<'tcx> {
    fn generate_pred_var(&mut self, pred_sig: chc::PredSig) -> chc::PredVarId {
        self.rcx.generate_pred_var(pred_sig)
    }
}

impl<'tcx> Analyzer<'tcx> {
    fn relate_sub_type(&mut self, got: &rty::Type, expected: &rty::Type) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_type");

        match (got, expected) {
            (rty::Type::Unit, rty::Type::Unit)
            | (rty::Type::Int, rty::Type::Int)
            | (rty::Type::Bool, rty::Type::Bool)
            | (rty::Type::String, rty::Type::String)
            | (rty::Type::Never, rty::Type::Never) => {}
            (rty::Type::Pointer(got), rty::Type::Pointer(expected))
                if got.kind == expected.kind =>
            {
                match got.kind {
                    rty::PointerKind::Own | rty::PointerKind::Ref(rty::RefKind::Immut) => {
                        self.relate_sub_type(&got.elem, &expected.elem);
                    }
                    rty::PointerKind::Ref(rty::RefKind::Mut) => {
                        self.relate_equal_type(&got.elem, &expected.elem);
                    }
                }
            }
            (rty::Type::Function(got), rty::Type::Function(expected)) => {
                // TODO: check sty and length is equal
                // TODO: add value_var dependency
                let mut builder = chc::ClauseBuilder::default();
                for (param_idx, param_rty) in got.params.iter_enumerated() {
                    if let Some(sort) = param_rty.ty.to_sort() {
                        builder.add_mapped_var(param_idx, sort);
                    }
                }
                for (got_ty, expected_ty) in got.params.iter().zip(expected.params.clone()) {
                    let clause = builder
                        .clone()
                        .with_value_var(&got_ty.ty)
                        .add_body(expected_ty.refinement)
                        .head(got_ty.refinement.clone());
                    self.add_clause(clause);
                    self.relate_sub_type(&expected_ty.ty, &got_ty.ty);
                }
                let clause = builder
                    .with_value_var(&got.ret.ty)
                    .add_body(got.ret.refinement.clone())
                    .head(expected.ret.refinement.clone());
                self.add_clause(clause);
                self.relate_sub_type(&got.ret.ty, &expected.ret.ty);
            }
            _ => panic!(
                "inconsistent types: got={}, expected={}",
                got.display(),
                expected.display()
            ),
        }
    }

    fn relate_equal_type(&mut self, got: &rty::Type, expected: &rty::Type) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "equal_type");

        self.relate_sub_type(got, expected);
        self.relate_sub_type(expected, got);
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let rcx = RefineCtxt::default();
        let basic_blocks = HashMap::default();
        Self {
            tcx,
            rcx,
            basic_blocks,
        }
    }

    pub fn add_clause(&mut self, clause: chc::Clause) {
        self.rcx.add_clause(clause);
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        self.rcx.register_def(def_id, rty)
    }

    pub fn def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.rcx.def_ty(def_id)
    }

    pub fn register_basic_block_ty(
        &mut self,
        def_id: LocalDefId,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        tracing::debug!(def_id = ?def_id, ?bb, rty = %rty.display(), "register_basic_block_ty");
        self.basic_blocks.entry(def_id).or_default().insert(bb, rty);
    }

    pub fn basic_block_ty(&self, def_id: LocalDefId, bb: BasicBlock) -> &BasicBlockType {
        &self.basic_blocks[&def_id][&bb]
    }

    pub fn register_well_known_defs(&mut self) {
        let panic_ty = {
            let param = rty::RefinedType::new(
                rty::PointerType::immut_to(rty::Type::string()).into(),
                rty::Refinement::bottom(),
            );
            let ret = rty::RefinedType::new(rty::Type::never(), rty::Refinement::bottom());
            rty::FunctionType::new([param.vacuous()].into_iter().collect(), ret)
        };
        let panic_def_id = self.tcx.require_lang_item(LangItem::Panic, None);
        self.register_def(panic_def_id, rty::RefinedType::unrefined(panic_ty.into()));
    }

    pub fn crate_analyzer(&mut self) -> crate_::Analyzer<'tcx, '_> {
        crate_::Analyzer::new(self)
    }

    pub fn local_def_analyzer(
        &mut self,
        local_def_id: LocalDefId,
    ) -> local_def::Analyzer<'tcx, '_> {
        local_def::Analyzer::new(self, local_def_id)
    }

    pub fn basic_block_analyzer(
        &mut self,
        local_def_id: LocalDefId,
        bb: BasicBlock,
    ) -> basic_block::Analyzer<'tcx, '_> {
        basic_block::Analyzer::new(self, local_def_id, bb)
    }

    pub fn solve(&mut self) {
        if let Err(err) = self.rcx.solve() {
            self.tcx.dcx().err(format!("verification error: {:?}", err));
        }
    }
}
