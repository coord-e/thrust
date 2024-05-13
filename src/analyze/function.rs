use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::{self, BasicBlock, Body};
use rustc_middle::ty::TyCtxt;

use crate::error::Result;
use crate::refine::{BasicBlockType, RefineBodyCtxt, RefineCtxt};
use crate::rty::FunctionType;

pub struct FunctionAnalyzer<'rcx, 'tcx, 'mir> {
    tcx: TyCtxt<'tcx>,
    bcx: RefineBodyCtxt<'rcx>,

    body: &'mir Body<'tcx>,
}

impl<'rcx, 'tcx, 'mir> FunctionAnalyzer<'rcx, 'tcx, 'mir> {
    pub fn new(tcx: TyCtxt<'tcx>, rcx: &'rcx mut RefineCtxt, body: &'mir Body<'tcx>) -> Self {
        let bcx = rcx.body_ctxt();
        Self { tcx, bcx, body }
    }

    pub fn rcx(&self) -> &RefineCtxt {
        self.bcx.rcx()
    }

    pub fn rcx_mut(&mut self) -> &mut RefineCtxt {
        self.bcx.rcx_mut()
    }

    fn refine_basic_blocks(&mut self) {
        use rustc_mir_dataflow::Analysis as _;
        let mut results = rustc_mir_dataflow::impls::MaybeLiveLocals
            .into_engine(self.tcx, self.body)
            .iterate_to_fixpoint()
            .into_results_cursor(self.body);

        for bb in self.body.basic_blocks.indices() {
            results.seek_to_block_start(bb);
            let bb_ins = results.get();

            let live_locals: Vec<_> = bb_ins
                .iter()
                .map(|in_local| (in_local, self.body.local_decls[in_local].ty))
                .collect();
            // function return type is basic block return type
            let ret_ty = self.body.local_decls[mir::RETURN_PLACE].ty;
            let rty = self.rcx_mut().mir_basic_block_ty(live_locals, ret_ty);
            self.bcx.register_basic_block(bb, rty);
        }
    }

    #[tracing::instrument(name = "bb", skip(self, expected))]
    fn type_basic_block(&mut self, bb: BasicBlock, expected: &BasicBlockType) -> Result<()> {
        let mut ecx = self.bcx.basic_block_ctxt();
        let expected_ret = ecx.bind_locals(&expected);

        let data = &self.body.basic_blocks[bb];
        use rustc_middle::mir::{Rvalue, StatementKind, TerminatorKind};
        for stmt in &data.statements {
            tracing::debug!(stmt = ?stmt);
            match &stmt.kind {
                StatementKind::Assign(d) => {
                    let (local, operand) = match &**d {
                        (p, Rvalue::Use(op)) if p.projection.len() == 0 => (p.local, op),
                        _ => unimplemented!(),
                    };
                    if ecx.is_known_local(local) {
                        unimplemented!()
                    }

                    let rty = ecx.mir_refined_ty(self.body.local_decls[local].ty);
                    // TODO: maybe we should tie them together in ecx
                    ecx.type_operand(operand.clone(), &rty);
                    ecx.bind_local(local, rty);
                }
                _ => {
                    tracing::warn!(stmt = ?stmt, "skipped");
                    // unimplemented!();
                }
            }
        }

        let term = &data.terminator().kind;
        tracing::debug!(term = ?term);
        match term {
            TerminatorKind::Return => {
                ecx.type_return(&expected_ret);
            }
            TerminatorKind::Goto { target } => {
                ecx.type_goto(*target, &expected_ret);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                ecx.type_switch_int(discr.clone(), targets.clone(), &expected_ret);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                // TODO: maybe we should tie them together in ecx
                let destination = match destination {
                    p if p.projection.len() == 0 => p.local,
                    _ => unimplemented!(),
                };
                if ecx.is_known_local(destination) {
                    unimplemented!()
                }

                let panic_def_id = self.tcx.require_lang_item(LangItem::Panic, None);
                // TODO: ad-hoc. should be implemented by inserting panic into rcx.defs
                if matches!(func.const_fn_def(), Some((def_id, _)) if def_id == panic_def_id) {
                    ecx.type_panic();
                } else {
                    let rty = ecx.mir_refined_ty(self.body.local_decls[destination].ty);
                    ecx.type_call(func.clone(), args.clone().into_iter().map(|a| a.node), &rty);
                    ecx.bind_local(destination, rty);
                    if let Some(target) = target {
                        ecx.type_goto(*target, &expected_ret);
                    } else {
                        // TODO: what
                        unimplemented!();
                    }
                }
            }
            _ => {
                tracing::warn!(term = ?term, "skipped");
                // unimplemented!();
            }
        }

        Ok(())
    }

    pub fn run(&mut self, expected: &FunctionType) -> Result<()> {
        self.refine_basic_blocks();

        for bb in self.body.basic_blocks.indices() {
            // BasicBlockAnalyzer::new(self.tcx, &mut self.bcx, self.data, bb).run()?;
            // TODO: remove clone
            let rty = self.bcx.basic_block_ty(bb).clone();
            self.type_basic_block(bb, &rty)?;
        }

        let mut ecx = self.bcx.basic_block_ctxt();
        let ret = ecx.bind_params(expected.clone());
        ecx.type_goto(mir::START_BLOCK, &ret);

        Ok(())
    }
}
