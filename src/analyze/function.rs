use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::{self, BasicBlock, Body};
use rustc_middle::ty::{TyCtxt, TypeAndMut};

use crate::error::Result;
use crate::refine::{BasicBlockType, RefineBodyCtxt, RefineCtxt};
use crate::rty::{FunctionType, PointerType};

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
                .map(|in_local| {
                    let decl = &self.body.local_decls[in_local];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    (in_local, type_and_mut)
                })
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
        use rustc_middle::mir::{BorrowKind, PlaceElem, Rvalue, TerminatorKind};

        for (stmt_idx, stmt) in data.statements.iter().enumerate() {
            if let Some((p, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))) = stmt.kind.as_assign() {
                if p.projection.len() != 0 {
                    unimplemented!();
                }
                // TODO: is it appropriate to use builtin_deref here... maybe we should handle dereferencing logic in `refine`
                let inner_ty = self.body.local_decls[p.local]
                    .ty
                    .builtin_deref(true)
                    .unwrap()
                    .ty;
                ecx.add_prophecy_var(stmt_idx, inner_ty);
            }
        }

        for (stmt_idx, stmt) in data.statements.iter().enumerate() {
            tracing::debug!(%stmt_idx, stmt = ?stmt);
            match stmt.kind.as_assign() {
                Some((p, Rvalue::Ref(_, BorrowKind::Mut { .. }, referent)))
                    if p.projection.len() == 0 && referent.projection.len() == 0 =>
                {
                    // mutable borrow
                    let decl = &self.body.local_decls[p.local];
                    let rty = ecx.borrow_local(stmt_idx, referent.local);
                    ecx.bind_local(p.local, rty, decl.mutability);
                }
                Some((p, rvalue)) if p.projection.len() == 0 && !ecx.is_known_local(p.local) => {
                    // new binding
                    let decl = &self.body.local_decls[p.local];
                    let rty = ecx.mir_refined_ty(decl.ty);
                    // TODO: maybe we should tie them together in ecx
                    ecx.type_rvalue(rvalue.clone(), &rty);
                    ecx.bind_local(p.local, rty, decl.mutability);
                }
                Some((p, Rvalue::Use(operand)))
                    if p.projection.as_slice() == &[PlaceElem::Deref] =>
                {
                    // assignment
                    ecx.assign_to_local(p.local, operand.clone());
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

                let decl = &self.body.local_decls[destination];
                let rty = ecx.mir_refined_ty(decl.ty);
                ecx.type_call(func.clone(), args.clone().into_iter().map(|a| a.node), &rty);
                ecx.bind_local(destination, rty, decl.mutability);
                if let Some(target) = target {
                    ecx.type_goto(*target, &expected_ret);
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
