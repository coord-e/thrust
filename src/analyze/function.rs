use std::collections::HashMap;

use rustc_hir::lang_items::LangItem;
use rustc_index::{bit_set::BitSet, IndexVec};
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeAndMut};

use crate::error::Result;
use crate::refine::{BasicBlockType, RefineBasicBlockCtxt, RefineBodyCtxt, RefineCtxt};
use crate::rty::{FunctionType, PointerType};

struct RenameLocalVisitor<'tcx> {
    from: Local,
    to: Local,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for RenameLocalVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_local(&mut self, local: &mut Local, _: mir::visit::PlaceContext, _: mir::Location) {
        if *local == self.from {
            *local = self.to;
        }
    }
}

struct ReborrowVisitor<'a, 'tcx, 'rcx, 'bcx> {
    tcx: TyCtxt<'tcx>,
    ecx: &'a mut RefineBasicBlockCtxt<'rcx, 'bcx>,
    local_decls: &'a mut IndexVec<Local, mir::LocalDecl<'tcx>>,
}

impl<'tcx> ReborrowVisitor<'_, 'tcx, '_, '_> {
    fn insert_reborrow(&mut self, local: Local, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, self.local_decls[local].source_info.span);
        let new_local = self.local_decls.push(decl);
        let place = if self.ecx.is_mut_local(local) {
            mir::Place::from(local).project_deeper(&[mir::PlaceElem::Deref], self.tcx)
        } else {
            local.into()
        };
        let new_local_ty = self.ecx.borrow_place_(place, inner_ty);
        self.ecx
            .bind_local(new_local, new_local_ty, mir::Mutability::Not);
        tracing::info!(old_local = ?local, ?new_local, "implicitly reborrowed");
        new_local
    }
}

impl<'a, 'tcx, 'rcx, 'bcx> mir::visit::MutVisitor<'tcx> for ReborrowVisitor<'a, 'tcx, 'rcx, 'bcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_assign(
        &mut self,
        place: &mut mir::Place<'tcx>,
        rvalue: &mut mir::Rvalue<'tcx>,
        location: mir::Location,
    ) {
        if place.projection.as_slice() != &[mir::PlaceElem::Deref] {
            self.super_assign(place, rvalue, location);
            return;
        }

        let mir_ty::TyKind::Ref(_, inner_ty, m) = self.local_decls[place.local].ty.kind() else {
            self.super_assign(place, rvalue, location);
            return;
        };

        let new_local = self.insert_reborrow(place.local, *inner_ty);
        RenameLocalVisitor {
            from: place.local,
            to: new_local,
            tcx: self.tcx,
        }
        .visit_rvalue(rvalue, location);
        place.local = new_local;
        self.super_assign(place, rvalue, location);
    }

    // TODO: is it always true that the operand is not referred again in rvalue
    fn visit_operand(&mut self, operand: &mut mir::Operand<'tcx>, location: mir::Location) {
        let Some(p) = operand.place() else {
            self.super_operand(operand, location);
            return;
        };

        if p.projection.as_slice() == &[mir::PlaceElem::Deref] {
            self.super_operand(operand, location);
            return;
        }
        if !p.projection.is_empty() {
            unimplemented!();
        }

        let mir_ty::TyKind::Ref(_, inner_ty, m) = self.local_decls[p.local].ty.kind() else {
            self.super_operand(operand, location);
            return;
        };
        if !operand.is_move() && m.is_mut() {
            let new_local = self.insert_reborrow(p.local, *inner_ty);
            *operand = mir::Operand::Move(new_local.into());
        }

        self.super_operand(operand, location);
    }
}

impl<'a, 'tcx, 'rcx, 'bcx> ReborrowVisitor<'a, 'tcx, 'rcx, 'bcx> {
    pub fn visit_statement(&mut self, stmt: &mut mir::Statement<'tcx>) {
        mir::visit::MutVisitor::visit_statement(self, stmt, mir::Location::START);
        // dummy location
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
        // dummy location
    }
}

#[derive(Debug, Clone)]
struct DropPoints {
    after_statements: Vec<BitSet<Local>>,
    after_terminator: HashMap<BasicBlock, BitSet<Local>>,
}

impl DropPoints {
    pub fn after_statement(&self, statement_index: usize) -> BitSet<Local> {
        self.after_statements[statement_index].clone()
    }

    pub fn after_terminator(&self, target: &BasicBlock) -> BitSet<Local> {
        let mut t = self.after_terminator[target].clone();
        t.union(self.after_statements.last().unwrap());
        t
    }
}

fn def_local<'a, 'tcx, T: mir::visit::MirVisitable<'tcx> + ?Sized>(
    visitable: &'a T,
) -> Option<Local> {
    struct Visitor {
        local: Option<Local>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Visitor {
        fn visit_local(
            &mut self,
            local: Local,
            ctxt: mir::visit::PlaceContext,
            _location: mir::Location,
        ) {
            if ctxt.is_place_assignment() {
                let old = self.local.replace(local);
                assert!(old.is_none());
            }
        }
    }
    let mut visitor = Visitor { local: None };
    visitable.apply(mir::Location::START, &mut visitor);
    visitor.local
}

pub struct FunctionAnalyzer<'rcx, 'tcx, 'mir> {
    tcx: TyCtxt<'tcx>,
    bcx: RefineBodyCtxt<'rcx>,

    body: &'mir Body<'tcx>,
    drop_points: HashMap<BasicBlock, DropPoints>,
}

impl<'rcx, 'tcx, 'mir> FunctionAnalyzer<'rcx, 'tcx, 'mir> {
    pub fn new(tcx: TyCtxt<'tcx>, rcx: &'rcx mut RefineCtxt, body: &'mir Body<'tcx>) -> Self {
        let bcx = rcx.body_ctxt();
        let drop_points = Default::default();
        Self {
            tcx,
            bcx,
            body,
            drop_points,
        }
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

        let mut bb_ins = HashMap::new();
        for (bb, data) in mir::traversal::postorder(self.body) {
            let mut after_terminator = HashMap::new();
            let mut after_statements = Vec::new();
            after_statements.resize_with(data.statements.len() + 1, || BitSet::new_empty(0));

            results.seek_to_block_end(bb);
            let live_locals_after_terminator = results.get().clone();

            use rustc_data_structures::graph::WithSuccessors as _;
            for succ_bb in self.body.basic_blocks.successors(bb) {
                let edge_drops = {
                    let mut t = live_locals_after_terminator.clone();
                    t.subtract(&bb_ins[&succ_bb]);
                    t
                };
                after_terminator.insert(succ_bb, edge_drops);
            }

            let mut last_live_locals = live_locals_after_terminator;
            // TODO: we may use seek_before_primary_effect here
            for statement_index in (0..=data.statements.len()).rev() {
                let loc = mir::Location {
                    statement_index,
                    block: bb,
                };
                results.seek_after_primary_effect(loc);
                let live_locals = results.get().clone();
                after_statements[statement_index] = {
                    let mut t = live_locals.clone();
                    if let Some(def) = def_local(data.visitable(statement_index)) {
                        t.insert(def);
                    }
                    t.subtract(&last_live_locals);
                    t
                };
                last_live_locals = live_locals;
            }

            tracing::info!(
                ?bb,
                ?after_statements,
                ?after_terminator,
                "analyzed implicit drop points"
            );
            self.drop_points.insert(
                bb,
                DropPoints {
                    after_statements,
                    after_terminator,
                },
            );

            bb_ins.insert(bb, last_live_locals.clone());
            let live_locals: Vec<_> = last_live_locals
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
        let mut local_decls = self.body.local_decls.clone();
        use rustc_middle::mir::{BorrowKind, PlaceElem, Rvalue, TerminatorKind};

        for (stmt_idx, stmt) in data.statements.iter().enumerate() {
            if let Some((p, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))) = stmt.kind.as_assign() {
                if p.projection.len() != 0 {
                    unimplemented!();
                }
                // TODO: is it appropriate to use builtin_deref here... maybe we should handle dereferencing logic in `refine`
                let inner_ty = local_decls[p.local].ty.builtin_deref(true).unwrap().ty;
                ecx.add_prophecy_var(stmt_idx, inner_ty);
            }
        }

        for (stmt_idx, mut stmt) in data.statements.iter().cloned().enumerate() {
            tracing::debug!(%stmt_idx, stmt = ?stmt);
            ReborrowVisitor {
                tcx: self.tcx,
                ecx: &mut ecx,
                local_decls: &mut local_decls,
            }
            .visit_statement(&mut stmt);
            match stmt.kind.as_assign() {
                Some((p, Rvalue::Ref(_, BorrowKind::Mut { .. }, referent)))
                    if p.projection.len() == 0 && referent.projection.len() == 0 =>
                {
                    // mutable borrow
                    let decl = &local_decls[p.local];
                    let rty = ecx.borrow_local(stmt_idx, referent.local);
                    ecx.bind_local(p.local, rty, decl.mutability);
                }
                Some((p, rvalue)) if p.projection.len() == 0 && !ecx.is_known_local(p.local) => {
                    // new binding
                    let decl = &local_decls[p.local];
                    let rty = ecx.mir_refined_ty(decl.ty);
                    // TODO: maybe we should tie them together in ecx
                    ecx.type_rvalue(rvalue.clone(), &rty);
                    ecx.bind_local(p.local, rty, decl.mutability);
                }
                Some((p, rvalue)) if p.projection.as_slice() == &[PlaceElem::Deref] => {
                    // assignment
                    ecx.assign_to_local(p.local, rvalue.clone());
                }
                _ => {
                    unimplemented!();
                }
            }
            for local in self.drop_points[&bb].after_statements[stmt_idx].iter() {
                tracing::info!(?local, ?stmt_idx, "implicitly dropped after statement");
                ecx.drop_local(local);
            }
        }

        let mut term = data.terminator().clone();
        ReborrowVisitor {
            tcx: self.tcx,
            ecx: &mut ecx,
            local_decls: &mut local_decls,
        }
        .visit_terminator(&mut term);
        tracing::debug!(term = ?term.kind);
        match &term.kind {
            TerminatorKind::Return => {
                ecx.type_return(&expected_ret);
            }
            TerminatorKind::Goto { target } => {
                ecx.type_goto(*target, &expected_ret);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                ecx.type_switch_int(
                    discr.clone(),
                    targets.clone(),
                    &expected_ret,
                    |ecx, target| {
                        for local in self.drop_points[&bb].after_terminator(&target).iter() {
                            tracing::info!(?local, ?target, "implicitly dropped for target");
                            ecx.drop_local(local);
                        }
                    },
                );
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

                let decl = &local_decls[destination];
                let rty = ecx.mir_refined_ty(decl.ty);
                ecx.type_call(func.clone(), args.clone().into_iter().map(|a| a.node), &rty);
                ecx.bind_local(destination, rty, decl.mutability);
                if let Some(target) = target {
                    for local in self.drop_points[&bb].after_terminator(target).iter() {
                        tracing::info!(?local, "implicitly dropped after call");
                        ecx.drop_local(local);
                    }
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
