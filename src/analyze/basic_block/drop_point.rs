use std::collections::HashMap;

use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};

#[derive(Debug, Clone, Default)]
pub struct DropPoints<'tcx> {
    pub before_statements: Vec<mir::Place<'tcx>>,
    after_statements: Vec<Vec<mir::Place<'tcx>>>,
    after_terminator: HashMap<BasicBlock, Vec<mir::Place<'tcx>>>,
    /// Places dropped after the terminator regardless of the target, in
    /// addition to the liveness-derived sets above.
    after_terminator_extra: Vec<mir::Place<'tcx>>,
}

impl DropPoints<'_> {
    pub fn builder<'mir, 'tcx>(body: &'mir Body<'tcx>) -> DropPointsBuilder<'mir, 'tcx> {
        DropPointsBuilder {
            body,
            bb_ins_cache: HashMap::new(),
        }
    }
}

impl<'tcx> DropPoints<'tcx> {
    pub fn position(&self, place: mir::Place<'tcx>) -> Option<usize> {
        self.after_statements
            .iter()
            .position(|s| s.contains(&place))
            .or_else(|| {
                self.is_after_terminator(place)
                    .then_some(self.after_statements.len())
            })
    }

    fn is_after_terminator(&self, place: mir::Place<'tcx>) -> bool {
        self.after_terminator.values().any(|s| s.contains(&place))
            || self.after_terminator_extra.contains(&place)
    }

    pub fn remove_after_statement(
        &mut self,
        statement_index: usize,
        place: mir::Place<'tcx>,
    ) -> bool {
        if let Some(pos) = self.after_statements[statement_index]
            .iter()
            .position(|p| *p == place)
        {
            self.after_statements[statement_index].remove(pos);
            true
        } else {
            false
        }
    }

    pub fn insert_after_statement(
        &mut self,
        statement_index: usize,
        place: mir::Place<'tcx>,
    ) -> bool {
        let statements = &mut self.after_statements[statement_index];
        if statements.contains(&place) {
            false
        } else {
            statements.push(place);
            true
        }
    }

    pub fn after_statement(&self, statement_index: usize) -> Vec<mir::Place<'tcx>> {
        self.after_statements[statement_index].clone()
    }

    pub fn insert_after_terminator(&mut self, place: mir::Place<'tcx>) {
        if !self.after_terminator_extra.contains(&place) {
            self.after_terminator_extra.push(place);
        }
    }

    pub fn after_terminator(&self, target: &BasicBlock) -> Vec<mir::Place<'tcx>> {
        let mut places = self.after_terminator[target].clone();
        for place in self.after_statements.last().unwrap() {
            if !places.contains(place) {
                places.push(*place);
            }
        }
        for place in &self.after_terminator_extra {
            if !places.contains(place) {
                places.push(*place);
            }
        }
        places
    }
}

#[derive(Debug, Clone)]
pub struct DropPointsBuilder<'mir, 'tcx> {
    body: &'mir Body<'tcx>,
    bb_ins_cache: HashMap<BasicBlock, DenseBitSet<Local>>,
}

/// Locals whose ownership is fully transferred away by the statement (or
/// terminator) at `statement_index`. Such a local is left uninitialized, so its
/// drop obligation (including resolving any mutable-borrow prophecies it owns)
/// moves to the destination and it must not be dropped at the move site.
///
/// Only owned (non-reference) operands are reported: `move`d references are
/// turned into reborrows by `ReborrowVisitor`/`RustCallVisitor`, so the source
/// local remains live and must still be dropped.
fn moved_locals<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    statement_index: usize,
) -> DenseBitSet<Local> {
    struct Visitor<'a, 'tcx> {
        body: &'a Body<'tcx>,
        locals: DenseBitSet<Local>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'_, 'tcx> {
        fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, _location: mir::Location) {
            if let mir::Operand::Move(place) = operand {
                if place.projection.is_empty() && !self.body.local_decls[place.local].ty.is_ref() {
                    self.locals.insert(place.local);
                }
            }
        }
    }
    let mut visitor = Visitor {
        body,
        locals: DenseBitSet::new_empty(body.local_decls.len()),
    };
    let loc = mir::Location {
        statement_index,
        block: bb,
    };
    let data = &body.basic_blocks[bb];
    use mir::visit::Visitor as _;
    if statement_index < data.statements.len() {
        visitor.visit_statement(&data.statements[statement_index], loc);
    } else if let Some(tmnt) = &data.terminator {
        visitor.visit_terminator(tmnt, loc);
    }
    visitor.locals
}

fn def_local<'tcx>(data: &mir::BasicBlockData<'tcx>, statement_index: usize) -> Option<Local> {
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
    let loc = mir::Location::START;
    use mir::visit::Visitor as _;
    if statement_index < data.statements.len() {
        visitor.visit_statement(&data.statements[statement_index], loc);
    } else if let Some(tmnt) = &data.terminator {
        visitor.visit_terminator(tmnt, loc);
    }
    visitor.local
}

impl<'mir, 'tcx> DropPointsBuilder<'mir, 'tcx> {
    pub fn build(
        &mut self,
        results: &mut ResultsCursor<'mir, 'tcx, MaybeLiveLocals>,
        bb: BasicBlock,
    ) -> DropPoints<'tcx> {
        let data = &self.body.basic_blocks[bb];

        let mut after_terminator = HashMap::new();
        let mut after_statements = Vec::new();
        after_statements.resize_with(data.statements.len() + 1, Vec::new);

        results.seek_to_block_end(bb);
        let live_locals_after_terminator = results.get().clone();

        use rustc_data_structures::graph::Successors as _;
        let mut ins = DenseBitSet::new_empty(self.body.local_decls.len());
        for succ_bb in self.body.basic_blocks.successors(bb) {
            self.bb_ins_cache.entry(succ_bb).or_insert_with(|| {
                results.seek_to_block_start(succ_bb);
                results.get().clone()
            });
            let edge_drops = {
                let mut t = live_locals_after_terminator.clone();
                t.subtract(&self.bb_ins_cache[&succ_bb]);
                t
            };
            after_terminator.insert(succ_bb, edge_drops.iter().map(Into::into).collect());
            ins.union(&self.bb_ins_cache[&succ_bb]);
        }

        tracing::debug!(?live_locals_after_terminator, ?ins);
        // FIXME: isn't it appropriate to use live_locals_after_terminator here? but it lacks
        //        some locals from successor ins...
        let mut last_live_locals = ins;
        // TODO: we may use seek_before_primary_effect here
        for statement_index in (0..=data.statements.len()).rev() {
            let loc = mir::Location {
                statement_index,
                block: bb,
            };
            results.seek_after_primary_effect(loc);
            let live_locals = results.get().clone();
            tracing::debug!(?live_locals, ?loc);
            after_statements[statement_index] = {
                let mut t = live_locals.clone();
                if let Some(def) = def_local(data, statement_index) {
                    t.insert(def);
                }
                t.subtract(&last_live_locals);
                t.subtract(&moved_locals(self.body, bb, statement_index));
                t.iter().map(Into::into).collect()
            };
            last_live_locals = live_locals;
        }

        self.bb_ins_cache.insert(bb, last_live_locals.clone());

        tracing::info!(
            ?bb,
            ?after_statements,
            ?after_terminator,
            "analyzed implicit drop points"
        );
        DropPoints {
            before_statements: Default::default(),
            after_statements,
            after_terminator,
            after_terminator_extra: Default::default(),
        }
    }
}
