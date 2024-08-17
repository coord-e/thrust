use std::collections::HashMap;

use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};

#[derive(Debug, Clone, Default)]
pub struct DropPoints {
    // TODO: ad-hoc
    pub before_statements: Vec<Local>,
    after_statements: Vec<BitSet<Local>>,
    after_terminator: HashMap<BasicBlock, BitSet<Local>>,
}

impl DropPoints {
    pub fn builder<'mir, 'tcx>(body: &'mir Body<'tcx>) -> DropPointsBuilder<'mir, 'tcx> {
        DropPointsBuilder {
            body,
            bb_ins_cache: HashMap::new(),
        }
    }

    pub fn position(&self, local: Local) -> Option<usize> {
        self.after_statements
            .iter()
            .position(|s| s.contains(local))
            .or_else(|| {
                self.after_terminator
                    .values()
                    .any(|s| s.contains(local))
                    .then_some(self.after_statements.len())
            })
    }

    pub fn remove_after_statement(&mut self, statement_index: usize, local: Local) -> bool {
        self.after_statements[statement_index].remove(local)
    }

    pub fn insert_after_statement(&mut self, statement_index: usize, local: Local) -> bool {
        self.after_statements[statement_index].insert(local)
    }

    pub fn after_statement(&self, statement_index: usize) -> BitSet<Local> {
        self.after_statements[statement_index].clone()
    }

    pub fn after_terminator(&self, target: &BasicBlock) -> BitSet<Local> {
        let mut t = self.after_terminator[target].clone();
        t.union(self.after_statements.last().unwrap());
        t
    }
}

#[derive(Debug, Clone)]
pub struct DropPointsBuilder<'mir, 'tcx> {
    body: &'mir Body<'tcx>,
    bb_ins_cache: HashMap<BasicBlock, BitSet<Local>>,
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

impl<'mir, 'tcx> DropPointsBuilder<'mir, 'tcx> {
    pub fn build(
        &mut self,
        results: &mut ResultsCursor<'mir, 'tcx, MaybeLiveLocals>,
        bb: BasicBlock,
    ) -> DropPoints {
        let data = &self.body.basic_blocks[bb];

        let mut after_terminator = HashMap::new();
        let mut after_statements = Vec::new();
        after_statements.resize_with(data.statements.len() + 1, || BitSet::new_empty(0));

        results.seek_to_block_end(bb);
        let live_locals_after_terminator = results.get().clone();

        use rustc_data_structures::graph::WithSuccessors as _;
        let mut ins = BitSet::new_empty(self.body.local_decls.len());
        for succ_bb in self.body.basic_blocks.successors(bb) {
            if !self.bb_ins_cache.contains_key(&succ_bb) {
                results.seek_to_block_start(succ_bb);
                self.bb_ins_cache.insert(succ_bb, results.get().clone());
            }
            let edge_drops = {
                let mut t = live_locals_after_terminator.clone();
                t.subtract(&self.bb_ins_cache[&succ_bb]);
                t
            };
            after_terminator.insert(succ_bb, edge_drops);
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
                if let Some(def) = def_local(data.visitable(statement_index)) {
                    t.insert(def);
                }
                t.subtract(&last_live_locals);
                t
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
        }
    }
}
