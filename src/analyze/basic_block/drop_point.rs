use std::collections::{HashMap, HashSet};

use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{self, BasicBlock, Body, Local, Location};
use rustc_middle::ty::TyCtxt;
use rustc_mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};

/// A set of implicit-drop targets: `drops` are the whole locals to drop;
/// `except` are moved-out sub-places to skip when a drop walks into them.
#[derive(Debug, Clone, Default)]
pub struct DropSet<'tcx> {
    pub drops: HashSet<Local>,
    pub except: HashSet<mir::Place<'tcx>>,
}

impl<'tcx> DropSet<'tcx> {
    /// Schedule `local` to be dropped whole.
    pub fn insert(&mut self, local: Local) {
        self.drops.insert(local);
    }

    fn extend(&mut self, other: &DropSet<'tcx>) {
        self.drops.extend(other.drops.iter().copied());
        self.except.extend(other.except.iter().copied());
    }
}

#[derive(Debug, Clone, Default)]
pub struct DropPoints<'tcx> {
    pub before_statements: DropSet<'tcx>,
    after_statements: Vec<DropSet<'tcx>>,
    after_terminator: HashMap<BasicBlock, DropSet<'tcx>>,
    after_terminator_extra: DropSet<'tcx>,
}

impl DropPoints<'_> {
    pub fn builder<'mir, 'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
    ) -> DropPointsBuilder<'mir, 'tcx> {
        DropPointsBuilder {
            body,
            bb_ins_cache: HashMap::new(),
            moves: Moves::collect(tcx, body),
        }
    }
}

impl<'tcx> DropPoints<'tcx> {
    pub fn after_statement(&self, statement_index: usize) -> DropSet<'tcx> {
        self.after_statements[statement_index].clone()
    }

    pub fn insert_after_terminator(&mut self, local: Local) {
        self.after_terminator_extra.insert(local);
    }

    pub fn after_terminator(&self, target: &BasicBlock) -> DropSet<'tcx> {
        let mut set = self.after_terminator[target].clone();
        set.extend(self.after_statements.last().unwrap());
        set.extend(&self.after_terminator_extra);
        set
    }
}

#[derive(Clone)]
pub struct DropPointsBuilder<'mir, 'tcx> {
    body: &'mir Body<'tcx>,
    bb_ins_cache: HashMap<BasicBlock, DenseBitSet<Local>>,
    moves: Moves<'tcx>,
}

/// The `move`d operands of a body, excluding reference-typed places.
///
/// `move`d references are turned into reborrows by
/// `ReborrowVisitor`/`RustCallVisitor`, so the source still owns its prophecy
/// and must be dropped normally; they are therefore not recorded here.
///
/// A whole-local move leaves the local uninitialized, transferring its entire
/// drop obligation (including resolving any mutable-borrow prophecies it owns)
/// to the destination, so it must not be dropped at the move site — where the
/// local also becomes dead, hence the per-location keying. A partial (projected)
/// field move transfers only a sub-place, but the parent stays live until its
/// remaining parts die later; dropping it wholesale at that point would walk
/// into the moved-out sub-place and resolve its `&mut` prophecy a second time,
/// so a partially-moved local is excluded from dropping entirely.
#[derive(Clone, Default)]
struct Moves<'tcx> {
    /// Whole-local moves, keyed by the location performing the move.
    whole: HashMap<Location, DenseBitSet<Local>>,
    /// Partial field moves, keyed by the parent local.
    partial: HashMap<Local, Vec<mir::Place<'tcx>>>,
}

impl<'tcx> Moves<'tcx> {
    fn collect(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Moves<'tcx> {
        struct Visitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            body: &'a Body<'tcx>,
            moves: Moves<'tcx>,
        }
        impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'_, 'tcx> {
            fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: Location) {
                let mir::Operand::Move(place) = operand else {
                    return;
                };
                if place.ty(&self.body.local_decls, self.tcx).ty.is_ref() {
                    return;
                }
                if place.projection.is_empty() {
                    self.moves
                        .whole
                        .entry(location)
                        .or_insert_with(|| DenseBitSet::new_empty(self.body.local_decls.len()))
                        .insert(place.local);
                } else {
                    let entry = self.moves.partial.entry(place.local).or_default();
                    if !entry.contains(place) {
                        entry.push(*place);
                    }
                }
            }
        }
        let mut visitor = Visitor {
            tcx,
            body,
            moves: Moves::default(),
        };
        use mir::visit::Visitor as _;
        visitor.visit_body(body);
        visitor.moves
    }
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
    /// Turn a set of locals that become dead into the drop targets. Each dying
    /// local is dropped whole; a local with partial field moves contributes
    /// those moved-out sub-places as exceptions, so the drop resolves its
    /// still-owned parts while skipping the moved-out ones.
    fn drop_set(&self, locals: DenseBitSet<Local>) -> DropSet<'tcx> {
        let mut set = DropSet::default();
        for local in locals.iter() {
            set.drops.insert(local);
            if let Some(moved) = self.moves.partial.get(&local) {
                set.except.extend(moved.iter().copied());
            }
        }
        set
    }

    pub fn build(
        &mut self,
        results: &mut ResultsCursor<'mir, 'tcx, MaybeLiveLocals>,
        bb: BasicBlock,
    ) -> DropPoints<'tcx> {
        let data = &self.body.basic_blocks[bb];

        let mut after_terminator = HashMap::new();
        let mut after_statements = Vec::new();
        after_statements.resize_with(data.statements.len() + 1, DropSet::default);

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
            after_terminator.insert(succ_bb, self.drop_set(edge_drops));
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
                if let Some(moved) = self.moves.whole.get(&loc) {
                    t.subtract(moved);
                }
                self.drop_set(t)
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
            before_statements: DropSet::default(),
            after_statements,
            after_terminator,
            after_terminator_extra: DropSet::default(),
        }
    }
}
