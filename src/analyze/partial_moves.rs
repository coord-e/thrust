use std::collections::{HashMap, HashSet};

use rustc_index::IndexVec;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{self, BasicBlock, Body, Location, Place};
use rustc_middle::ty::TyCtxt;
use rustc_mir_dataflow::Analysis;

mod owner_liveness;

#[derive(Default)]
pub struct PartialMoves<'tcx> {
    pub block_origins: IndexVec<BasicBlock, BasicBlock>,
    pub after: HashMap<Location, HashSet<Place<'tcx>>>,
    pub edges: HashMap<(BasicBlock, BasicBlock), HashSet<Place<'tcx>>>,
}

struct Ownership<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    places: &'a [Place<'tcx>],
    moved: Vec<bool>,
}

fn contains<'tcx>(parent: Place<'tcx>, child: Place<'tcx>) -> bool {
    parent.local == child.local && child.projection.starts_with(parent.projection)
}

impl<'tcx> Ownership<'_, 'tcx> {
    fn initialize(&mut self, place: Place<'tcx>) {
        for (tracked, moved) in self.places.iter().zip(&mut self.moved) {
            if contains(place, *tracked) {
                *moved = false;
            }
        }
    }

    fn exclusions(&self) -> HashSet<Place<'tcx>> {
        self.places
            .iter()
            .zip(&self.moved)
            .filter_map(|(place, moved)| moved.then_some(*place))
            .collect()
    }
}

impl<'tcx> Visitor<'tcx> for Ownership<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, _location: Location) {
        if let mir::Operand::Move(place) = operand {
            if place.ty(&self.body.local_decls, self.tcx).ty.is_ref() {
                return;
            }
            for (tracked, moved) in self.places.iter().zip(&mut self.moved) {
                if contains(*place, *tracked) {
                    *moved = true;
                }
            }
        }
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, value: &mir::Rvalue<'tcx>, location: Location) {
        self.visit_rvalue(value, location);
        self.initialize(*place);
    }
}

struct PartialMovePlaces<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    places: Vec<Place<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for PartialMovePlaces<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, _location: Location) {
        if let mir::Operand::Move(place) = operand {
            if !place.projection.is_empty()
                && !place.ty(&self.body.local_decls, self.tcx).ty.is_ref()
                && !self.places.contains(place)
            {
                self.places.push(*place);
            }
        }
    }
}

impl<'tcx> PartialMoves<'tcx> {
    /// Separate control-flow joins with different ownership states so each drop
    /// has an unconditional, path-specific set of exclusions. A loop reuses the
    /// block for an already-seen state instead of unrolling the execution.
    pub fn analyze(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) -> Self {
        let mut collector = PartialMovePlaces {
            tcx,
            body,
            places: Vec::new(),
        };
        collector.visit_body(body);
        let places = collector.places;
        if places.is_empty() {
            return Self {
                block_origins: body.basic_blocks.indices().collect(),
                ..Self::default()
            };
        }

        let mut result = Self::default();
        let mut liveness = owner_liveness::OwnerLiveness
            .iterate_to_fixpoint(tcx, body, None)
            .into_results_cursor(body);
        let mut blocks = IndexVec::new();
        let initial = vec![false; places.len()];
        let mut pending = vec![(mir::START_BLOCK, initial.clone())];
        let mut versions = HashMap::from([((mir::START_BLOCK, initial), mir::START_BLOCK)]);
        let mut index = 0;
        while index < pending.len() {
            let (original, state) = &pending[index];
            result.block_origins.push(*original);
            let block = BasicBlock::from_usize(index);
            let mut data = body.basic_blocks[*original].clone();
            let mut ownership = Ownership {
                tcx,
                body,
                places: &places,
                moved: state.clone(),
            };
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                ownership.visit_statement(statement, location);
                result.after.insert(location, ownership.exclusions());
            }
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            let terminator = data.terminator_mut();
            ownership.visit_terminator(terminator, location);
            let call_destination = match terminator.kind {
                mir::TerminatorKind::Call {
                    destination,
                    target: Some(target),
                    ..
                } => Some((destination, target)),
                _ => None,
            };
            result.after.insert(location, ownership.exclusions());
            terminator.successors_mut(|target| {
                let mut edge = Ownership {
                    tcx,
                    body,
                    places: &places,
                    moved: ownership.moved.clone(),
                };
                if let Some((destination, return_target)) = call_destination {
                    if *target == return_target {
                        edge.initialize(destination);
                    }
                }
                let exclusions = edge.exclusions();
                liveness.seek_to_block_start(*target);
                for (place, moved) in places.iter().zip(&mut edge.moved) {
                    if !liveness.get().contains(place.local) {
                        *moved = false;
                    }
                }
                let key = (*target, edge.moved.clone());
                *target = *versions.entry(key.clone()).or_insert_with(|| {
                    let version = BasicBlock::from_usize(pending.len());
                    pending.push(key);
                    version
                });
                result.edges.insert((block, *target), exclusions);
            });
            blocks.push(data);
            index += 1;
        }
        body.basic_blocks = mir::BasicBlocks::new(blocks);
        result
    }
}
