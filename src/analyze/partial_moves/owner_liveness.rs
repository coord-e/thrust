use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{
    BasicBlock, Body, CallReturnPlaces, Local, Location, Statement, StatementKind, Terminator,
    TerminatorEdges, TerminatorKind,
};
use rustc_mir_dataflow::{impls::MaybeLiveLocals, Analysis, Backward};

/// A projected assignment still needs the ownership state of untouched fields.
pub struct OwnerLiveness;

impl<'tcx> Analysis<'tcx> for OwnerLiveness {
    type Domain = DenseBitSet<Local>;
    type Direction = Backward;

    const NAME: &'static str = "partial_move_owners";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        MaybeLiveLocals.bottom_value(body)
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {}

    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        MaybeLiveLocals.apply_primary_statement_effect(state, statement, location);
        if let StatementKind::Assign(assignment) = &statement.kind {
            let (place, _) = &**assignment;
            if !place.projection.is_empty() {
                state.insert(place.local);
            }
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let edges = MaybeLiveLocals.apply_primary_terminator_effect(state, terminator, location);
        if let TerminatorKind::Call { destination, .. } = &terminator.kind {
            if !destination.projection.is_empty() {
                state.insert(destination.local);
            }
        }
        edges
    }

    fn apply_call_return_effect(
        &mut self,
        state: &mut Self::Domain,
        block: BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        MaybeLiveLocals.apply_call_return_effect(state, block, return_places);
    }
}
