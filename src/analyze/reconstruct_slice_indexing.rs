//! Reconstructs slice indexing calls erased by MIR lowering.

use rustc_hir::def::Namespace;
use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::{
    self, BasicBlock, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self as mir_ty, Ty, TyCtxt};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::{sym, Symbol};

use crate::analyze;

/// The bounds-check block emitted for an indexing expression.
struct BoundsCheck<'tcx> {
    block: BasicBlock,
    condition_local: Option<Local>,
    len: Operand<'tcx>,
    index: Operand<'tcx>,
    index_local: Local,
    target: BasicBlock,
    unwind: mir::UnwindAction,
    source_info: mir::SourceInfo,
}

/// The slice access in the target of a [`BoundsCheck`].
struct SliceAccess<'tcx> {
    indexed_place: mir::Place<'tcx>,
    receiver: mir::Place<'tcx>,
    receiver_mutability: mir_ty::Mutability,
    slice_ty: Ty<'tcx>,
    elem_ty: Ty<'tcx>,
    mutable: bool,
}

struct IndexedPlaceFinder<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    index: Local,
    found: Option<(mir::Place<'tcx>, bool)>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for IndexedPlaceFinder<'_, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        if self.found.is_some() {
            return;
        }
        let Some(index_pos) = place
            .projection
            .iter()
            .position(|elem| elem == mir::PlaceElem::Index(self.index))
        else {
            return;
        };
        let indexed = mir::Place {
            local: place.local,
            projection: self
                .tcx
                .mk_place_elems(&place.projection.as_slice()[..=index_pos]),
        };
        let base = mir::Place {
            local: place.local,
            projection: self
                .tcx
                .mk_place_elems(&place.projection.as_slice()[..index_pos]),
        };
        if matches!(
            base.ty(&self.body.local_decls, self.tcx).ty.kind(),
            mir_ty::TyKind::Slice(_)
        ) {
            self.found = Some((indexed, context.is_mutating_use()));
        }
    }
}

/// Reconstructs the trait call erased by MIR's first-class slice indexing operation.
///
/// For example, optimized MIR for `slice[index]` contains:
///
/// ```text
/// fn shared_slice_index(_1: &[i32], _2: usize) -> i32 {
///     let mut _0: i32;
///     let mut _3: usize;
///     let mut _4: bool;
///
///     bb0: {
///         _3 = PtrMetadata(copy _1);
///         _4 = Lt(copy _2, copy _3);
///         assert(move _4, "index out of bounds: the length is {} but the index is {}", move _3, copy _2) -> [success: bb1, unwind continue];
///     }
///
///     bb1: {
///         _0 = copy (*_1)[_2];
///         return;
///     }
/// }
/// ```
///
/// This reconstruction replaces that sequence with an `Index::index` or `IndexMut::index_mut`
/// call terminator and rewrites the indexed place to dereference its result:
///
/// ```text
/// fn shared_slice_index(_1: &[i32], _2: usize) -> i32 {
///     let mut _0: i32;
///     let _5: &i32;
///
///     bb0: {
///         _5 = <[i32] as Index<usize>>::index(copy _1, copy _2)
///             -> [return: bb1, unwind continue];
///     }
///
///     bb1: {
///         _0 = copy (*_5);
///         return;
///     }
/// }
/// ```
///
/// The analyzer therefore applies the registered trait-method type and remains independent of
/// the model selected for slices.
pub fn reconstruct<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    for block in body.basic_blocks.indices().collect::<Vec<_>>() {
        let Some(bounds_check) = find_bounds_check(body, block) else {
            continue;
        };
        let Some(access) = find_slice_access(tcx, body, &bounds_check) else {
            tracing::trace!(?block, "bounds check is not followed by slice indexing");
            continue;
        };
        // The rewritten target uses a result local defined by this block's new call. Entering it
        // from another predecessor would leave that local undefined.
        assert_eq!(
            body.basic_blocks.predecessors()[bounds_check.target].as_slice(),
            [block],
            "slice indexing target must have exactly one predecessor",
        );

        tracing::debug!(
            assert_block = ?block,
            target = ?bounds_check.target,
            indexed_place = ?access.indexed_place,
            receiver = ?access.receiver,
            mutable = access.mutable,
            "reconstructing a trait method call from slice indexing"
        );
        reconstruct_access(tcx, body, bounds_check, access);
    }
}

/// Recognizes the bounds-check terminator and records the simple local used as the index.
fn find_bounds_check<'tcx>(body: &Body<'tcx>, block: BasicBlock) -> Option<BoundsCheck<'tcx>> {
    let terminator = body.basic_blocks[block].terminator.as_ref()?;
    let TerminatorKind::Assert {
        cond,
        msg,
        target,
        unwind,
        ..
    } = &terminator.kind
    else {
        return None;
    };
    let mir::AssertMessage::BoundsCheck { len, index } = &**msg else {
        return None;
    };
    let index_place = index.place()?;
    if !index_place.projection.is_empty() {
        return None;
    }

    Some(BoundsCheck {
        block,
        condition_local: cond
            .place()
            .filter(|place| place.projection.is_empty())
            .map(|place| place.local),
        len: len.clone(),
        index: index.clone(),
        index_local: index_place.local,
        target: *target,
        unwind: *unwind,
        source_info: terminator.source_info,
    })
}

/// Finds the matching `(*slice)[index]` place in the bounds check's target block.
fn find_slice_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
) -> Option<SliceAccess<'tcx>> {
    use mir::visit::Visitor as _;

    let mut finder = IndexedPlaceFinder {
        body,
        tcx,
        index: bounds_check.index_local,
        found: None,
    };
    finder.visit_basic_block_data(bounds_check.target, &body.basic_blocks[bounds_check.target]);
    let (indexed_place, mutable) = finder.found?;

    // The indexed place has the shape `receiver.*[index]`; strip the dereference and index to
    // recover the reference passed to `Index::index` or `IndexMut::index_mut`.
    let mut receiver_projection = indexed_place.projection.as_slice().to_vec();
    if receiver_projection.pop() != Some(mir::PlaceElem::Index(bounds_check.index_local))
        || receiver_projection.pop() != Some(mir::PlaceElem::Deref)
    {
        return None;
    }
    let receiver = mir::Place {
        local: indexed_place.local,
        projection: tcx.mk_place_elems(&receiver_projection),
    };
    let mir_ty::TyKind::Ref(_, slice_ty, receiver_mutability) =
        receiver.ty(&body.local_decls, tcx).ty.kind()
    else {
        return None;
    };
    let mir_ty::TyKind::Slice(elem_ty) = slice_ty.kind() else {
        return None;
    };
    if mutable && !receiver_mutability.is_mut() {
        return None;
    }

    Some(SliceAccess {
        indexed_place,
        receiver,
        receiver_mutability: *receiver_mutability,
        slice_ty: *slice_ty,
        elem_ty: *elem_ty,
        mutable,
    })
}

fn reconstruct_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: BoundsCheck<'tcx>,
    access: SliceAccess<'tcx>,
) {
    let region = mir_ty::Region::new_from_kind(tcx, mir_ty::RegionKind::ReErased);
    let result_ty = mir_ty::Ty::new_ref(
        tcx,
        region,
        access.elem_ty,
        if access.mutable {
            mir_ty::Mutability::Mut
        } else {
            mir_ty::Mutability::Not
        },
    );
    let result_local = body
        .local_decls
        .push(mir::LocalDecl::new(result_ty, bounds_check.source_info.span).immutable());

    replace_indexed_place(
        body,
        tcx,
        bounds_check.target,
        access.indexed_place,
        result_local,
    );
    let receiver = receiver_operand(tcx, body, &bounds_check, &access, region);
    remove_bounds_check_setup(body, &bounds_check, access.receiver.local);

    let (lang_item, method_name) = if access.mutable {
        (LangItem::IndexMut, sym::index_mut)
    } else {
        (LangItem::Index, sym::index)
    };
    let method = lang_item_method(tcx, lang_item, method_name);
    let args = tcx.mk_args(&[access.slice_ty.into(), tcx.types.usize.into()]);
    let func = super::fn_operand(tcx, method, args, bounds_check.source_info.span);
    let call_args = [receiver, bounds_check.index]
        .into_iter()
        .map(|node| Spanned {
            node,
            span: bounds_check.source_info.span,
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();

    body.basic_blocks.as_mut()[bounds_check.block].terminator = Some(mir::Terminator {
        source_info: bounds_check.source_info,
        kind: TerminatorKind::Call {
            func,
            args: call_args,
            destination: result_local.into(),
            target: Some(bounds_check.target),
            unwind: bounds_check.unwind,
            call_source: mir::CallSource::Normal,
            fn_span: bounds_check.source_info.span,
        },
    });
    tracing::trace!(?result_local, ?method, "slice indexing call inserted");
}

/// Replaces every use of the indexed place in the target block with `*result_local`.
fn replace_indexed_place<'tcx>(
    body: &mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    target: BasicBlock,
    indexed_place: mir::Place<'tcx>,
    result_local: Local,
) {
    let replacement = tcx.mk_place_deref(result_local.into());
    let mut replacer =
        analyze::ReplacePlacesVisitor::with_replacement(tcx, indexed_place, replacement);
    let target_data = &mut body.basic_blocks.as_mut()[target];
    for statement in &mut target_data.statements {
        replacer.visit_statement(statement);
    }
    if let Some(terminator) = &mut target_data.terminator {
        replacer.visit_terminator(terminator);
    }
}

/// Builds the receiver operand, inserting a shared reborrow when indexing through `&mut [T]`.
fn receiver_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    access: &SliceAccess<'tcx>,
    region: mir_ty::Region<'tcx>,
) -> Operand<'tcx> {
    if !access.mutable && access.receiver_mutability.is_mut() {
        let ty = mir_ty::Ty::new_ref(tcx, region, access.slice_ty, mir_ty::Mutability::Not);
        let local = body
            .local_decls
            .push(mir::LocalDecl::new(ty, bounds_check.source_info.span).immutable());
        body.basic_blocks.as_mut()[bounds_check.block]
            .statements
            .push(mir::Statement::new(
                bounds_check.source_info,
                StatementKind::Assign(Box::new((
                    local.into(),
                    Rvalue::Ref(
                        region,
                        mir::BorrowKind::Shared,
                        tcx.mk_place_deref(access.receiver),
                    ),
                ))),
            ));
        Operand::Copy(local.into())
    } else if access.mutable {
        Operand::Move(access.receiver)
    } else {
        Operand::Copy(access.receiver)
    }
}

/// Removes the MIR temporaries that only supported the now-replaced bounds check.
fn remove_bounds_check_setup<'tcx>(
    body: &mut Body<'tcx>,
    bounds_check: &BoundsCheck<'tcx>,
    receiver_local: Local,
) {
    let mut lowered_locals: Vec<_> = bounds_check.condition_local.into_iter().collect();
    if let Some(len_place) = bounds_check
        .len
        .place()
        .filter(|place| place.projection.is_empty())
    {
        lowered_locals.push(len_place.local);
        for statement in &body.basic_blocks[bounds_check.block].statements {
            let Some((lhs, Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand))) =
                statement.kind.as_assign()
            else {
                continue;
            };
            if lhs.local == len_place.local {
                // Only include the PtrMetadata operand if it is a distinct temporary — i.e.
                // not the receiver that the reconstructed Index::index call will use.
                // When PtrMetadata is applied directly to the slice reference (the receiver),
                // that local must not be NOP'd: its assignment may be in this same block.
                if let Some(raw_place) = operand
                    .place()
                    .filter(|place| place.projection.is_empty() && place.local != receiver_local)
                {
                    lowered_locals.push(raw_place.local);
                }
            }
        }
    }

    tracing::trace!(
        ?lowered_locals,
        "removing replaced bounds-check temporaries"
    );
    for statement in &mut body.basic_blocks.as_mut()[bounds_check.block].statements {
        let Some((lhs, _)) = statement.kind.as_assign() else {
            continue;
        };
        if lowered_locals.contains(&lhs.local) {
            statement.kind = StatementKind::Nop;
        }
    }
}

fn lang_item_method(tcx: TyCtxt<'_>, item: LangItem, name: Symbol) -> DefId {
    let trait_id = tcx.lang_items().get(item).unwrap();
    tcx.associated_items(trait_id)
        .in_definition_order()
        .find(|item| item.name() == name && item.namespace() == Namespace::ValueNS)
        .unwrap()
        .def_id
}

#[cfg(test)]
mod tests;
