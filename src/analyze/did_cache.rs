use std::cell::OnceCell;

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_target::abi::FieldIdx;

#[derive(Debug, Clone, Default)]
struct DefIds {
    unique: OnceCell<Option<DefId>>,
    nonnull: OnceCell<Option<DefId>>,
}

#[derive(Clone)]
pub struct DefIdCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_ids: DefIds,
}

impl<'tcx> DefIdCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            def_ids: DefIds::default(),
        }
    }

    pub fn box_(&self) -> Option<DefId> {
        self.tcx.lang_items().owned_box()
    }

    pub fn unique(&self) -> Option<DefId> {
        *self.def_ids.unique.get_or_init(|| {
            let Some(box_did) = self.box_() else {
                return None;
            };
            let box_first_did =
                self.tcx.adt_def(box_did).non_enum_variant().fields[FieldIdx::from_u32(0)].did;
            let unique_def = self
                .tcx
                .type_of(box_first_did)
                .instantiate_identity()
                .ty_adt_def()
                .expect("expected Box to contain Unique");
            Some(unique_def.did())
        })
    }

    pub fn nonnull(&self) -> Option<DefId> {
        *self.def_ids.nonnull.get_or_init(|| {
            let Some(unique_did) = self.unique() else {
                return None;
            };
            let unique_first_did =
                self.tcx.adt_def(unique_did).non_enum_variant().fields[FieldIdx::from_u32(0)].did;
            let nonnull_def = self
                .tcx
                .type_of(unique_first_did)
                .instantiate_identity()
                .ty_adt_def()
                .expect("expected Unique to contain NonNull");
            Some(nonnull_def.did())
        })
    }
}
