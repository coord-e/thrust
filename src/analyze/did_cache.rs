//! Retrieves and caches well-known [`DefId`]s.

use std::cell::OnceCell;
use std::rc::Rc;

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;
use rustc_target::abi::FieldIdx;

#[derive(Debug, Clone, Default)]
struct DefIds {
    unique: OnceCell<Option<DefId>>,
    nonnull: OnceCell<Option<DefId>>,

    model_ty: OnceCell<Option<DefId>>,
    int_model: OnceCell<Option<DefId>>,
    mut_model: OnceCell<Option<DefId>>,
    box_model: OnceCell<Option<DefId>>,
    array_model: OnceCell<Option<DefId>>,
    closure_model: OnceCell<Option<DefId>>,

    mut_model_new: OnceCell<Option<DefId>>,
    box_model_new: OnceCell<Option<DefId>>,
}

/// Retrieves and caches well-known [`DefId`]s.
///
/// [`DefId`]s of some well-known types can be retrieved as lang items or via the definition of
/// lang items. This struct implements that logic and caches the results.
#[derive(Clone)]
pub struct DefIdCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_ids: Rc<DefIds>,
}

impl<'tcx> DefIdCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            def_ids: Rc::new(DefIds::default()),
        }
    }

    pub fn box_(&self) -> Option<DefId> {
        self.tcx.lang_items().owned_box()
    }

    pub fn unique(&self) -> Option<DefId> {
        *self.def_ids.unique.get_or_init(|| {
            let box_did = self.box_()?;
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
            let unique_did = self.unique()?;
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

    fn annotated_def(&self, path: &[Symbol]) -> Option<DefId> {
        let map = self.tcx.hir();
        for item_id in map.items() {
            let def_id = item_id.owner_id.to_def_id();
            if self.tcx.get_attrs_by_path(def_id, path).next().is_some() {
                return Some(def_id);
            }

            let item = map.item(item_id);
            if let rustc_hir::ItemKind::Trait(_, _, _, _, trait_item_refs) = item.kind {
                for trait_item_ref in trait_item_refs {
                    let def_id = trait_item_ref.id.owner_id.to_def_id();
                    if self.tcx.get_attrs_by_path(def_id, path).next().is_some() {
                        return Some(def_id);
                    }
                }
            }
            if let rustc_hir::ItemKind::Impl(impl_) = item.kind {
                for impl_item_ref in impl_.items {
                    let def_id = impl_item_ref.id.owner_id.to_def_id();
                    if self.tcx.get_attrs_by_path(def_id, path).next().is_some() {
                        return Some(def_id);
                    }
                }
            }
        }
        None
    }

    pub fn model_ty(&self) -> Option<DefId> {
        *self
            .def_ids
            .model_ty
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::model_ty_path()))
    }

    pub fn int_model(&self) -> Option<DefId> {
        *self
            .def_ids
            .int_model
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::int_model_path()))
    }

    pub fn mut_model(&self) -> Option<DefId> {
        *self
            .def_ids
            .mut_model
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::mut_model_path()))
    }

    pub fn box_model(&self) -> Option<DefId> {
        *self
            .def_ids
            .box_model
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::box_model_path()))
    }

    pub fn array_model(&self) -> Option<DefId> {
        *self
            .def_ids
            .array_model
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::array_model_path()))
    }

    pub fn closure_model(&self) -> Option<DefId> {
        *self
            .def_ids
            .closure_model
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::closure_model_path()))
    }

    pub fn mut_model_new(&self) -> Option<DefId> {
        *self
            .def_ids
            .mut_model_new
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::mut_model_new_path()))
    }

    pub fn box_model_new(&self) -> Option<DefId> {
        *self
            .def_ids
            .box_model_new
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::box_model_new_path()))
    }
}
