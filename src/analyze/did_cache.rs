//! Retrieves and caches well-known [`DefId`]s.

use std::cell::OnceCell;
use std::rc::Rc;

use rustc_abi::FieldIdx;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;

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
    array_model_store: OnceCell<Option<DefId>>,

    seq_model: OnceCell<Option<DefId>>,
    seq_empty: OnceCell<Option<DefId>>,
    seq_singleton: OnceCell<Option<DefId>>,
    seq_len: OnceCell<Option<DefId>>,
    seq_push: OnceCell<Option<DefId>>,

    exists: OnceCell<Option<DefId>>,
    forall: OnceCell<Option<DefId>>,
    implies: OnceCell<Option<DefId>>,
    invariant_marker: OnceCell<Option<DefId>>,

    fn_param_wrapper: OnceCell<Option<DefId>>,
    fn_param_at_entry: OnceCell<Option<DefId>>,

    closure_precondition: OnceCell<Option<DefId>>,
    closure_postcondition: OnceCell<Option<DefId>>,
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
        for item_id in self.tcx.hir_free_items() {
            let def_id = item_id.owner_id.to_def_id();
            if self.tcx.get_attrs_by_path(def_id, path).next().is_some() {
                return Some(def_id);
            }

            let item = self.tcx.hir_item(item_id);
            if let rustc_hir::ItemKind::Trait(_, _, _, _, _, _, trait_item_refs) = item.kind {
                for trait_item_ref in trait_item_refs {
                    let def_id = trait_item_ref.owner_id.to_def_id();
                    if self.tcx.get_attrs_by_path(def_id, path).next().is_some() {
                        return Some(def_id);
                    }
                }
            }
            if let rustc_hir::ItemKind::Impl(impl_) = item.kind {
                for impl_item_ref in impl_.items {
                    let def_id = impl_item_ref.owner_id.to_def_id();
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

    pub fn array_model_store(&self) -> Option<DefId> {
        *self
            .def_ids
            .array_model_store
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::array_model_store_path()))
    }

    pub fn seq_model(&self) -> Option<DefId> {
        *self
            .def_ids
            .seq_model
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::seq_model_path()))
    }

    pub fn seq_empty(&self) -> Option<DefId> {
        *self
            .def_ids
            .seq_empty
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::seq_empty_path()))
    }

    pub fn seq_singleton(&self) -> Option<DefId> {
        *self
            .def_ids
            .seq_singleton
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::seq_singleton_path()))
    }

    pub fn seq_len(&self) -> Option<DefId> {
        *self
            .def_ids
            .seq_len
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::seq_len_path()))
    }

    pub fn seq_push(&self) -> Option<DefId> {
        *self
            .def_ids
            .seq_push
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::seq_push_path()))
    }

    pub fn exists(&self) -> Option<DefId> {
        *self
            .def_ids
            .exists
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::exists_path()))
    }

    pub fn forall(&self) -> Option<DefId> {
        *self
            .def_ids
            .forall
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::forall_path()))
    }

    pub fn implies(&self) -> Option<DefId> {
        *self
            .def_ids
            .implies
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::implies_path()))
    }

    pub fn invariant_marker(&self) -> Option<DefId> {
        *self
            .def_ids
            .invariant_marker
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::invariant_marker_path()))
    }

    pub fn fn_param_wrapper(&self) -> Option<DefId> {
        *self
            .def_ids
            .fn_param_wrapper
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::fn_param_wrapper_path()))
    }

    pub fn fn_param_at_entry(&self) -> Option<DefId> {
        *self
            .def_ids
            .fn_param_at_entry
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::fn_param_at_entry_path()))
    }

    pub fn closure_precondition(&self) -> Option<DefId> {
        *self
            .def_ids
            .closure_precondition
            .get_or_init(|| self.annotated_def(&crate::analyze::annot::closure_precondition_path()))
    }

    pub fn closure_postcondition(&self) -> Option<DefId> {
        *self.def_ids.closure_postcondition.get_or_init(|| {
            self.annotated_def(&crate::analyze::annot::closure_postcondition_path())
        })
    }
}
