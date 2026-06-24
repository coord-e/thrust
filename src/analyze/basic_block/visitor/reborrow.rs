use rustc_middle::mir::{self, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

use crate::analyze::ReplacePlacesVisitor;

pub struct ReborrowVisitor<'a, 'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    analyzer: &'a mut crate::analyze::basic_block::Analyzer<'tcx, 'ctx>,
}

impl<'tcx> ReborrowVisitor<'_, 'tcx, '_> {
    fn insert_borrow(&mut self, place: mir::Place<'tcx>, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, Default::default()).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.borrow_place_(place, inner_ty);
        self.analyzer.bind_local(new_local, new_local_ty);
        tracing::info!(old_place = ?place, ?new_local, "implicitly borrowed");
        new_local
    }

    fn insert_reborrow(&mut self, place: mir::Place<'tcx>, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, Default::default()).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.borrow_place_(place, inner_ty);
        self.analyzer.bind_local(new_local, new_local_ty);
        tracing::info!(old_place = ?place, ?new_local, "implicitly reborrowed");
        new_local
    }
}

impl<'a, 'tcx, 'ctx> mir::visit::MutVisitor<'tcx> for ReborrowVisitor<'a, 'tcx, 'ctx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_assign(
        &mut self,
        place: &mut mir::Place<'tcx>,
        rvalue: &mut mir::Rvalue<'tcx>,
        location: mir::Location,
    ) {
        if !self.analyzer.is_defined(place.local) {
            self.super_assign(place, rvalue, location);
            return;
        }

        // (*s)[idx] = val: rewrite as *ptr = val, where ptr comes from
        // <[T] as IndexMut<usize>>::index_mut(s, idx) via the existing extern spec.
        // The existing reborrow + call pipeline then handles *ptr = val normally.
        if let [mir::PlaceElem::Deref, mir::PlaceElem::Index(idx_local)] =
            place.projection.as_slice()
        {
            let slice_local = place.local;
            let idx_local = *idx_local;
            let slice_mir_ty = self.analyzer.local_decls[slice_local].ty;
            let (inner_slice_ty, elem_ty) = match slice_mir_ty.kind() {
                mir_ty::TyKind::Ref(_, inner, _) => match inner.kind() {
                    mir_ty::TyKind::Slice(elem_ty) => (*inner, *elem_ty),
                    _ => unimplemented!("Index projection on non-slice ref"),
                },
                _ => unimplemented!("Index projection on non-ref"),
            };

            // Reborrow *s → s1: &mut [T], updating s's current to a fresh prophecy.
            let s1 = self.insert_reborrow(
                mir::Place {
                    local: slice_local,
                    projection: self.tcx.mk_place_elems(&[mir::PlaceElem::Deref]),
                },
                inner_slice_ty,
            );

            // Build fresh return type for ptr: &mut T (existential vars for current/final).
            let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
            let ptr_mir_ty = mir_ty::Ty::new_mut_ref(self.tcx, r, elem_ty);
            let ptr_rty = {
                let a = &mut *self.analyzer;
                a.type_builder
                    .for_template(&mut a.ctx)
                    .with_scope(&a.env)
                    .build_refined(ptr_mir_ty)
            };

            // Construct the func operand for <[T] as IndexMut<usize>>::index_mut.
            // type_call resolves the abstract DefId to the concrete impl internally.
            let index_mut_trait = self.tcx.lang_items().index_mut_trait().unwrap();
            let index_mut_def_id = self
                .tcx
                .associated_items(index_mut_trait)
                .filter_by_name_unhygienic(rustc_span::Symbol::intern("index_mut"))
                .next()
                .expect("IndexMut::index_mut not found")
                .def_id;
            let abstract_args = self.tcx.mk_args(&[
                mir_ty::GenericArg::from(inner_slice_ty),
                mir_ty::GenericArg::from(self.tcx.types.usize),
            ]);
            let fn_def_ty = mir_ty::Ty::new_fn_def(self.tcx, index_mut_def_id, abstract_args);
            let func_op = mir::Operand::Constant(Box::new(mir::ConstOperand {
                span: rustc_span::DUMMY_SP,
                user_ty: None,
                const_: mir::Const::zero_sized(fn_def_ty),
            }));

            // Apply the extern spec via the existing type_call.
            self.analyzer.type_call(
                func_op,
                [
                    mir::Operand::Move(s1.into()),
                    mir::Operand::Copy(idx_local.into()),
                ],
                &ptr_rty,
            );

            // Bind ptr and rewrite the place; super_assign then handles *ptr = val.
            let ptr_decl = mir::LocalDecl::new(ptr_mir_ty, rustc_span::DUMMY_SP).immutable();
            let ptr_local = self.analyzer.local_decls.push(ptr_decl);
            self.analyzer.bind_local(ptr_local, ptr_rty);
            *place = self.tcx.mk_place_deref(ptr_local.into());
            self.super_assign(place, rvalue, location);
            return;
        }

        if place.projection.is_empty() && self.analyzer.is_mut_local(place.local) {
            let ty = self.analyzer.local_decls[place.local].ty;
            let new_local = self.insert_borrow(place.local.into(), ty);
            let new_place = self.tcx.mk_place_deref(new_local.into());
            ReplacePlacesVisitor::with_replacement(self.tcx, place.local.into(), new_place)
                .visit_rvalue(rvalue, location);
            *place = new_place;
            self.super_assign(place, rvalue, location);
            return;
        }

        let inner_place = if place.projection.last() == Some(&mir::PlaceElem::Deref) {
            // *m = *m + 1 => m1 = &mut m; *m1 = *m + 1
            let mut projection = place.projection.as_ref().to_vec();
            projection.pop();
            mir::Place {
                local: place.local,
                projection: self.tcx.mk_place_elems(&projection),
            }
        } else {
            // s.0 = s.0 + 1 => m1 = &mut s.0; *m1 = *m1 + 1
            *place
        };

        let ty = inner_place.ty(&self.analyzer.local_decls, self.tcx).ty;
        let (new_local, new_place) = match ty.kind() {
            mir_ty::TyKind::Ref(_, inner_ty, m) if m.is_mut() => {
                let new_local = self.insert_reborrow(*place, *inner_ty);
                (new_local, new_local.into())
            }
            mir_ty::TyKind::Adt(adt, args) if adt.is_box() => {
                let inner_ty = args.type_at(0);
                let new_local = self.insert_borrow(*place, inner_ty);
                (new_local, new_local.into())
            }
            _ => {
                let new_local = self.insert_borrow(*place, ty);
                (new_local, self.tcx.mk_place_deref(new_local.into()))
            }
        };

        ReplacePlacesVisitor::with_replacement(self.tcx, inner_place, new_place)
            .visit_rvalue(rvalue, location);
        *place = self.tcx.mk_place_deref(new_local.into());
        self.super_assign(place, rvalue, location);
    }

    // TODO: is it always true that the operand is not referred again in rvalue
    fn visit_operand(&mut self, operand: &mut mir::Operand<'tcx>, location: mir::Location) {
        let Some(p) = operand.place() else {
            self.super_operand(operand, location);
            return;
        };

        let mir_ty::TyKind::Ref(_, inner_ty, m) =
            p.ty(&self.analyzer.local_decls, self.tcx).ty.kind()
        else {
            self.super_operand(operand, location);
            return;
        };

        if m.is_mut() {
            let new_local = self.insert_reborrow(self.tcx.mk_place_deref(p), *inner_ty);
            *operand = mir::Operand::Move(new_local.into());
        }

        self.super_operand(operand, location);
    }
}

impl<'a, 'tcx, 'ctx> ReborrowVisitor<'a, 'tcx, 'ctx> {
    pub fn new(analyzer: &'a mut crate::analyze::basic_block::Analyzer<'tcx, 'ctx>) -> Self {
        let tcx = analyzer.tcx;
        Self { analyzer, tcx }
    }

    pub fn visit_statement(&mut self, stmt: &mut mir::Statement<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_statement(self, stmt, mir::Location::START);
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
    }
}
