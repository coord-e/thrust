use rustc_middle::mir::{self, Local, Place};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

struct ReplaceLocalVisitor<'tcx> {
    from: Local,
    to: Place<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for ReplaceLocalVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(
        &mut self,
        place: &mut Place<'tcx>,
        _: mir::visit::PlaceContext,
        _: mir::Location,
    ) {
        if place.local == self.from {
            place.local = self.to.local;
            place.projection = self
                .tcx
                .mk_place_elems_from_iter(self.to.projection.iter().chain(place.projection));
        }
    }
}

pub struct ReborrowVisitor<'a, 'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    analyzer: &'a mut super::Analyzer<'tcx, 'ctx>,
}

impl<'tcx> ReborrowVisitor<'_, 'tcx, '_> {
    fn insert_borrow(&mut self, local: Local, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl =
            mir::LocalDecl::new(ty, self.analyzer.local_decls[local].source_info.span).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.borrow_place_(local.into(), inner_ty);
        self.analyzer
            .bind_local(new_local, new_local_ty, mir::Mutability::Not);
        tracing::info!(old_local = ?local, ?new_local, "implicitly borrowed");
        new_local
    }

    fn insert_reborrow(&mut self, local: Local, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl =
            mir::LocalDecl::new(ty, self.analyzer.local_decls[local].source_info.span).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let place = if self.analyzer.is_mut_local(local) {
            mir::Place::from(local).project_deeper(&[mir::PlaceElem::Deref], self.tcx)
        } else {
            local.into()
        };
        let new_local_ty = self.analyzer.borrow_place_(place, inner_ty);
        self.analyzer
            .bind_local(new_local, new_local_ty, mir::Mutability::Not);
        tracing::info!(old_local = ?local, ?new_local, "implicitly reborrowed");
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
        if place.projection.is_empty()
            && self.analyzer.is_defined(place.local)
            && self.analyzer.is_mut_local(place.local)
        {
            let ty = self.analyzer.local_decls[place.local].ty;
            let new_local = self.insert_borrow(place.local, ty);
            let new_place = self.tcx.mk_place_deref(new_local.into());
            ReplaceLocalVisitor {
                from: place.local,
                to: new_place.clone(),
                tcx: self.tcx,
            }
            .visit_rvalue(rvalue, location);
            *place = new_place;
            self.super_assign(place, rvalue, location);
            return;
        }

        if place.projection.as_slice() != &[mir::PlaceElem::Deref] {
            self.super_assign(place, rvalue, location);
            return;
        }

        let mir_ty::TyKind::Ref(_, inner_ty, m) = self.analyzer.local_decls[place.local].ty.kind()
        else {
            self.super_assign(place, rvalue, location);
            return;
        };

        let new_local = self.insert_reborrow(place.local, *inner_ty);
        ReplaceLocalVisitor {
            from: place.local,
            to: new_local.into(),
            tcx: self.tcx,
        }
        .visit_rvalue(rvalue, location);
        place.local = new_local;
        self.super_assign(place, rvalue, location);
    }

    // TODO: is it always true that the operand is not referred again in rvalue
    fn visit_operand(&mut self, operand: &mut mir::Operand<'tcx>, location: mir::Location) {
        let Some(p) = operand.place() else {
            self.super_operand(operand, location);
            return;
        };

        if p.projection.as_slice() == &[mir::PlaceElem::Deref] {
            self.super_operand(operand, location);
            return;
        }
        if !p.projection.is_empty() {
            unimplemented!();
        }

        let mir_ty::TyKind::Ref(_, inner_ty, m) = self.analyzer.local_decls[p.local].ty.kind()
        else {
            self.super_operand(operand, location);
            return;
        };
        if !operand.is_move() && m.is_mut() {
            let new_local = self.insert_reborrow(p.local, *inner_ty);
            *operand = mir::Operand::Move(new_local.into());
        }

        self.super_operand(operand, location);
    }
}

impl<'a, 'tcx, 'ctx> ReborrowVisitor<'a, 'tcx, 'ctx> {
    pub fn new(analyzer: &'a mut super::Analyzer<'tcx, 'ctx>) -> Self {
        let tcx = analyzer.tcx;
        Self { analyzer, tcx }
    }

    pub fn visit_statement(&mut self, stmt: &mut mir::Statement<'tcx>) {
        mir::visit::MutVisitor::visit_statement(self, stmt, mir::Location::START);
        // dummy location
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
        // dummy location
    }
}

