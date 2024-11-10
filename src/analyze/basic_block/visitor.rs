use std::collections::HashMap;

use rustc_middle::mir::{self, Local, Place};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

pub struct ReplacePlacesVisitor<'tcx> {
    replacements: HashMap<(Local, &'tcx [mir::PlaceElem<'tcx>]), Place<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for ReplacePlacesVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(
        &mut self,
        place: &mut Place<'tcx>,
        _: mir::visit::PlaceContext,
        _: mir::Location,
    ) {
        let proj = place.projection.as_slice();
        for i in 0..=proj.len() {
            if let Some(to) = self.replacements.get(&(place.local, &proj[0..i])) {
                place.local = to.local;
                place.projection = self.tcx.mk_place_elems_from_iter(
                    to.projection.iter().chain(proj.iter().skip(i).cloned()),
                );
                return;
            }
        }
    }
}

impl<'tcx> ReplacePlacesVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            replacements: Default::default(),
        }
    }

    pub fn with_replacement(tcx: TyCtxt<'tcx>, from: Place<'tcx>, to: Place<'tcx>) -> Self {
        let mut visitor = Self::new(tcx);
        visitor.add_replacement(from, to);
        visitor
    }

    pub fn add_replacement(&mut self, from: Place<'tcx>, to: Place<'tcx>) {
        self.replacements
            .insert((from.local, from.projection.as_slice()), to);
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

pub struct ReborrowVisitor<'a, 'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    analyzer: &'a mut super::Analyzer<'tcx, 'ctx>,
}

impl<'tcx> ReborrowVisitor<'_, 'tcx, '_> {
    fn insert_borrow(&mut self, place: mir::Place<'tcx>, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, Default::default()).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.borrow_place_(place, inner_ty);
        self.analyzer
            .bind_local(new_local, new_local_ty, mir::Mutability::Not);
        tracing::info!(old_place = ?place, ?new_local, "implicitly borrowed");
        new_local
    }

    fn insert_reborrow(&mut self, place: mir::Place<'tcx>, inner_ty: mir_ty::Ty<'tcx>) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_mut_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, Default::default()).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.borrow_place_(place, inner_ty);
        self.analyzer
            .bind_local(new_local, new_local_ty, mir::Mutability::Not);
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

        if place.projection.is_empty() && self.analyzer.is_mut_local(place.local) {
            let ty = self.analyzer.local_decls[place.local].ty;
            let new_local = self.insert_borrow(place.local.into(), ty);
            let new_place = self.tcx.mk_place_deref(new_local.into());
            ReplacePlacesVisitor::with_replacement(self.tcx, place.local.into(), new_place.clone())
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
                let new_local = self.insert_reborrow(place.clone(), *inner_ty);
                (new_local, new_local.into())
            }
            mir_ty::TyKind::Adt(adt, args) if adt.is_box() => {
                let inner_ty = args.type_at(0);
                let new_local = self.insert_borrow(place.clone(), inner_ty);
                (new_local, new_local.into())
            }
            _ => {
                let new_local = self.insert_borrow(place.clone(), ty);
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

        // TODO: !operand.is_move() ?
        if m.is_mut() {
            let new_local = self.insert_reborrow(self.tcx.mk_place_deref(p), *inner_ty);
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
        // dummy location
        mir::visit::MutVisitor::visit_statement(self, stmt, mir::Location::START);
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
    }
}
