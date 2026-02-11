use rustc_middle::mir::{self, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

pub struct RustCallVisitor<'a, 'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    analyzer: &'a mut crate::analyze::basic_block::Analyzer<'tcx, 'ctx>,
}

// TODO: consolidate logic with ReborrowVisitor
impl<'tcx> RustCallVisitor<'_, 'tcx, '_> {
    fn insert_immut_borrow(
        &mut self,
        place: mir::Place<'tcx>,
        inner_ty: mir_ty::Ty<'tcx>,
    ) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_imm_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, Default::default()).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.immut_borrow_place(place);
        self.analyzer.bind_local(new_local, new_local_ty);
        tracing::info!(old_place = ?place, ?new_local, "implicitly (imm-)borrowed");
        new_local
    }

    fn insert_immut_reborrow(
        &mut self,
        place: mir::Place<'tcx>,
        inner_ty: mir_ty::Ty<'tcx>,
    ) -> Local {
        let r = mir_ty::Region::new_from_kind(self.tcx, mir_ty::RegionKind::ReErased);
        let ty = mir_ty::Ty::new_imm_ref(self.tcx, r, inner_ty);
        let decl = mir::LocalDecl::new(ty, Default::default()).immutable();
        let new_local = self.analyzer.local_decls.push(decl);
        let new_local_ty = self.analyzer.immut_borrow_place(place);
        self.analyzer.bind_local(new_local, new_local_ty);
        tracing::info!(old_place = ?place, ?new_local, "implicitly (imm-)reborrowed");
        new_local
    }
}

impl<'a, 'tcx, 'ctx> mir::visit::MutVisitor<'tcx> for RustCallVisitor<'a, 'tcx, 'ctx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        if let mir::TerminatorKind::Call { func, args, .. } = &mut terminator.kind {
            if let Some((def_id, generic_args)) = func.const_fn_def() {
                if !self.analyzer.ctx().is_fn_trait_method(def_id) {
                    self.super_terminator(terminator, location);
                    return;
                }

                // RustCallVisitor expects all generic args to be already instantiated
                let mir_ty::TyKind::Closure(resolved_def_id, _) = generic_args.type_at(0).kind()
                else {
                    panic!("expected closure arg for fn trait");
                };
                let fn_sig = self
                    .analyzer
                    .ctx()
                    .local_fn_sig(resolved_def_id.expect_local());
                if !matches!(fn_sig.abi, rustc_target::spec::abi::Abi::RustCall) {
                    self.super_terminator(terminator, location);
                    return;
                }
                tracing::info!(?def_id, ?resolved_def_id, "handling RustCall function call");

                // three cases to consider:
                // 1. function of resolved_def_id takes &{closure} but def_id is FnMut::call_mut
                // 2. function of resolved_def_id takes &{closure} but def_id is FnOnce::call_once
                // 3. function of resolved_def_id takes &mut {closure} but def_id is FnOnce::call_once
                let resolved_closure_ty = fn_sig.inputs().first().unwrap();
                let arg_closure_ty = args
                    .first()
                    .unwrap()
                    .node
                    .ty(&self.analyzer.local_decls, self.tcx);
                let arg_closure_place = args.first().unwrap().node.place().unwrap();
                if matches!(
                    resolved_closure_ty.ref_mutability(),
                    Some(mir_ty::Mutability::Not)
                ) {
                    if let mir_ty::TyKind::Ref(_, closure_ty, mir_ty::Mutability::Mut) =
                        arg_closure_ty.kind()
                    {
                        // case 1: &mut {closure} -> &{closure}
                        let borrow_target_place = self.tcx.mk_place_deref(arg_closure_place);
                        let borrowed_closure_local =
                            self.insert_immut_reborrow(borrow_target_place, *closure_ty);
                        args[0].node = mir::Operand::Copy(borrowed_closure_local.into());
                        tracing::debug!("applied immut-reborrow for closure argument");
                    } else if arg_closure_ty.ref_mutability().is_none() {
                        // case 2: {closure} -> &{closure}
                        let borrowed_closure_local =
                            self.insert_immut_borrow(arg_closure_place, arg_closure_ty);
                        args[0].node = mir::Operand::Copy(borrowed_closure_local.into());
                        tracing::debug!("applied immut-borrow for closure argument");
                    }
                } else if matches!(
                    resolved_closure_ty.ref_mutability(),
                    Some(mir_ty::Mutability::Mut)
                    if arg_closure_ty.ref_mutability().is_none()
                ) {
                    // case 3: {closure} -> &mut {closure}
                    unimplemented!();
                }
            }
        }

        self.super_terminator(terminator, location);
    }
}

impl<'a, 'tcx, 'ctx> RustCallVisitor<'a, 'tcx, 'ctx> {
    pub fn new(analyzer: &'a mut crate::analyze::basic_block::Analyzer<'tcx, 'ctx>) -> Self {
        let tcx = analyzer.tcx;
        Self { analyzer, tcx }
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
    }
}
