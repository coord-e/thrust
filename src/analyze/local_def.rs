//! Analyze a local definition.

use std::collections::{HashMap, HashSet};

use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeAndMut};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::symbol::Ident;

use crate::analyze;
use crate::annot::{self, AnnotFormula, AnnotParser, ResolverExt as _};
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{self, BasicBlockType, TypeBuilder};
use crate::rty;

fn stmt_str_literal(stmt: &rustc_hir::Stmt) -> Option<String> {
    use rustc_ast::LitKind;
    use rustc_hir::{Expr, ExprKind, Stmt, StmtKind};

    match stmt {
        Stmt {
            kind:
                StmtKind::Semi(Expr {
                    kind:
                        ExprKind::Lit(rustc_hir::Lit {
                            node: LitKind::Str(symbol, _),
                            ..
                        }),
                    ..
                }),
            ..
        } => Some(symbol.to_string()),
        _ => None,
    }
}

/// An implementation of the typing of local definitions.
///
/// The current implementation only applies to function definitions. The entry point is
/// [`Analyzer::run`], which generates constraints during typing, given the expected type of the function.
pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,

    body: Body<'tcx>,
    /// to substitute HIR types during translation in [`crate::analyze::annot_fn`]
    generic_args: mir_ty::GenericArgsRef<'tcx>,
    drop_points: HashMap<BasicBlock, analyze::basic_block::DropPoints>,
    type_builder: TypeBuilder<'tcx>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn extract_param_annots<T>(
        &self,
        resolver: T,
        self_type_name: Option<String>,
    ) -> Vec<(Ident, rty::RefinedType<T::Output>)>
    where
        T: annot::Resolver,
    {
        let mut param_annots = Vec::new();
        let parser = AnnotParser::new(&resolver, self_type_name);
        for attrs in self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::param_path())
        {
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let (ident, ts) = analyze::annot::split_param(&ts);
            let param = parser.parse_rty(ts).unwrap();
            param_annots.push((ident, param));
        }
        param_annots
    }

    fn extract_ret_annot<T>(
        &self,
        resolver: T,
        self_type_name: Option<String>,
    ) -> Option<rty::RefinedType<T::Output>>
    where
        T: annot::Resolver,
    {
        let mut ret_annot = None;
        let parser = AnnotParser::new(&resolver, self_type_name);
        for attrs in self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::ret_path())
        {
            if ret_annot.is_some() {
                unimplemented!();
            }
            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let ret = parser.parse_rty(ts).unwrap();
            ret_annot = Some(ret);
        }
        ret_annot
    }

    fn impl_type(&self) -> Option<rustc_middle::ty::Ty<'tcx>> {
        use rustc_hir::def::DefKind;

        let parent_def_id = self.tcx.parent(self.local_def_id.to_def_id());

        if !matches!(self.tcx.def_kind(parent_def_id), DefKind::Impl { .. }) {
            return None;
        }

        let self_ty = self.tcx.type_of(parent_def_id).instantiate_identity();

        Some(self_ty)
    }

    pub fn analyze_predicate_definition(&self) {
        self.define_as_predicate(refine::user_defined_pred(
            self.tcx,
            self.local_def_id.to_def_id(),
        ));

        // For thrust::{requires,ensures} annotations which does not know DefId of the predicate
        // during parsing, we also define a predicate with a name based on the self type name
        //
        // TODO: remove this after we dropped old annotation parser impl
        //       (then move this to crate_::Analyzer)
        let pred_item_name = self
            .tcx
            .item_name(self.local_def_id.to_def_id())
            .to_string();
        if let Some(self_ty) = self.impl_type() {
            let name = chc::UserDefinedPred::new(self_ty.to_string() + "_" + &pred_item_name);
            self.define_as_predicate(name);
        }
    }

    fn define_as_predicate(&self, pred: chc::UserDefinedPred) {
        // function's body
        use rustc_hir::{Block, Expr, ExprKind};

        let hir_body = self.tcx.hir_maybe_body_owned_by(self.local_def_id).unwrap();

        let predicate_body = match hir_body.value {
            Expr {
                kind: ExprKind::Block(Block { stmts, .. }, _),
                ..
            } => stmts
                .iter()
                .find_map(stmt_str_literal)
                .expect("invalid predicate definition: no string literal was found."),
            _ => panic!("expected function body, got: {hir_body:?}"),
        };

        // names and sorts of arguments
        let arg_names = self
            .tcx
            .fn_arg_idents(self.local_def_id.to_def_id())
            .iter()
            .map(|ident| {
                ident
                    .expect("predicate arguments must be named")
                    .name
                    .to_string()
            });

        let sig = self.ctx.fn_sig(self.local_def_id.to_def_id());
        let arg_sorts = sig
            .inputs()
            .iter()
            .map(|input_ty| self.type_builder.build(*input_ty).to_sort());

        let arg_name_and_sorts = arg_names.into_iter().zip(arg_sorts).collect::<Vec<_>>();

        self.ctx.system.borrow_mut().push_pred_define(
            pred,
            chc::UserDefinedPredSig::from(arg_name_and_sorts),
            predicate_body,
        );
    }

    pub fn is_annotated_as_trusted(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::trusted_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_callable(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::callable_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_extern_spec_fn(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::extern_spec_fn_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_predicate(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::predicate_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_ignored(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::ignored_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_formula_fn(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::formula_fn_path(),
            )
            .next()
            .is_some()
    }

    // TODO: unify this logic with extraction functions above
    pub fn is_fully_annotated(&self) -> bool {
        let has_requires = self
            .tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::requires_path(),
            )
            .next()
            .is_some()
            || self
                .ctx
                .extract_path_with_attr(self.local_def_id, &analyze::annot::requires_path_path())
                .is_some();
        let has_ensures = self
            .tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::ensures_path(),
            )
            .next()
            .is_some()
            || self
                .ctx
                .extract_path_with_attr(self.local_def_id, &analyze::annot::ensures_path_path())
                .is_some();
        let annotated_params: Vec<_> = self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::param_path())
            .map(|attrs| {
                let ts = analyze::annot::extract_annot_tokens(attrs.clone());
                let (ident, _) = analyze::annot::split_param(&ts);
                ident
            })
            .collect();
        let has_ret = self
            .tcx
            .get_attrs_by_path(self.local_def_id.to_def_id(), &analyze::annot::ret_path())
            .next()
            .is_some();

        let arg_names = self.tcx.fn_arg_idents(self.local_def_id.to_def_id());
        let all_params_annotated = arg_names
            .iter()
            .all(|ident| ident.is_some_and(|i| annotated_params.contains(&i)));
        self.is_annotated_as_callable()
            || (has_requires && has_ensures)
            || (all_params_annotated && has_ret)
    }

    pub fn local_trait_item_id(&self) -> Option<LocalDefId> {
        let impl_item_assoc = self
            .tcx
            .opt_associated_item(self.local_def_id.to_def_id())?;
        let trait_item_id = impl_item_assoc
            .trait_item_def_id
            .and_then(|id| id.as_local())?;

        if trait_item_id == self.local_def_id {
            return None;
        }

        Some(trait_item_id)
    }

    pub fn trait_item_ty(&mut self) -> Option<rty::RefinedType> {
        let impl_did = self.tcx.parent(self.local_def_id.to_def_id());

        if self.tcx.def_kind(impl_did) != (rustc_hir::def::DefKind::Impl { of_trait: true }) {
            return None;
        }

        let trait_ref = self.tcx.impl_trait_ref(impl_did)?.instantiate_identity();
        let trait_item_did = self
            .tcx
            .associated_item(self.local_def_id.to_def_id())
            .trait_item_def_id
            .unwrap();
        self.ctx.def_ty_with_args(trait_item_did, trait_ref.args)
    }

    // TODO: Remove this eager precompute together with
    // `Analyzer::known_function_ty_with_args` once formula translation can call a read-only
    // `def_ty_with_args` directly.
    fn precompute_callable_param_contracts(&mut self, sig: &mir_ty::FnSig<'tcx>) {
        for input_ty in sig.inputs() {
            let inst =
                mir_ty::EarlyBinder::bind(*input_ty).instantiate(self.tcx, self.generic_args);
            let inst = self
                .tcx
                .normalize_erasing_regions(mir_ty::TypingEnv::fully_monomorphized(), inst);
            let (fn_def_id, fn_args) = match inst.kind() {
                mir_ty::TyKind::Closure(def_id, args) => {
                    (*def_id, self.tcx.mk_args(args.as_closure().parent_args()))
                }
                mir_ty::TyKind::FnDef(def_id, args) => (*def_id, *args),
                _ => continue,
            };
            if fn_def_id == self.local_def_id.to_def_id() {
                continue;
            }
            let _ = self.ctx.def_ty_with_args(fn_def_id, fn_args);
        }
    }

    // Note that we do not expect predicate variables to be generated here
    // when type params are still present in the type. Callers should ensure either
    // - type params are fully instantiated, or
    // - the function is fully annotated
    pub fn expected_ty(&mut self) -> rty::RefinedType {
        let sig = self
            .ctx
            .fn_sig_with_body(self.local_def_id.to_def_id(), &self.body);

        let mut param_resolver = analyze::annot::ParamResolver::default();
        for (input_ident, input_ty) in self
            .tcx
            .fn_arg_idents(self.local_def_id.to_def_id())
            .iter()
            .zip(sig.inputs())
        {
            let input_ty = self.type_builder.build(*input_ty);
            param_resolver.push_param(
                input_ident
                    .map(|i| i.name)
                    .unwrap_or(rustc_span::Symbol::intern("")),
                input_ty.to_sort(),
            );
        }

        let output_ty = self.type_builder.build(sig.output());
        let result_param_resolver = annot::StackedResolver::default()
            .resolver(analyze::annot::ResultResolver::new(output_ty.to_sort()))
            .resolver((&param_resolver).map(rty::RefinedTypeVar::Free));

        let self_type_name = self.impl_type().map(|ty| ty.to_string());

        // Formula translation for `pre!(f(..))`/`post!(f(..), result)` is read-only. If a callable
        // parameter resolves to a deferred closure/function def, force its analysis here so the
        // translator can later find the cached contract.
        self.precompute_callable_param_contracts(&sig);

        let mut require_annot = self.ctx.extract_require_annot(
            self.local_def_id,
            &param_resolver,
            self_type_name.clone(),
            self.generic_args,
        );

        let mut ensure_annot = self.ctx.extract_ensure_annot(
            self.local_def_id,
            &result_param_resolver,
            self_type_name.clone(),
            self.generic_args,
        );

        if let Some(trait_item_id) = self.local_trait_item_id() {
            tracing::info!("trait item found: {:?}", trait_item_id);
            let trait_require_annot = self.ctx.extract_require_annot(
                trait_item_id,
                &param_resolver,
                self_type_name.clone(),
                self.generic_args,
            );
            let trait_ensure_annot = self.ctx.extract_ensure_annot(
                trait_item_id,
                &result_param_resolver,
                self_type_name.clone(),
                self.generic_args,
            );

            assert!(require_annot.is_none() || trait_require_annot.is_none());
            require_annot = require_annot.or(trait_require_annot);

            assert!(ensure_annot.is_none() || trait_ensure_annot.is_none());
            ensure_annot = ensure_annot.or(trait_ensure_annot);
        }

        let param_annots = self.extract_param_annots(&param_resolver, self_type_name.clone());
        let ret_annot = self.extract_ret_annot(&param_resolver, self_type_name);

        if self.is_annotated_as_callable() {
            if require_annot.is_some() || ensure_annot.is_some() {
                unimplemented!();
            }
            if !param_annots.is_empty() || ret_annot.is_some() {
                unimplemented!();
            }

            require_annot = Some(AnnotFormula::top());
            ensure_annot = Some(AnnotFormula::top());
        }

        assert!(require_annot.is_none() || param_annots.is_empty());
        assert!(ensure_annot.is_none() || ret_annot.is_none());

        let refinement_annots = self
            .ctx
            .extract_refinement_annots(self.local_def_id, self.generic_args);

        let trait_item_ty = self.trait_item_ty();
        let is_fully_annotated = self.is_fully_annotated();

        let mut builder = self.type_builder.for_function_template(&mut self.ctx, sig);
        if let Some(AnnotFormula::Formula(require)) = require_annot {
            let formula = require.map_var(|idx| {
                if idx.index() == sig.inputs().len() - 1 {
                    rty::RefinedTypeVar::Value
                } else {
                    rty::RefinedTypeVar::Free(idx)
                }
            });
            builder.param_refinement(formula.into());
        }
        if let Some(AnnotFormula::Formula(ensure)) = ensure_annot {
            builder.ret_refinement(ensure.into());
        }
        for (ident, annot_rty) in param_annots {
            use annot::Resolver as _;
            let (idx, _) = param_resolver.resolve(ident).expect("unknown param");
            builder.param_rty(idx, annot_rty);
        }
        if let Some(ret_rty) = ret_annot {
            builder.ret_rty(ret_rty);
        }
        for (position, refinement) in refinement_annots {
            builder.refinement_at(&position, refinement);
        }

        if is_fully_annotated {
            rty::RefinedType::unrefined(builder.build().into())
        } else if let Some(trait_item_ty) = trait_item_ty {
            trait_item_ty
        } else {
            rty::RefinedType::unrefined(builder.build().into())
        }
    }

    /// Extract the target DefId from `#[thrust::extern_spec_fn]` function.
    ///
    /// The target is identified as the tail call expression (last expression without
    /// semicolon) in the function body block.
    pub fn extern_spec_fn_target_def_id(&self) -> DefId {
        let node = self.tcx.hir_node_by_def_id(self.local_def_id);
        let body_id = match node {
            rustc_hir::Node::Item(item) => {
                let rustc_hir::ItemKind::Fn { body: body_id, .. } = item.kind else {
                    panic!("extern_spec_fn must be a function");
                };
                body_id
            }
            rustc_hir::Node::ImplItem(impl_item) => {
                let rustc_hir::ImplItemKind::Fn(_, body_id) = impl_item.kind else {
                    panic!("extern_spec_fn must be a function");
                };
                body_id
            }
            rustc_hir::Node::TraitItem(trait_item) => {
                let rustc_hir::TraitItemKind::Fn(_, rustc_hir::TraitFn::Provided(body_id)) =
                    trait_item.kind
                else {
                    panic!("extern_spec_fn must be a function with a body");
                };
                body_id
            }
            _ => panic!("extern_spec_fn must be a function item or impl item"),
        };

        let body = self.tcx.hir_body(body_id);

        // The body is a block; the tail expression is the function call to the target.
        let rustc_hir::ExprKind::Block(block, _) = &body.value.kind else {
            panic!("extern_spec_fn body must be a block");
        };
        let tail_expr = block
            .expr
            .expect("extern_spec_fn block must end with a tail call expression");

        let rustc_hir::ExprKind::Call(func_expr, _) = &tail_expr.kind else {
            panic!("extern_spec_fn tail expression must be a function call");
        };
        let rustc_hir::ExprKind::Path(qpath) = &func_expr.kind else {
            panic!("extern_spec_fn call must be a path expression");
        };

        let typeck_result = self.tcx.typeck(self.local_def_id);
        let hir_id = func_expr.hir_id;
        let rustc_hir::def::Res::Def(_, def_id) = typeck_result.qpath_res(qpath, hir_id) else {
            panic!("extern_spec_fn call must resolve to a definition");
        };

        let args = typeck_result.node_args(hir_id);
        let typing_env = self.body.typing_env(self.tcx);
        let instance = mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args).unwrap();
        if let Some(instance) = instance {
            instance.def_id()
        } else {
            def_id
        }
    }

    fn is_mut_param(&self, param_idx: rty::FunctionParamIdx) -> bool {
        let param_local = analyze::local_of_function_param(param_idx);
        self.body.local_decls[param_local].mutability.is_mut()
    }

    fn extract_elaborated_deref(
        &self,
        stmt: &mir::Statement<'tcx>,
    ) -> Option<(Local, mir::Place<'tcx>)> {
        let mir::StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        let (lhs, rvalue) = &**assign;
        if !lhs.projection.as_ref().is_empty() {
            return None;
        }
        let lhs_local = lhs.local;

        if let mir::Rvalue::CopyForDeref(place) = &rvalue {
            return Some((lhs_local, *place));
        }

        let unique_did = self.ctx.def_ids.unique()?;
        let nonnull_did = self.ctx.def_ids.nonnull()?;

        use mir::ProjectionElem::Field;
        use rustc_abi::FieldIdx;
        const ZERO_FIELD: FieldIdx = FieldIdx::from_u32(0);

        // Box deref pattern: `(_box.0.0 as *const T) Transmute`
        //   projection = [..., Field(0, Unique<T>), Field(0, NonNull<T>)], transmuted to *const T
        let mir::Rvalue::Cast(mir::CastKind::Transmute, mir::Operand::Copy(place), cast_ty) =
            &rvalue
        else {
            return None;
        };
        if !matches!(cast_ty.kind(), mir_ty::TyKind::RawPtr(_, mutbl) if mutbl.is_not()) {
            return None;
        }
        let Some((rest, [Field(ZERO_FIELD, ty0), Field(ZERO_FIELD, ty1)])) =
            place.projection.as_slice().split_last_chunk::<2>()
        else {
            return None;
        };
        let rest_place = mir::Place {
            local: place.local,
            projection: self.tcx.mk_place_elems(rest),
        };
        let local_ty = rest_place.ty(&self.body.local_decls, self.tcx).ty;
        if !local_ty.is_box() {
            return None;
        }
        let inner_ty = local_ty.boxed_ty()?;
        if !matches!(ty0.kind(), mir_ty::TyKind::Adt(def, args)
            if def.did() == unique_did && args.type_at(0) == inner_ty)
        {
            return None;
        }
        if !matches!(ty1.kind(), mir_ty::TyKind::Adt(def, args)
            if def.did() == nonnull_did && args.type_at(0) == inner_ty)
        {
            return None;
        }
        Some((lhs_local, rest_place))
    }

    fn unelaborate_derefs(&mut self) {
        let mut v = analyze::ReplacePlacesVisitor::new(self.tcx);
        for (block, data) in self.body.basic_blocks.clone().iter_enumerated() {
            for (idx, _stmt) in data.statements.iter().enumerate() {
                let stmt =
                    &mut self.body.basic_blocks.as_mut().as_mut_slice()[block].statements[idx];
                v.visit_statement(stmt);
                let stmt = stmt.clone();
                let Some((dest_local, box_place)) = self.extract_elaborated_deref(&stmt) else {
                    continue;
                };
                self.body.basic_blocks.as_mut().as_mut_slice()[block].statements[idx].kind =
                    mir::StatementKind::Nop;
                v.add_replacement(dest_local.into(), box_place);
            }
            if let Some(tmnt) =
                &mut self.body.basic_blocks.as_mut().as_mut_slice()[block].terminator
            {
                v.visit_terminator(tmnt);
            }
        }
    }

    fn mut_locals(
        &self,
        data: &mir::BasicBlockData<'tcx>,
        statement_index: usize,
    ) -> DenseBitSet<Local> {
        struct Visitor<'tcx, 'a> {
            tcx: TyCtxt<'tcx>,
            body: &'a Body<'tcx>,

            locals: DenseBitSet<Local>,
        }
        impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'tcx, '_> {
            fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
                if let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place) = rvalue {
                    self.locals.insert(place.local);
                }
                self.super_rvalue(rvalue, location);
            }

            fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: mir::Location) {
                // to be reborrowed; see analyze::basic_block::visitor. A `&mut`
                // field read out of an aggregate is `copy (_1.0)`, so match Copy
                // too to mark the base local. Reference only: `is_mutable_ptr()`
                // also covers `*mut`, which is Copy but never reborrowed.
                if let mir::Operand::Move(place) | mir::Operand::Copy(place) = operand {
                    if matches!(
                        place.ty(&self.body.local_decls, self.tcx).ty.kind(),
                        mir_ty::TyKind::Ref(_, _, m) if m.is_mut()
                    ) {
                        self.locals.insert(place.local);
                    }
                }
                self.super_operand(operand, location);
            }

            fn visit_terminator(
                &mut self,
                terminator: &mir::Terminator<'tcx>,
                location: mir::Location,
            ) {
                // calling an FnMut closure via FnOnce::call_once resolves to the closure
                // function taking &mut {closure}, so RustCallVisitor mutably borrows the
                // closure argument; see analyze::basic_block::visitor
                if let mir::TerminatorKind::Call { func, args, .. } = &terminator.kind {
                    if let Some((def_id, generic_args)) = func.const_fn_def() {
                        let trait_did = self
                            .tcx
                            .opt_associated_item(def_id)
                            .and_then(|item| item.trait_container(self.tcx));
                        if trait_did.is_some() && trait_did == self.tcx.lang_items().fn_once_trait()
                        {
                            if let mir_ty::TyKind::Closure(_, closure_args) =
                                generic_args.type_at(0).kind()
                            {
                                if closure_args.as_closure().kind() == mir_ty::ClosureKind::FnMut {
                                    if let Some(place) = args[0].node.place() {
                                        self.locals.insert(place.local);
                                    }
                                }
                            }
                        }
                    }
                }
                self.super_terminator(terminator, location);
            }

            fn visit_assign(
                &mut self,
                place: &mir::Place<'tcx>,
                rvalue: &mir::Rvalue<'tcx>,
                location: mir::Location,
            ) {
                self.locals.insert(place.local);
                self.super_assign(place, rvalue, location);
            }
        }

        let mut visitor = Visitor {
            tcx: self.tcx,
            body: &self.body,
            locals: DenseBitSet::new_empty(self.body.local_decls.len()),
        };
        let loc = mir::Location::START;
        use mir::visit::Visitor as _;
        if statement_index < data.statements.len() {
            visitor.visit_statement(&data.statements[statement_index], loc);
        } else if let Some(tmnt) = &data.terminator {
            visitor.visit_terminator(tmnt, loc);
        }
        visitor.locals
    }

    // XXX: In nightly-2024-09-08, `MaybeInitializedPlaces::switch_int_edge_effects`
    //      requires `SwitchInt` values to be in the same order as `AdtDef::discriminants`.
    //      Since optimizations can sometimes break this order, we normalize it beforehand.
    //
    // > thread 'rustc' panicked at /rustc/12b26c13fba25c9e1bc2fdf05f3c2dbb851c83de/compiler/rustc_mir_dataflow/src/impls/initialized.rs:431:18:
    // > Order of `AdtDef::discriminants` differed from `SwitchInt::values`
    fn normalize_switch_int_discriminant_order(&mut self) {
        let blocks = self.body.basic_blocks.as_mut().as_mut_slice();
        for block in blocks.iter_mut() {
            let Some(terminator) = &mut block.terminator else {
                continue;
            };
            let mir::TerminatorKind::SwitchInt { discr, targets } = &mut terminator.kind else {
                continue;
            };
            let Some(discr_place) = discr.place() else {
                continue;
            };

            let enum_adt = block.statements.iter().rev().find_map(|stmt| {
                let mir::StatementKind::Assign(assign) = &stmt.kind else {
                    return None;
                };
                let (lhs, mir::Rvalue::Discriminant(disc_place)) = assign.as_ref() else {
                    return None;
                };
                if *lhs != discr_place {
                    return None;
                }
                let ty = disc_place.ty(&self.body.local_decls, self.tcx).ty;
                if let mir_ty::TyKind::Adt(def, _) = ty.kind() {
                    Some(*def)
                } else {
                    None
                }
            });
            let Some(adt_def) = enum_adt else {
                continue;
            };

            let otherwise = targets.otherwise();
            let mut pairs: Vec<(u128, mir::BasicBlock)> = targets.iter().collect();
            let discriminant_order: Vec<u128> = adt_def
                .discriminants(self.tcx)
                .map(|(_, discr)| discr.val)
                .collect();
            pairs.sort_by_key(|(val, _)| {
                discriminant_order
                    .iter()
                    .position(|d| d == val)
                    .unwrap_or(usize::MAX)
            });
            *targets = mir::SwitchTargets::new(pairs.into_iter(), otherwise);
        }
    }

    fn reassign_local_mutabilities(&mut self) {
        use rustc_mir_dataflow::{
            move_paths::{HasMoveData as _, MoveData},
            Analysis as _, MaybeReachable,
        };

        self.normalize_switch_int_discriminant_order();

        for local_decl in &mut self.body.local_decls {
            local_decl.mutability = mir::Mutability::Not;
        }

        let move_data = {
            // XXX: what...
            let mut body = self.body.clone();
            struct Visitor {
                deref_temps: DenseBitSet<Local>,
            }
            impl<'tcx> mir::visit::Visitor<'tcx> for Visitor {
                fn visit_assign(
                    &mut self,
                    place: &mir::Place<'tcx>,
                    rvalue: &mir::Rvalue<'tcx>,
                    _location: mir::Location,
                ) {
                    if let mir::Rvalue::CopyForDeref { .. } = rvalue {
                        self.deref_temps.insert(place.local);
                    }
                }
            }
            let mut visitor = Visitor {
                deref_temps: DenseBitSet::new_empty(body.local_decls.len()),
            };
            use mir::visit::Visitor as _;
            visitor.visit_body(&body);
            for (local, local_decl) in body.local_decls.iter_enumerated_mut() {
                let local_info = if visitor.deref_temps.contains(local) {
                    mir::LocalInfo::DerefTemp
                } else {
                    mir::LocalInfo::Boring
                };
                local_decl.local_info = mir::ClearCrossCrate::Set(Box::new(local_info));
            }
            MoveData::gather_moves(&body, self.tcx, |_| true)
        };
        let tmp_body = self.body.clone();
        let mut results =
            rustc_mir_dataflow::impls::MaybeInitializedPlaces::new(self.tcx, &tmp_body, &move_data)
                .iterate_to_fixpoint(self.tcx, &self.body, None)
                .into_results_cursor(&tmp_body);

        let mut zst_locals = DenseBitSet::new_empty(self.body.local_decls.len());
        for (local, local_decl) in self.body.local_decls.iter_enumerated() {
            let ty = local_decl.ty;
            if self
                .tcx
                .layout_of(self.body.typing_env(self.tcx).as_query_input(ty))
                .map(|l| l.is_zst())
                .unwrap_or(false)
            {
                zst_locals.insert(local);
            }
        }

        for (block, data) in mir::traversal::preorder(&tmp_body) {
            for statement_index in 0..=data.statements.len() {
                let loc = mir::Location {
                    statement_index,
                    block,
                };
                results.seek_before_primary_effect(loc);
                let MaybeReachable::Reachable(init_places) = results.get() else {
                    continue;
                };
                let init_locals: HashSet<_> = init_places
                    .iter()
                    .map(|p| results.analysis().move_data().move_paths[p].place.local)
                    .collect();
                let mut_locals = self.mut_locals(data, statement_index);
                tracing::info!(
                    ?init_locals,
                    ?mut_locals,
                    ?zst_locals,
                    ?statement_index,
                    ?block,
                    stmt = ?data.statements.get(statement_index),
                );
                for mut_local in mut_locals.iter() {
                    if init_locals.contains(&mut_local) || zst_locals.contains(mut_local) {
                        self.body.local_decls[mut_local].mutability = mir::Mutability::Mut;
                        tracing::info!(?mut_local, ?statement_index, ?block, "marking mut");
                    }
                }
            }
        }
    }

    /// Scans the body for loop-invariant marker calls and groups them by
    /// enclosing loop header. Multiple invariants for the same header are kept
    /// in source order; the caller is responsible for AND'ing them.
    fn collect_loop_invariant_annotations(
        &self,
    ) -> HashMap<BasicBlock, Vec<(LocalDefId, mir_ty::GenericArgsRef<'tcx>)>> {
        let mut loop_invariants: HashMap<_, Vec<_>> = HashMap::new();
        for (bb, data) in self.body.basic_blocks.iter_enumerated() {
            let Some(term) = &data.terminator else {
                continue;
            };
            let mir::TerminatorKind::Call { func, args, .. } = &term.kind else {
                continue;
            };
            let Some((def_id, _)) = func.const_fn_def() else {
                continue;
            };
            if Some(def_id) != self.ctx.def_ids().invariant_marker() {
                continue;
            }

            let arg_ty = args[0].node.ty(&self.body.local_decls, self.tcx);
            let mir_ty::TyKind::FnDef(formula_def_id, generic_args) = arg_ty.kind() else {
                panic!("invariant marker argument must be a formula function item");
            };
            let formula_def_id = formula_def_id
                .as_local()
                .expect("invariant formula function must be local");
            let header = Self::loop_header_of(&self.body, bb).unwrap_or_else(|| {
                panic!("no enclosing loop header for invariant marker at {bb:?}")
            });
            loop_invariants
                .entry(header)
                .or_default()
                .push((formula_def_id, *generic_args));
        }
        loop_invariants
    }

    /// Walks up the dominator tree from the marker block to the innermost
    /// enclosing loop header: the first dominator that needs its own
    /// precondition (in-degree >= 2) and has a back edge.
    fn loop_header_of(body: &Body<'_>, marker_bb: BasicBlock) -> Option<BasicBlock> {
        let doms = body.basic_blocks.dominators();
        let preds = body.basic_blocks.predecessors();
        let mut cur = Some(marker_bb);
        while let Some(bb) = cur {
            if analyze::basic_block::needs_own_precondition(body, bb)
                && preds[bb].iter().any(|&p| doms.dominates(bb, p))
            {
                return Some(bb);
            }
            cur = doms.immediate_dominator(bb);
        }
        None
    }

    /// Resolves the live local matching a source variable name at the given
    /// basic block, among the locals that are parameters of `bty`.
    ///
    /// When several distinct live locals share the name (e.g. two shadowed
    /// variables that are both loop-carried), the mapping is ambiguous; rather
    /// than silently pick one, this raises a fatal error. Disambiguating which
    /// shadow an invariant refers to is left as future work.
    fn local_of_name_in_bb(&self, name: rustc_span::Symbol, bty: &BasicBlockType) -> Option<Local> {
        let mut found: Option<Local> = None;
        for vdi in &self.body.var_debug_info {
            if vdi.name != name {
                continue;
            }
            let mir::VarDebugInfoContents::Place(place) = vdi.value else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            if bty.param_of_local(place.local).is_none() {
                continue;
            }
            match found {
                None => found = Some(place.local),
                Some(prev) if prev == place.local => {}
                Some(_) => self.tcx.dcx().fatal(format!(
                    "loop invariant refers to `{name}`, which is ambiguous at the loop header: \
                     multiple live variables share this name (e.g. through shadowing). \
                     Rename the variables to disambiguate."
                )),
            }
        }
        found
    }

    fn function_param_local_of_name(&self, name: rustc_span::Symbol) -> Option<Local> {
        let mut found: Option<Local> = None;
        for vdi in &self.body.var_debug_info {
            if vdi.name != name {
                continue;
            }
            let mir::VarDebugInfoContents::Place(place) = vdi.value else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            let local = place.local;
            if local.index() == 0 || local.index() > self.body.arg_count {
                continue;
            }
            match found {
                None => found = Some(local),
                Some(prev) if prev == local => {}
                Some(_) => panic!("multiple function arguments share the name `{name}`"),
            }
        }
        found
    }

    /// Translates a user-provided loop invariant (a formula function over named
    /// live variables) into a precondition refinement over `bty`'s parameters.
    /// Each formula parameter names a live variable at the loop header and is
    /// mapped to the corresponding basic-block parameter.
    fn build_invariant_precondition(
        &self,
        formula_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        bty: &BasicBlockType,
    ) -> rty::Refinement<rty::FunctionParamIdx> {
        let formula_fn = self
            .ctx
            .formula_fn_with_args(formula_def_id, generic_args)
            .expect("invariant formula function is not registered");
        let idents = self.tcx.fn_arg_idents(formula_def_id.to_def_id());
        let sig = self
            .tcx
            .fn_sig(formula_def_id.to_def_id())
            .instantiate(self.tcx, generic_args);

        let mut mapping: Vec<rty::FunctionParamIdx> = Vec::with_capacity(idents.len());
        for (ident_opt, input_ty) in idents.iter().zip(sig.skip_binder().inputs()) {
            let name = ident_opt.expect("invariant parameters must be named").name;
            let input_ty = {
                let typing_env =
                    mir_ty::TypingEnv::post_analysis(self.tcx, formula_def_id.to_def_id());
                self.tcx
                    .try_normalize_erasing_regions(typing_env, *input_ty)
                    .unwrap_or(*input_ty)
            };

            // The synthetic `__thrust_self` parameter (emitted when an invariant refers to the receiver
            // `self`) maps to the loop-carried receiver, which appears as `self` in debug info.
            let name = if name.as_str() == "__thrust_self" {
                rustc_span::Symbol::intern("self")
            } else {
                name
            };

            if input_ty
                .ty_adt_def()
                .is_some_and(|def| Some(def.did()) == self.ctx.def_ids().fn_param_wrapper())
            {
                let local = self.function_param_local_of_name(name).unwrap_or_else(|| {
                    self.tcx.dcx().fatal(format!(
                        "loop invariant refers to `{name}` via FnParam, but it is not a function parameter"
                    ))
                });
                let param_idx = crate::analyze::function_param_of_local(local);
                mapping.push(bty.param_of_outer_fn_param(param_idx).unwrap());
            } else {
                let local = self.local_of_name_in_bb(name, bty).unwrap_or_else(|| {
                    self.tcx.dcx().fatal(format!(
                        "loop invariant refers to `{name}`, which is not a live variable at the loop header"
                    ))
                });
                mapping.push(bty.param_of_local(local).unwrap());
            }
        }

        formula_fn
            .formula()
            .clone()
            .subst_var(|idx| chc::Term::var(rty::RefinedTypeVar::Free(mapping[idx.index()])))
            .into()
    }

    fn refine_basic_blocks(&mut self) {
        use rustc_mir_dataflow::Analysis as _;
        let loop_invariants = self.collect_loop_invariant_annotations();
        let mut results = rustc_mir_dataflow::impls::MaybeLiveLocals
            .iterate_to_fixpoint(self.tcx, &self.body, None)
            .into_results_cursor(&self.body);

        let mut builder = analyze::basic_block::DropPoints::builder(&self.body);
        for (bb, _data) in mir::traversal::postorder(&self.body) {
            let span = tracing::info_span!("refine_basic_block", ?bb);
            let _guard = span.enter();

            self.drop_points.insert(bb, builder.build(&mut results, bb));
            results.seek_to_block_start(bb);
            let mut live_locals: Vec<_> = results
                .get()
                .iter()
                .map(|in_local| {
                    let decl = &self.body.local_decls[in_local];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    (in_local, type_and_mut)
                })
                .collect();
            // TODO: ad-hoc
            if bb == mir::START_BLOCK {
                for a in self.body.args_iter() {
                    if live_locals.iter().any(|(l, _)| *l == a) {
                        continue;
                    }
                    let decl = &self.body.local_decls[a];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    live_locals.push((a, type_and_mut));
                    self.drop_points
                        .get_mut(&bb)
                        .unwrap()
                        .before_statements
                        .push(a);
                }
            }
            // function return type is basic block return type
            let ret_ty = self.body.local_decls[mir::RETURN_PLACE].ty;
            if let Some(invariants) = loop_invariants.get(&bb) {
                // A user-supplied loop invariant fully replaces inference: build
                // the block type without a precondition pvar and install the
                // invariant as its precondition. Multiple `invariant!` calls at
                // the same header are AND'd in source order.
                let mut bty = self
                    .type_builder
                    .build_basic_block(&self.body, live_locals, ret_ty);
                let mut inv = rty::Refinement::top();
                for &(formula_def_id, generic_args) in invariants {
                    let one = self.build_invariant_precondition(formula_def_id, generic_args, &bty);
                    inv.push_conj(one);
                }
                bty.set_precondition(inv);
                self.ctx
                    .register_basic_block_ty_with_precondition(self.local_def_id, bb, bty);
            } else if analyze::basic_block::needs_own_precondition(&self.body, bb) {
                let bty = self
                    .type_builder
                    .for_template(&mut self.ctx)
                    .build_basic_block(&self.body, live_locals, ret_ty);
                self.ctx
                    .register_basic_block_ty_with_precondition(self.local_def_id, bb, bty);
            } else {
                // The block inherits its predecessor's outgoing env state as its
                // precondition, materialized lazily during the predecessor's
                // analysis. Record only unrefined type here.
                let bty = self
                    .type_builder
                    .build_basic_block(&self.body, live_locals, ret_ty);
                self.ctx
                    .register_basic_block_ty_without_precondition(self.local_def_id, bb, bty);
            };
        }
    }

    fn analyze_basic_blocks(&mut self, expected_fn_ty: &rty::RefinedType) {
        let expected_fn_ty = expected_fn_ty.ty.as_function().unwrap();
        // Reverse postorder guarantees each block that inherits its precondition
        // is visited after the predecessor that lazily materialized its type.
        for (bb, data) in mir::traversal::reverse_postorder(&self.body) {
            if data.is_cleanup {
                continue;
            }
            let rty = self
                .ctx
                .basic_block_ty_with_precondition(self.local_def_id, bb)
                .clone();
            let drop_points = self.drop_points[&bb].clone();
            self.ctx
                .basic_block_analyzer(self.local_def_id, bb)
                .body(self.body.clone())
                .drop_points(drop_points)
                .run(&rty, expected_fn_ty);
        }
    }

    fn elaborate_mut_params(&self, fn_ty: &mut rty::FunctionType) {
        if self.body.arg_count == 0 {
            return;
        }

        for (param_idx, param_ty) in fn_ty.params.iter_enumerated_mut() {
            let ty = if self.is_mut_param(param_idx) {
                rty::PointerType::own(param_ty.ty.clone()).into()
            } else {
                param_ty.ty.clone()
            };
            *param_ty = rty::RefinedType::new(
                ty,
                param_ty
                    .refinement
                    .clone()
                    .subst_value_var(|| {
                        if self.is_mut_param(param_idx) {
                            chc::Term::var(rty::RefinedTypeVar::Value).box_current()
                        } else {
                            chc::Term::var(rty::RefinedTypeVar::Value)
                        }
                    })
                    .subst_free_var(|v| {
                        if self.is_mut_param(v) {
                            chc::Term::var(v).box_current()
                        } else {
                            chc::Term::var(v)
                        }
                    }),
            );
        }

        fn_ty.ret.refinement = fn_ty.ret.refinement.clone().subst_free_var(|v| {
            if self.is_mut_param(v) {
                chc::Term::var(v).box_current()
            } else {
                chc::Term::var(v)
            }
        });
    }

    /// Drop excessive parameters from the BB-side entry function type that do not
    /// correspond to any function argument. These are introduced by ZST locals whose
    /// liveness analysis treats them as live without an explicit def.
    fn drop_bb_zst_params(&self, bb_ty: &BasicBlockType) -> rty::FunctionType {
        let mut fn_ty = bb_ty.to_function_ty();
        let arg_locals: HashSet<_> = self.body.args_iter().collect();

        for idx in bb_ty.local_params().rev() {
            let local = bb_ty.local_of_param(idx).unwrap();
            if !arg_locals.contains(&local) {
                fn_ty.remove_param(idx);
            }
        }

        // A function type must keep at least one parameter to host the precondition
        // predicate. When the function has no real argument, both the expected type and
        // the BB type carry a synthetic unit parameter (see
        // `crate::refine::TypeBuilder::build_basic_block`). That synthetic has no
        // backing local, so it survives the drop loop untouched. If instead the entry
        // block exposed only ZST-local parameters (e.g. `RETURN_PLACE`), dropping them
        // empties the type, and we re-introduce the synthetic unit parameter carrying
        // the precondition refinement of the last dropped parameter.
        if self.body.arg_count == 0 && fn_ty.params.is_empty() {
            let refinement = bb_ty.as_ref().last_param().unwrap().refinement.clone();
            fn_ty
                .params
                .push(rty::RefinedType::new(rty::Type::unit(), refinement));
        }

        fn_ty
    }

    /// Drop function parameters from `expected_ty` whose corresponding local is unused
    /// (and thus not represented) in the BB-side entry function type.
    fn drop_unused_expected_params(
        &self,
        expected_ty: &mut rty::FunctionType,
        bb_ty: &BasicBlockType,
    ) {
        if self.body.arg_count == 0 {
            return;
        }
        let arg_locals: HashSet<_> = self.body.args_iter().collect();
        let present_arg_locals: HashSet<_> = bb_ty
            .locals()
            .filter(|local| arg_locals.contains(local))
            .collect();
        for idx in expected_ty.params.indices().rev() {
            let arg_local = analyze::local_of_function_param(idx);
            if !present_arg_locals.contains(&arg_local) {
                expected_ty.remove_param(idx);
            }
        }
    }

    fn assert_entry(&mut self, expected: &rty::RefinedType) {
        let mut entry_ty = self
            .ctx
            .basic_block_ty_with_precondition(self.local_def_id, mir::START_BLOCK)
            .clone();
        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry before");
        let mut expected = expected.ty.as_function().cloned().unwrap();
        self.elaborate_mut_params(&mut expected);

        entry_ty.truncate_outer_fn_params();
        self.drop_unused_expected_params(&mut expected, &entry_ty);
        let entry_ty = self.drop_bb_zst_params(&entry_ty);

        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry after");
        let clauses = rty::relate_sub_param_types(&entry_ty.params, &expected.params);
        self.ctx.extend_clauses(clauses);
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(ctx: &'ctx mut analyze::Analyzer<'tcx>, local_def_id: LocalDefId) -> Self {
        let tcx = ctx.tcx;
        let body = tcx.optimized_mir(local_def_id.to_def_id()).clone();
        let drop_points = Default::default();
        let type_builder = TypeBuilder::new(tcx, ctx.def_ids(), local_def_id.to_def_id());
        let generic_args = tcx.mk_args(&[]);
        Self {
            ctx,
            tcx,
            local_def_id,
            body,
            generic_args,
            drop_points,
            type_builder,
        }
    }

    pub fn local_def_id(&self) -> LocalDefId {
        self.local_def_id
    }

    pub fn generic_args(&mut self, generic_args: mir_ty::GenericArgsRef<'tcx>) -> &mut Self {
        self.generic_args = generic_args;
        self.body =
            mir_ty::EarlyBinder::bind(self.body.clone()).instantiate(self.tcx, generic_args);
        self
    }

    pub fn run(&mut self, expected: &rty::RefinedType) {
        let span = tracing::info_span!("def", def = %self.tcx.def_path_str(self.local_def_id));
        let _guard = span.enter();

        self.unelaborate_derefs();
        self.reassign_local_mutabilities();
        self.refine_basic_blocks();
        self.analyze_basic_blocks(expected);
        self.assert_entry(expected);
    }
}
