use std::collections::HashMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Body};
use rustc_middle::ty::{TyCtxt, TypeAndMut};
use rustc_span::def_id::LocalDefId;

use crate::analyze;
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{BasicBlockType, TemplateTypeGenerator};
use crate::rty;

pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,
    body: &'tcx Body<'tcx>,

    drop_points: HashMap<BasicBlock, analyze::basic_block::DropPoints>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn is_mut_param(&self, param_idx: rty::FunctionParamIdx) -> bool {
        let param_local = analyze::local_of_function_param(param_idx);
        self.body.local_decls[param_local].mutability.is_mut()
    }

    fn refine_basic_blocks(&mut self) {
        use rustc_mir_dataflow::Analysis as _;
        let mut results = rustc_mir_dataflow::impls::MaybeLiveLocals
            .into_engine(self.tcx, self.body)
            .iterate_to_fixpoint()
            .into_results_cursor(self.body);

        let mut builder = analyze::basic_block::DropPoints::builder(self.body);
        for (bb, _data) in mir::traversal::postorder(self.body) {
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
            let rty = self.ctx.mir_basic_block_ty(live_locals, ret_ty);
            self.ctx.register_basic_block_ty(self.local_def_id, bb, rty);
        }
    }

    fn analyze_basic_blocks(&mut self) {
        for bb in self.body.basic_blocks.indices() {
            let rty = self.ctx.basic_block_ty(self.local_def_id, bb).clone();
            let drop_points = self.drop_points[&bb].clone();
            self.ctx
                .basic_block_analyzer(self.local_def_id, bb)
                .drop_points(drop_points)
                .run(&rty);
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
                    .subst_var(|v| {
                        if self.is_mut_param(v) {
                            chc::Term::var(v).box_current()
                        } else {
                            chc::Term::var(v)
                        }
                    }),
            );
        }

        fn_ty.ret.refinement = fn_ty.ret.refinement.clone().subst_var(|v| {
            if self.is_mut_param(v) {
                chc::Term::var(v).box_current()
            } else {
                chc::Term::var(v)
            }
        });
    }

    // TODO: remove this
    fn elaborate_unused_args(
        &self,
        bb_ty: &BasicBlockType,
        expected_ty: &rty::FunctionType,
    ) -> rty::FunctionType {
        let mut params = IndexVec::new();
        let mut subst = HashMap::new();
        for (param_idx, param_ty) in bb_ty.as_ref().params.iter_enumerated() {
            if let Some(param_local) = bb_ty.local_of_param(param_idx) {
                // unit return may use _0 without preceeding def
                if param_local == mir::RETURN_PLACE {
                    subst.extend(
                        bb_ty
                            .as_ref()
                            .params
                            .indices()
                            .skip_while(|idx| idx.index() <= param_idx.index())
                            .map(|idx| (idx, idx + 1)),
                    );
                    if bb_ty.as_ref().params.len() == 1 {
                        params.push(rty::RefinedType::new(
                            rty::Type::unit(),
                            param_ty.refinement.clone(),
                        ));
                    }
                    continue;
                }
                while analyze::local_of_function_param(params.next_index()) != param_local {
                    tracing::debug!(next_idx = ?params.next_index(), param_local = ?param_local, "elaborate_unused_args");
                    let mock_ty = expected_ty.params[params.next_index()].ty.clone();
                    params.push(rty::RefinedType::unrefined(mock_ty).vacuous());
                }
            }
            subst.insert(param_idx, params.next_index());
            params.push(param_ty.clone().map_var(|v| subst[&v]));
        }
        rty::FunctionType::new(params, bb_ty.as_ref().ret.clone().map_var(|v| subst[&v]))
    }

    fn assert_entry(&mut self, expected: &rty::RefinedType) {
        let entry_ty = self.ctx.basic_block_ty(self.local_def_id, mir::START_BLOCK);
        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry before");
        let mut expected = expected.ty.as_function().cloned().unwrap();
        self.elaborate_mut_params(&mut expected);

        let entry_ty = self.elaborate_unused_args(&entry_ty, &expected);

        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry after");
        self.ctx.relate_sub_type(&entry_ty.into(), &expected.into());
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(ctx: &'ctx mut analyze::Analyzer<'tcx>, local_def_id: LocalDefId) -> Self {
        let tcx = ctx.tcx;
        let body = tcx.optimized_mir(local_def_id.to_def_id());
        let drop_points = Default::default();
        Self {
            ctx,
            tcx,
            local_def_id,
            body,
            drop_points,
        }
    }

    pub fn run(&mut self, expected: &rty::RefinedType) {
        self.refine_basic_blocks();
        self.analyze_basic_blocks();
        self.assert_entry(expected);
    }
}
