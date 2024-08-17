use std::collections::HashMap;

use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, LocalDefId};

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::BasicBlockType;
use crate::rty::{self, ClauseBuilderExt as _};

mod annot;
mod basic_block;
mod crate_;
mod did_cache;
mod local_def;

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Collection of refined known def types.
    ///
    /// currently contains only local-def templates,
    /// but will be extended to contain externally known def's refinement types
    /// (at least for every defs referenced by local def bodies)
    defs: HashMap<DefId, rty::RefinedType>,

    /// Resulting CHC system.
    system: chc::System,

    basic_blocks: HashMap<LocalDefId, HashMap<BasicBlock, BasicBlockType>>,
    def_ids: did_cache::DefIdCache<'tcx>,
}

impl<'tcx> crate::refine::PredVarGenerator for Analyzer<'tcx> {
    fn generate_pred_var(&mut self, pred_sig: chc::PredSig) -> chc::PredVarId {
        self.system.new_pred_var(pred_sig)
    }
}

impl<'tcx> Analyzer<'tcx> {
    fn implied_atom<FV, F>(&mut self, atoms: Vec<chc::Atom<FV>>, mut fv_sort: F) -> chc::Atom<FV>
    where
        F: FnMut(FV) -> chc::Sort,
        FV: std::hash::Hash + Eq + Clone + std::fmt::Debug + 'static,
    {
        let fvs: Vec<_> = atoms.iter().flat_map(|a| a.fv()).cloned().collect();
        let mut builder = chc::ClauseBuilder::default();
        let mut pred_sig = chc::PredSig::new();
        for fv in &fvs {
            let sort = fv_sort(fv.clone());
            builder.add_mapped_var(fv.clone(), sort.clone());
            pred_sig.push(sort);
        }
        for atom in atoms {
            builder.add_body_mapped(atom);
        }
        let pv = self.system.new_pred_var(pred_sig);
        let head = chc::Atom::new(pv.into(), fvs.into_iter().map(chc::Term::var).collect());
        let clause = builder.head_mapped(head.clone());
        self.add_clause(clause);
        head
    }

    fn relate_sub_type(&mut self, got: &rty::Type, expected: &rty::Type) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "sub_type");

        match (got, expected) {
            (rty::Type::Int, rty::Type::Int)
            | (rty::Type::Bool, rty::Type::Bool)
            | (rty::Type::String, rty::Type::String)
            | (rty::Type::Never, rty::Type::Never) => {}
            (rty::Type::Tuple(got), rty::Type::Tuple(expected))
                if got.elems.len() == expected.elems.len() =>
            {
                for (got_ty, expected_ty) in got.elems.iter().zip(expected.elems.iter()) {
                    self.relate_sub_type(got_ty, expected_ty);
                }
            }
            (rty::Type::Pointer(got), rty::Type::Pointer(expected))
                if got.kind == expected.kind =>
            {
                match got.kind {
                    rty::PointerKind::Own | rty::PointerKind::Ref(rty::RefKind::Immut) => {
                        self.relate_sub_type(&got.elem, &expected.elem);
                    }
                    rty::PointerKind::Ref(rty::RefKind::Mut) => {
                        self.relate_equal_type(&got.elem, &expected.elem);
                    }
                }
            }
            (rty::Type::Function(got), rty::Type::Function(expected)) => {
                // TODO: check sty and length is equal
                // TODO: add value_var dependency
                let mut builder = chc::ClauseBuilder::default();
                for (param_idx, param_rty) in got.params.iter_enumerated() {
                    builder.add_mapped_var(param_idx, param_rty.ty.to_sort());
                }
                for (got_ty, expected_ty) in got.params.iter().zip(expected.params.clone()) {
                    let clause = builder
                        .clone()
                        .with_value_var(&got_ty.ty)
                        .add_body(expected_ty.refinement)
                        .head(got_ty.refinement.clone());
                    self.add_clause(clause);
                    self.relate_sub_type(&expected_ty.ty, &got_ty.ty);
                }
                let clause = builder
                    .with_value_var(&got.ret.ty)
                    .add_body(got.ret.refinement.clone())
                    .head(expected.ret.refinement.clone());
                self.add_clause(clause);
                self.relate_sub_type(&got.ret.ty, &expected.ret.ty);
            }
            _ => panic!(
                "inconsistent types: got={}, expected={}",
                got.display(),
                expected.display()
            ),
        }
    }

    fn relate_equal_type(&mut self, got: &rty::Type, expected: &rty::Type) {
        tracing::debug!(got = %got.display(), expected = %expected.display(), "equal_type");

        self.relate_sub_type(got, expected);
        self.relate_sub_type(expected, got);
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let defs = Default::default();
        let system = Default::default();
        let basic_blocks = Default::default();
        Self {
            tcx,
            defs,
            system,
            basic_blocks,
            def_ids: did_cache::DefIdCache::new(tcx),
        }
    }

    pub fn add_clause(&mut self, clause: chc::Clause) {
        tracing::debug!(clause = %clause.display(), id = ?self.system.clauses.next_index(), "add_clause");
        self.system.clauses.push(clause);
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        tracing::debug!(def_id = ?def_id, rty = %rty.display(), "register_def");
        self.defs.insert(def_id, rty);
    }

    pub fn def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.defs.get(&def_id)
    }

    pub fn register_basic_block_ty(
        &mut self,
        def_id: LocalDefId,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        tracing::debug!(def_id = ?def_id, ?bb, rty = %rty.display(), "register_basic_block_ty");
        self.basic_blocks.entry(def_id).or_default().insert(bb, rty);
    }

    pub fn basic_block_ty(&self, def_id: LocalDefId, bb: BasicBlock) -> &BasicBlockType {
        &self.basic_blocks[&def_id][&bb]
    }

    pub fn register_well_known_defs(&mut self) {
        let panic_ty = {
            let param = rty::RefinedType::new(
                rty::PointerType::immut_to(rty::Type::string()).into(),
                rty::Refinement::bottom(),
            );
            let ret = rty::RefinedType::new(rty::Type::never(), rty::Refinement::bottom());
            rty::FunctionType::new([param.vacuous()].into_iter().collect(), ret)
        };
        let panic_def_id = self.tcx.require_lang_item(LangItem::Panic, None);
        self.register_def(panic_def_id, rty::RefinedType::unrefined(panic_ty.into()));
    }

    pub fn crate_analyzer(&mut self) -> crate_::Analyzer<'tcx, '_> {
        crate_::Analyzer::new(self)
    }

    pub fn local_def_analyzer(
        &mut self,
        local_def_id: LocalDefId,
    ) -> local_def::Analyzer<'tcx, '_> {
        local_def::Analyzer::new(self, local_def_id)
    }

    pub fn basic_block_analyzer(
        &mut self,
        local_def_id: LocalDefId,
        bb: BasicBlock,
    ) -> basic_block::Analyzer<'tcx, '_> {
        basic_block::Analyzer::new(self, local_def_id, bb)
    }

    pub fn solve(&mut self) {
        if let Err(err) = self.system.solve() {
            self.tcx.dcx().err(format!("verification error: {:?}", err));
        }
    }
}
