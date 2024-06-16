use std::collections::HashMap;

use rustc_middle::mir::Local;
use rustc_span::def_id::DefId;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::rty;

mod template;
pub use template::{PredVarGenerator, TemplateTypeGenerator};

mod basic_block;
pub use basic_block::BasicBlockType;

mod env;
pub use env::{Env, TempVarIdx, Var};

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

#[derive(Debug, Clone, Default)]
pub struct RefineCtxt {
    /// Collection of refined known def types.
    defs: HashMap<DefId, rty::RefinedType>,

    /// Resulting CHC system.
    system: chc::System,
}

impl PredVarGenerator for RefineCtxt {
    fn generate_pred_var(&mut self, pred_sig: chc::PredSig) -> chc::PredVarId {
        self.system.new_pred_var(pred_sig)
    }
}

impl RefineCtxt {
    pub fn system(&self) -> &chc::System {
        &self.system
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

    pub fn solve(&mut self) -> Result<(), chc::CheckSatError> {
        self.system.solve()
    }
}
