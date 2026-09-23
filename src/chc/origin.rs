use rustc_index::IndexVec;

use super::TermVarIdx;

#[derive(Debug, Clone)]
pub enum VarOrigin {
    Mapped(String),
    Value,
    Existential {
        variable: String,
        refinement: RefinementSource,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefinementSource {
    Environment(String),
    Assumption(usize),
    Body(usize),
}

#[derive(Debug, Clone)]
pub struct EnvironmentBinding {
    pub variable: String,
    pub refined_type: String,
}

#[derive(Debug, Clone)]
pub struct RefinementOrigin {
    pub formula: String,
    pub value_var: Option<TermVarIdx>,
}

#[derive(Debug, Clone, Default)]
pub struct ClauseOrigin {
    pub vars: IndexVec<TermVarIdx, VarOrigin>,
    pub environment: Vec<EnvironmentBinding>,
    pub assumptions: Vec<String>,
    pub body: Vec<RefinementOrigin>,
    pub head: Option<RefinementOrigin>,
}
