use std::fmt;

use crate::chc::{Sort, TermVarIdx, Var};
use crate::pretty::PrettyDisplayExt;
use crate::rty::{self, ExistentialVarIdx};

#[derive(Debug, Clone)]
pub struct ClauseOrigin {
    pub environment: Vec<Entry>,
    pub body: Vec<Entry>,
    pub head: Entry,
}

#[derive(Debug, Clone)]
pub struct Entry {
    text: String,
    mappings: Vec<VarMapping>,
}

#[derive(Debug, Clone)]
pub struct VarMapping {
    source: String,
    chc_var: TermVarIdx,
}

impl Entry {
    pub fn binding<V: Var, T: Var>(variable: V, ty: &rty::RefinedType<T>) -> Self {
        Self {
            text: format!("{variable:?}: {}", ty.display()),
            mappings: Vec::new(),
        }
    }

    pub fn parameter<V: Var>(variable: V, sort: &Sort) -> Self {
        Self {
            text: format!("{variable:?}: {}", sort.display()),
            mappings: Vec::new(),
        }
    }

    pub fn assumption<V: Var>(formula: &rty::Formula<V>) -> Self {
        Self {
            text: format!("_: {{ {} }}", formula.display()),
            mappings: Vec::new(),
        }
    }

    pub fn refinement<V: Var>(refinement: &rty::Refinement<V>) -> Self {
        Self {
            text: refinement.display().to_string(),
            mappings: Vec::new(),
        }
    }

    pub fn var_mapping<V: Var>(mut self, variable: V, chc_var: TermVarIdx) -> Self {
        self.mappings.push(VarMapping {
            source: format!("{variable:?}"),
            chc_var,
        });
        self
    }

    pub fn add_var_mapping<V: Var>(&mut self, variable: V, chc_var: TermVarIdx) {
        self.mappings.push(VarMapping {
            source: format!("{variable:?}"),
            chc_var,
        });
    }

    pub fn value_var_mapping(mut self, chc_var: TermVarIdx) -> Self {
        self.mappings.push(VarMapping {
            source: "ν".to_owned(),
            chc_var,
        });
        self
    }

    pub fn add_value_var_mapping(&mut self, chc_var: TermVarIdx) {
        self.mappings.push(VarMapping {
            source: "ν".to_owned(),
            chc_var,
        });
    }

    pub fn existential_var_mapping(
        mut self,
        variable: ExistentialVarIdx,
        chc_var: TermVarIdx,
    ) -> Self {
        self.mappings.push(VarMapping {
            source: variable.to_string(),
            chc_var,
        });
        self
    }

    pub fn add_existential_var_mapping(
        &mut self,
        variable: ExistentialVarIdx,
        chc_var: TermVarIdx,
    ) {
        self.mappings.push(VarMapping {
            source: variable.to_string(),
            chc_var,
        });
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn mappings(&self) -> &[VarMapping] {
        &self.mappings
    }
}

impl fmt::Display for VarMapping {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.source, self.chc_var)
    }
}
