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
    mappings: Vec<VariableMapping>,
}

#[derive(Debug, Clone)]
pub struct VariableMapping {
    source: String,
    target: TermVarIdx,
}

impl Entry {
    pub fn binding<V: Var, T: Var>(
        variable: V,
        ty: &rty::RefinedType<T>,
        target: Option<TermVarIdx>,
    ) -> Self {
        let mut entry = Self {
            text: format!("{variable:?}: {}", ty.display()),
            mappings: Vec::new(),
        };
        if let Some(target) = target {
            entry.mappings.push(VariableMapping {
                source: format!("{variable:?}"),
                target,
            });
        }
        entry
    }

    pub fn parameter<V: Var>(variable: V, sort: &Sort, target: TermVarIdx) -> Self {
        Self {
            text: format!("{variable:?}: {}", sort.display()),
            mappings: vec![VariableMapping {
                source: format!("{variable:?}"),
                target,
            }],
        }
    }

    pub fn assumption<V: Var>(formula: &rty::Formula<V>) -> Self {
        Self {
            text: format!("_: {{ {} }}", formula.display()),
            mappings: Vec::new(),
        }
    }

    pub fn refinement<V: Var>(
        refinement: &rty::Refinement<V>,
        value_var: Option<TermVarIdx>,
    ) -> Self {
        let mut entry = Self {
            text: refinement.display().to_string(),
            mappings: Vec::new(),
        };
        if let Some(target) = value_var {
            entry.mappings.push(VariableMapping {
                source: "ν".to_owned(),
                target,
            });
        }
        entry
    }

    pub fn map_existential(&mut self, variable: ExistentialVarIdx, target: TermVarIdx) {
        self.mappings.push(VariableMapping {
            source: variable.to_string(),
            target,
        });
    }

    pub fn mappings(&self) -> &[VariableMapping] {
        &self.mappings
    }
}

impl fmt::Display for Entry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.text)
    }
}

impl fmt::Display for VariableMapping {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.source, self.target)
    }
}
