/// hopv/hoice#73
use std::collections::{HashMap, HashSet};

use crate::chc;

struct SortDatatypes<'a> {
    defs: &'a [chc::Datatype],

    visited: HashSet<chc::DatatypeSymbol>,
    result: Vec<chc::DatatypeSymbol>,
}

fn symbol_references(ty: &chc::Datatype) -> Vec<chc::DatatypeSymbol> {
    let mut res = Vec::new();
    for ctor in &ty.ctors {
        for selector in &ctor.selectors {
            selector.sort.walk(|s| {
                // TODO: stop using format_context::Sort directly
                res.push(chc::format_context::Sort::new(s).to_symbol());
            });
        }
    }
    res
}

impl<'a> SortDatatypes<'a> {
    pub fn new(defs: &'a [chc::Datatype]) -> Self {
        Self {
            defs,
            visited: Default::default(),
            result: Default::default(),
        }
    }

    fn sorted(mut self) -> Vec<chc::DatatypeSymbol> {
        for ty in self.defs {
            self.sort_visit(&ty);
        }
        self.result
    }

    fn sort_visit(&mut self, ty: &chc::Datatype) {
        if self.visited.contains(&ty.symbol) {
            return;
        }
        self.visited.insert(ty.symbol.clone());
        for sym in symbol_references(ty) {
            if let Some(referred_ty) = self.defs.iter().find(|t| t.symbol == sym) {
                self.sort_visit(referred_ty);
            }
        }
        self.result.push(ty.symbol.clone());
    }
}

#[derive(Debug, Clone, Default)]
pub struct HoiceDatatypeRenamer {
    prefixes: HashMap<chc::DatatypeSymbol, String>,
}

impl HoiceDatatypeRenamer {
    pub fn new(tys: &[chc::Datatype]) -> Self {
        let sorted = SortDatatypes::new(tys).sorted();
        let prefixes = ('A'..='Z')
            .chain('a'..='z')
            .flat_map(|p| ('0'..='9').map(move |c| format!("{}{}", p, c)));
        let prefixes = sorted.into_iter().zip(prefixes).collect();
        HoiceDatatypeRenamer { prefixes }
    }

    pub fn rename(&self, sym: &chc::DatatypeSymbol) -> chc::DatatypeSymbol {
        if let Some(prefix) = self.prefixes.get(sym) {
            chc::DatatypeSymbol::new(format!("{}_{}", prefix, sym))
        } else {
            sym.clone()
        }
    }
}
