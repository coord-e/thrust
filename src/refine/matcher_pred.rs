// matcher_pred is a predicate variable p with the following implications:
// p(v1, v2, ..., vn, x) <= x = V1(v1)
// p(v1, v2, ..., vn, x) <= x = V2(v2)
// ...
// p(v1, v2, ..., vn, x) <= x = Vn(vn)

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_index::IndexVec;
use rustc_span::def_id::DefId;

use crate::chc;
use crate::pretty::{PrettyDisplayExt as _, PrettySliceExt as _};
use crate::rty;

#[derive(Debug, Clone)]
pub struct MatcherPredCache {
    matcher_preds: HashMap<chc::DatatypeSymbol, HashMap<Vec<chc::Sort>, chc::PredVarId>>,
    system: Rc<RefCell<chc::System>>,
    datatypes: Rc<RefCell<HashMap<DefId, rty::EnumDatatypeDef>>>,
}

impl MatcherPredCache {
    pub fn new(
        system: Rc<RefCell<chc::System>>,
        datatypes: Rc<RefCell<HashMap<DefId, rty::EnumDatatypeDef>>>,
    ) -> Self {
        Self {
            matcher_preds: Default::default(),
            system,
            datatypes,
        }
    }

    pub fn get_or_create(
        &mut self,
        symbol: &chc::DatatypeSymbol,
        args: &[chc::Sort],
    ) -> chc::PredVarId {
        if let Some(pred) = self.matcher_preds.get(symbol).and_then(|m| m.get(args)) {
            return *pred;
        }
        let matcher_pred = self.create(symbol, args);
        self.matcher_preds
            .entry(symbol.clone())
            .or_default()
            .insert(args.to_owned(), matcher_pred);
        matcher_pred
    }

    #[tracing::instrument(name = "matcher_pred", skip(self), fields(symbol = %symbol, args = %args.pretty_slice().display()))]
    fn create(&self, symbol: &chc::DatatypeSymbol, args: &[chc::Sort]) -> chc::PredVarId {
        let def = self
            .datatypes
            .borrow()
            .values()
            .find(|def| &def.name == symbol)
            .unwrap()
            .clone();
        let mut matcher_pred_sig: chc::PredSig = def
            .field_tys()
            .map(|ty| {
                let mut sort = ty.to_sort();
                sort.instantiate_params(args);
                sort
            })
            .collect();
        matcher_pred_sig.push(chc::Sort::datatype(def.name.clone(), args.to_vec()));
        let matcher_pred = self.system.borrow_mut().new_pred_var(
            matcher_pred_sig.clone(),
            chc::DebugInfo::from_current_span(),
        );

        let vars = IndexVec::<chc::TermVarIdx, _>::from_raw(matcher_pred_sig);
        let data_var: chc::TermVarIdx = (vars.len() - 1).into();
        let head = chc::Atom::new(
            matcher_pred.into(),
            vars.indices().map(chc::Term::var).collect(),
        );
        let mut offset = 0;
        for variant in &def.variants {
            let ctor_args = (0..variant.field_tys.len())
                .into_iter()
                .map(|i| chc::Term::var((i + offset).into()))
                .collect();
            offset += variant.field_tys.len();
            let ctor_term = chc::Term::datatype_ctor(
                def.name.clone(),
                args.to_vec(),
                variant.name.clone(),
                ctor_args,
            );
            let body = chc::Term::var(data_var).equal_to(ctor_term);
            let clause = chc::Clause {
                vars: vars.clone(),
                head: head.clone(),
                body: vec![body],
                debug_info: chc::DebugInfo::from_current_span(),
            };
            self.system.borrow_mut().push_clause(clause);
        }

        matcher_pred
    }
}
