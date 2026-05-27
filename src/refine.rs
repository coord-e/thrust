//! Core logic of refinement typing.
//!
//! This module includes the definition of the refinement typing environment and the template
//! type generation from MIR types.
//!
//! This module is used by the [`crate::analyze`] module. There is currently no clear boundary between
//! the `analyze` and `refine` modules, so it is a TODO to integrate this into the `analyze`
//! module and remove this one.

mod template;
pub use template::{TemplateRegistry, TemplateScope, TypeBuilder};

mod basic_block;
pub use basic_block::BasicBlockType;

mod env;
pub use env::{
    Assumption, EnumDefProvider, Env, PlaceType, PlaceTypeBuilder, PlaceTypeVar, TempVarIdx, Var,
};

use crate::chc::{DatatypeSymbol, ForallPred, UserDefinedPred};
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

fn stable_def_id_symbol(tcx: mir_ty::TyCtxt<'_>, did: DefId, prefix: &str) -> String {
    let hash = tcx.def_path_hash(did);
    let path = tcx.def_path(did);
    if let Some(name) = path.data.last().and_then(|d| d.data.get_opt_name()) {
        tracing::debug!("stable_def_id_symbol: name={}", name);
        format!("{}_{}_{}", prefix, name, hash.0.to_hex())
    } else {
        hash.0.to_hex()
    }
}

pub fn datatype_symbol(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> DatatypeSymbol {
    DatatypeSymbol::new(tcx.def_path_str(did).replace("::", "."))
}

pub fn user_defined_pred(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> UserDefinedPred {
    UserDefinedPred::new(stable_def_id_symbol(tcx, did, "p"))
}

pub fn forall_pred(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> ForallPred {
    ForallPred::new(stable_def_id_symbol(tcx, did, "q"))
}
