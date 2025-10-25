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
pub use env::{Assumption, Env, PlaceType, PlaceTypeBuilder, PlaceTypeVar, TempVarIdx, Var};

use crate::chc::DatatypeSymbol;
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

pub fn datatype_symbol(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> DatatypeSymbol {
    DatatypeSymbol::new(tcx.def_path_str(did).replace("::", "."))
}
