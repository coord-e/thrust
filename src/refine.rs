mod template;
pub use template::{TemplateScope, TemplateTypeGenerator, UnrefinedTypeGenerator};

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
