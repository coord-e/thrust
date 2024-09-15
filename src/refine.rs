mod template;
pub use template::{PredVarGenerator, TemplateTypeGenerator};

mod basic_block;
pub use basic_block::BasicBlockType;

mod env;
pub use env::{Env, PlaceType, TempVarIdx, UnboundAssumption, Var};

use crate::chc::DatatypeSymbol;
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

pub fn datatype_symbol<'tcx>(tcx: mir_ty::TyCtxt<'tcx>, did: DefId) -> DatatypeSymbol {
    DatatypeSymbol::new(tcx.def_path_str(did))
}
