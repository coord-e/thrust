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
pub use basic_block::{BasicBlockType, BasicBlockTypeParamKind};

mod env;
pub use env::{
    Assumption, EnumDefProvider, Env, PlaceType, PlaceTypeBuilder, PlaceTypeVar, TempVarIdx, Var,
};

use crate::chc::{DatatypeSymbol, UserDefinedPred};
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

fn stable_def_id_symbol(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> String {
    let hash = tcx.def_path_hash(did);
    let path = tcx.def_path(did);
    if let Some(name) = path.data.last().and_then(|d| d.data.get_opt_name()) {
        format!("{}_{}", name, hash.0.to_hex())
    } else {
        hash.0.to_hex()
    }
}

pub fn datatype_symbol(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> DatatypeSymbol {
    DatatypeSymbol::new(tcx.def_path_str(did).replace("::", "."))
}

/// The parameters of a `thrust_models::model::BitVec<WIDTH, SIGNED>` type.
#[derive(Debug, Clone, Copy)]
pub struct BitVecModel {
    pub width: u32,
    pub signed: bool,
}

impl BitVecModel {
    pub fn new<'tcx>(tcx: mir_ty::TyCtxt<'tcx>, args: mir_ty::GenericArgsRef<'tcx>) -> Self {
        let width = args
            .const_at(0)
            .try_to_target_usize(tcx)
            .expect("BitVec width must be a known constant");
        let signed = args
            .const_at(1)
            .try_to_value()
            .and_then(|value| value.try_to_bool())
            .expect("BitVec signedness must be a known constant");
        BitVecModel {
            width: width.try_into().unwrap(),
            signed,
        }
    }
}

pub fn user_defined_pred(tcx: mir_ty::TyCtxt<'_>, did: DefId) -> UserDefinedPred {
    UserDefinedPred::new(stable_def_id_symbol(tcx, did))
}
