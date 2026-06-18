#![feature(rustc_private)]

// Linking `rustc_driver` pulls in the rustc dylib closure (codegen, etc.) so the
// lib unit-test harness can link. It is only needed for `cargo test`; production
// builds get this from the `thrust-rustc` binary instead.
#[cfg(test)]
extern crate rustc_driver;

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_target;

// works with MIR
mod analyze;

// TODO: remove refine module
mod refine;

// pure logic
mod annot;
mod chc;
mod rty;

// utility
mod pretty;

pub use analyze::mir_borrowck_skip_formula_fn;
pub use analyze::Analyzer;
