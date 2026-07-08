#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
#[cfg(test)]
extern crate rustc_driver;
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
mod chc;
mod rty;

// utility
mod pretty;

pub use analyze::mir_borrowck_skip_formula_fn;
pub use analyze::Analyzer;
