#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;

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

pub use analyze::Analyzer;
