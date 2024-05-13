#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;

// works with MIR
mod analyze;

// interface (inspect MIR without TyCtxt)
// all logics that works provided all knowledge of MIR
mod refine;

// pure logic
mod chc;
mod rty;

// utility
mod index;
mod pretty;

// ?
mod error;

pub use analyze::Analyzer;
