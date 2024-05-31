#![feature(rustc_private)]

extern crate rustc_ast;
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

// TODO: so where should the elaboration happens?
// currently they resides in refine and analyze...
// maybe we should add a layer to implement relatively pure type system logic with MIR primitives

// pure logic
mod annot;
mod chc;
mod rty;

// utility
mod index;
mod pretty;

// ?
mod error;

pub use analyze::Analyzer;
