//! A set of utilities for pretty-printing various data structures.
//!
//! It uses the [`pretty`] crate to provide a flexible and configurable way to format complex
//! data structures for display. The main entry point is the [`PrettyDisplayExt`] trait,
//! which provides a [`PrettyDisplayExt::display`] method that returns a [`Display`] object to
//! turn [`Pretty`] values into [`std::fmt::Display`] that can be used with standard formatting macros.
//!
//! This is primarily used for debugging and logging purposes, to make the output of the tool
//! more readable.

use rustc_index::{IndexSlice, IndexVec};

use pretty::{termcolor, BuildDoc, DocAllocator, DocPtr, Pretty};

/// A wrapper around a [`crate::rty::FunctionType`] that provides a [`Pretty`] implementation.
pub struct FunctionType<'a, FV> {
    pub params:
        &'a rustc_index::IndexVec<crate::rty::FunctionParamIdx, crate::rty::RefinedType<FV>>,
    pub ret: &'a crate::rty::RefinedType<FV>,
}

impl<'a, 'b, 'c, D, FV> Pretty<'a, D, termcolor::ColorSpec> for &'b FunctionType<'c, FV>
where
    FV: crate::chc::Var,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        allocator
            .intersperse(self.params.iter().map(|ty| ty.pretty(allocator)), separator)
            .parens()
            .append(allocator.space())
            .append(allocator.text("→"))
            .append(allocator.line())
            .append(self.ret.pretty(allocator))
            .group()
    }
}

impl<'a, FV> FunctionType<'a, FV> {
    pub fn new(
        params: &'a IndexVec<crate::rty::FunctionParamIdx, crate::rty::RefinedType<FV>>,
        ret: &'a crate::rty::RefinedType<FV>,
    ) -> FunctionType<'a, FV> {
        FunctionType { params, ret }
    }
}

/// A wrapper around a slice that provides a [`Pretty`] implementation.
#[derive(Debug, Clone)]
pub struct PrettySlice<'a, T> {
    slice: &'a [T],
}

impl<'a, 'b, 'c, D, T> Pretty<'a, D, termcolor::ColorSpec> for &'c PrettySlice<'b, T>
where
    &'b T: Pretty<'a, D, termcolor::ColorSpec>,
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        allocator
            .intersperse(self.slice.iter().map(|ty| ty.pretty(allocator)), separator)
            .group()
            .brackets()
    }
}

// useful for debugging
#[allow(dead_code)]
pub trait PrettySliceExt {
    type Item;
    fn pretty_slice(&self) -> PrettySlice<Self::Item>;
}

impl<T> PrettySliceExt for [T] {
    type Item = T;
    fn pretty_slice(&self) -> PrettySlice<T> {
        PrettySlice { slice: self }
    }
}

impl<T> PrettySliceExt for Vec<T> {
    type Item = T;
    fn pretty_slice(&self) -> PrettySlice<T> {
        PrettySlice {
            slice: self.as_slice(),
        }
    }
}

impl<I: rustc_index::Idx, T> PrettySliceExt for IndexSlice<I, T> {
    type Item = T;
    fn pretty_slice(&self) -> PrettySlice<T> {
        PrettySlice { slice: &self.raw }
    }
}

impl<I: rustc_index::Idx, T> PrettySliceExt for IndexVec<I, T> {
    type Item = T;
    fn pretty_slice(&self) -> PrettySlice<T> {
        PrettySlice {
            slice: self.raw.as_slice(),
        }
    }
}

/// A wrapper around a type that provides a [`std::fmt::Display`] implementation via [`Pretty`].
#[derive(Debug, Clone)]
pub struct Display<'a, T> {
    value: &'a T,
    width: usize,
}

impl<'a, T> std::fmt::Display for Display<'a, T>
where
    &'a T: for<'b> Pretty<'b, pretty::Arena<'b, termcolor::ColorSpec>, termcolor::ColorSpec>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.to_doc(&pretty::Arena::new()).render_fmt(self.width, f)
    }
}

pub trait PrettyDisplayExt: Sized {
    fn display(&self) -> Display<Self>;
}

impl<P> PrettyDisplayExt for P
where
    for<'a, 'b> &'b P: Pretty<'a, pretty::Arena<'a, termcolor::ColorSpec>, termcolor::ColorSpec>,
{
    fn display(&self) -> Display<Self> {
        Display::new(self)
    }
}

const DEFAULT_WIDTH: usize = 150;

#[allow(dead_code)]
impl<'a, T> Display<'a, T> {
    fn new(value: &'a T) -> Self {
        Display {
            value,
            width: DEFAULT_WIDTH,
        }
    }

    fn to_doc<'b, D>(&self, alloc: &'b D) -> BuildDoc<'b, D::Doc, termcolor::ColorSpec>
    where
        &'a T: Pretty<'b, D, termcolor::ColorSpec>,
        D: DocAllocator<'b, termcolor::ColorSpec>,
        D::Doc: DocPtr<'b, termcolor::ColorSpec> + Clone,
    {
        self.value.pretty(alloc).1
    }

    fn to_doc_newline<'b, D>(&self, alloc: &'b D) -> BuildDoc<'b, D::Doc, termcolor::ColorSpec>
    where
        &'a T: Pretty<'b, D, termcolor::ColorSpec>,
        D: DocAllocator<'b, termcolor::ColorSpec>,
        D::Doc: DocPtr<'b, termcolor::ColorSpec> + Clone,
    {
        self.value.pretty(alloc).append(alloc.hardline()).1
    }

    pub fn render<W>(&self, writer: W) -> std::io::Result<()>
    where
        &'a T: for<'b> Pretty<'b, pretty::Arena<'b, termcolor::ColorSpec>, termcolor::ColorSpec>,
        W: termcolor::WriteColor,
    {
        let width = self.width;
        self.to_doc_newline(&pretty::Arena::new())
            .render_colored(width, writer)
    }

    pub fn render_stdout(&self) -> std::io::Result<()>
    where
        &'a T: for<'b> Pretty<'b, pretty::Arena<'b, termcolor::ColorSpec>, termcolor::ColorSpec>,
    {
        self.render(termcolor::StandardStream::stdout(
            termcolor::ColorChoice::Auto,
        ))
    }

    pub fn width(&mut self, width: usize) -> &mut Self {
        self.width = width;
        self
    }
}
