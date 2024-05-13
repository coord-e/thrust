use rustc_index::IndexVec;
use rustc_middle::mir::BasicBlock;

use crate::pretty::PrettyDisplayExt as _;

use super::{BasicBlockType, RefineBasicBlockCtxt, RefineCtxt};

#[derive(Debug)]
pub struct RefineBodyCtxt<'rcx> {
    rcx: &'rcx mut RefineCtxt,
    // TODO: consider interface and remove option here?
    basic_blocks: IndexVec<BasicBlock, Option<BasicBlockType>>,
}

impl<'rcx> RefineBodyCtxt<'rcx> {
    pub fn new(rcx: &'rcx mut RefineCtxt) -> Self {
        let basic_blocks = Default::default();
        Self { rcx, basic_blocks }
    }

    pub fn rcx(&self) -> &RefineCtxt {
        self.rcx
    }

    pub fn rcx_mut(&mut self) -> &mut RefineCtxt {
        self.rcx
    }

    pub fn basic_block_ctxt(&mut self) -> RefineBasicBlockCtxt<'rcx, '_> {
        RefineBasicBlockCtxt::new(self)
    }

    pub fn basic_block_ty(&self, bb: BasicBlock) -> &BasicBlockType {
        &self.basic_blocks.get(bb).unwrap().as_ref().unwrap()
    }

    pub fn register_basic_block(&mut self, bb: BasicBlock, ty: BasicBlockType) {
        tracing::debug!(bb = ?bb, ty = %ty.display(), "register_basic_block");
        self.basic_blocks.insert(bb, ty);
    }
}
