use std::io::Write as _;
use std::sync::Mutex;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{BasicBlock, Body, Operand, Rvalue, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::Spanned;

use super::{lang_item_method, reconstruct};

type MirInspector = dyn for<'tcx> FnOnce(TyCtxt<'tcx>, Body<'tcx>) + Send;

struct TestCallbacks {
    function_name: &'static str,
    inspect: Option<Box<MirInspector>>,
}

impl Callbacks for TestCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let local_def_id = tcx
            .mir_keys(())
            .iter()
            .copied()
            .filter(|local_def_id| tcx.def_kind(*local_def_id).is_fn_like())
            .find(|local_def_id| {
                tcx.item_name(local_def_id.to_def_id()).as_str() == self.function_name
            })
            .unwrap_or_else(|| panic!("function `{}` was not compiled", self.function_name));
        let body = tcx.optimized_mir(local_def_id.to_def_id()).clone();
        let inspect = self
            .inspect
            .take()
            .expect("MIR inspector was already called");
        inspect(tcx, body);
        Compilation::Stop
    }
}

fn with_optimized_mir(
    source: &str,
    function_name: &'static str,
    inspect: impl for<'tcx> FnOnce(TyCtxt<'tcx>, Body<'tcx>) + Send + 'static,
) {
    // rustc_driver installs process-global compiler state, so do not run embedded compilers in
    // parallel when the test harness executes these focused tests on different worker threads.
    static RUSTC_DRIVER: Mutex<()> = Mutex::new(());
    let _guard = RUSTC_DRIVER
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    let mut input = tempfile::Builder::new().suffix(".rs").tempfile().unwrap();
    input.write_all(source.as_bytes()).unwrap();
    let args = [
        "rustc".to_owned(),
        input.path().display().to_string(),
        "--crate-name=reconstruct_slice_indexing_test".to_owned(),
        "--crate-type=lib".to_owned(),
        "--edition=2021".to_owned(),
        "-Cdebug-assertions=off".to_owned(),
    ];
    let mut callbacks = TestCallbacks {
        function_name,
        inspect: Some(Box::new(inspect)),
    };
    rustc_driver::run_compiler(&args, &mut callbacks);
}

struct ReconstructedCall<'a, 'tcx> {
    block: BasicBlock,
    args: &'a [Spanned<Operand<'tcx>>],
}

fn find_call<'a, 'tcx>(
    body: &'a Body<'tcx>,
    def_id: rustc_span::def_id::DefId,
) -> ReconstructedCall<'a, 'tcx> {
    let mut calls = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                return None;
            };
            func.const_fn_def()
                .is_some_and(|(called, _)| called == def_id)
                .then_some(ReconstructedCall { block, args })
        });
    let call = calls.next().expect("expected reconstructed call");
    assert!(
        calls.next().is_none(),
        "expected exactly one reconstructed call"
    );
    call
}

#[test]
fn reconstructs_shared_slice_indexing() {
    with_optimized_mir(
        "pub fn test(slice: &[i32], index: usize) -> i32 { slice[index] }",
        "test",
        |tcx, mut body| {
            let (receiver, index) = {
                let mut params = body.args_iter();
                (params.next().unwrap(), params.next().unwrap())
            };
            reconstruct(tcx, &mut body);
            let index_method = lang_item_method(
                tcx,
                rustc_hir::lang_items::LangItem::Index,
                rustc_span::sym::index,
            );
            let call = find_call(&body, index_method);
            assert_eq!(call.args.len(), 2);
            assert_eq!(call.args[0].node, Operand::Copy(receiver.into()));
            assert_eq!(call.args[1].node, Operand::Copy(index.into()));
        },
    );
}

#[test]
fn reconstructs_mutable_slice_indexing() {
    with_optimized_mir(
        "pub fn test(slice: &mut [i32], index: usize) -> i32 { slice[index] += 1; slice[index] }",
        "test",
        |tcx, mut body| {
            let (receiver, index) = {
                let mut params = body.args_iter();
                (params.next().unwrap(), params.next().unwrap())
            };
            reconstruct(tcx, &mut body);
            let index_mut = lang_item_method(
                tcx,
                rustc_hir::lang_items::LangItem::IndexMut,
                rustc_span::sym::index_mut,
            );
            let index_method = lang_item_method(
                tcx,
                rustc_hir::lang_items::LangItem::Index,
                rustc_span::sym::index,
            );
            let mutable_call = find_call(&body, index_mut);
            assert_eq!(mutable_call.args.len(), 2);
            assert_eq!(mutable_call.args[0].node, Operand::Move(receiver.into()));
            assert_eq!(mutable_call.args[1].node, Operand::Copy(index.into()));

            let shared_call = find_call(&body, index_method);
            assert_eq!(shared_call.args.len(), 2);
            let Operand::Copy(shared_receiver) = &shared_call.args[0].node else {
                panic!("shared indexing receiver must be copied");
            };
            assert!(shared_receiver.projection.is_empty());
            assert_eq!(shared_call.args[1].node, Operand::Copy(index.into()));
            let (_, reborrow) = body.basic_blocks[shared_call.block]
                .statements
                .iter()
                .filter_map(|statement| statement.kind.as_assign())
                .find(|(place, _)| place.local == shared_receiver.local)
                .expect("shared receiver reborrow was not inserted");
            assert!(matches!(
                reborrow,
                Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, referent)
                    if *referent == tcx.mk_place_deref(receiver.into())
            ));
        },
    );
}

#[test]
fn reconstructs_shared_indexing_through_mutable_slice() {
    with_optimized_mir(
        "pub fn test(slice: &mut [i32], index: usize) -> i32 { slice[index] }",
        "test",
        |tcx, mut body| {
            let (receiver, index) = {
                let mut params = body.args_iter();
                (params.next().unwrap(), params.next().unwrap())
            };
            reconstruct(tcx, &mut body);
            let index_method = lang_item_method(
                tcx,
                rustc_hir::lang_items::LangItem::Index,
                rustc_span::sym::index,
            );
            let call = find_call(&body, index_method);
            assert_eq!(call.args.len(), 2);
            let Operand::Copy(shared_receiver) = &call.args[0].node else {
                panic!("shared indexing receiver must be copied");
            };
            assert!(shared_receiver.projection.is_empty());
            assert_eq!(call.args[1].node, Operand::Copy(index.into()));
            let (_, reborrow) = body.basic_blocks[call.block]
                .statements
                .iter()
                .filter_map(|statement| statement.kind.as_assign())
                .find(|(place, _)| place.local == shared_receiver.local)
                .expect("shared receiver reborrow was not inserted");
            assert!(matches!(
                reborrow,
                Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, referent)
                    if *referent == tcx.mk_place_deref(receiver.into())
            ));
        },
    );
}
