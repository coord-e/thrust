pub struct BasicBlockAnalyzer<'rcx, 'tcx, 'mir> {
    tcx: TyCtxt<'tcx>,
    bcx: RefineBasicBlockCtxt<'rcx>,

    body: &'mir Body<'tcx>,
    data: &'mir BasicBlockData<'tcx>,
}
