#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::interface::Compiler;
use rustc_interface::Queries;

struct CompilerCalls {}

impl Callbacks for CompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let mut ctx = refinement_analyzer::Analyzer::new(tcx);
            ctx.register_well_known_defs();
            ctx.crate_analyzer().run();
            ctx.solve();
        });
        Compilation::Stop
    }
}

pub fn main() {
    let args = std::env::args().collect::<Vec<_>>();

    use tracing_subscriber::{
        filter::{EnvFilter, LevelFilter},
        prelude::*,
    };
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_writer(std::io::stderr)
                .compact()
                .with_target(false)
                .without_time()
                .with_filter(
                    EnvFilter::builder()
                        .with_default_directive(LevelFilter::INFO.into())
                        .from_env_lossy(),
                ),
        )
        .init();

    let code =
        rustc_driver::catch_with_exit_code(|| RunCompiler::new(&args, &mut CompilerCalls {}).run());
    std::process::exit(code);
}
