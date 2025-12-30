#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::interface::{Compiler, Config};
use rustc_interface::Queries;

struct CompilerCalls {}

impl Callbacks for CompilerCalls {
    fn config(&mut self, config: &mut Config) {
        let attrs = &mut config.opts.unstable_opts.crate_attr;
        attrs.push("feature(register_tool)".to_owned());
        attrs.push("register_tool(thrust)".to_owned());
    }

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let mut result = queries.parse().unwrap();
        let krate = result.get_mut();

        let injected = include_str!("../std.rs");
        let mut parser = rustc_parse::new_parser_from_source_str(
            &compiler.sess.psess,
            rustc_span::FileName::Custom("thrust std injected".to_string()),
            injected.to_owned(),
        );
        while let Some(item) = parser
            .parse_item(rustc_parse::parser::ForceCollect::No)
            .unwrap()
        {
            krate.items.push(item);
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let mut ctx = thrust::Analyzer::new(tcx);
            ctx.register_well_known_defs();
            ctx.crate_analyzer().run();
            ctx.solve();
        });
        Compilation::Stop
    }
}

pub fn main() {
    let args = std::env::args().collect::<Vec<_>>();

    use tracing_subscriber::{filter::EnvFilter, prelude::*};
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_writer(std::io::stderr)
                .compact()
                .without_time()
                .with_filter(EnvFilter::from_default_env()),
        )
        .init();

    let code =
        rustc_driver::catch_with_exit_code(|| RunCompiler::new(&args, &mut CompilerCalls {}).run());
    std::process::exit(code);
}
