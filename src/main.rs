#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};

struct CompilerCalls {}

impl Callbacks for CompilerCalls {
    fn config(&mut self, config: &mut Config) {
        let attrs = &mut config.opts.unstable_opts.crate_attr;
        attrs.push("feature(register_tool)".to_owned());
        attrs.push("register_tool(thrust)".to_owned());

        config.override_queries = Some(|_sess, providers| {
            providers.queries.mir_borrowck = thrust::mir_borrowck_skip_formula_fn;
        });
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &Compiler,
        krate: &mut rustc_ast::Crate,
    ) -> Compilation {
        if matches!(std::env::var("THRUST_NO_INJECT_STD").as_deref(), Ok("1")) {
            return Compilation::Continue;
        }

        let injected = include_str!("../std.rs");
        let mut parser = rustc_parse::new_parser_from_source_str(
            &compiler.sess.psess,
            rustc_span::FileName::Custom("thrust std injected".to_string()),
            injected.to_owned(),
            rustc_parse::lexer::StripTokens::Nothing,
        )
        .unwrap();
        while let Some(item) = parser
            .parse_item(
                rustc_parse::parser::ForceCollect::No,
                rustc_parse::parser::AllowConstBlockItems::No,
            )
            .unwrap()
        {
            krate.items.push(item);
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> Compilation {
        let mut ctx = thrust::Analyzer::new(tcx);
        ctx.register_well_known_defs();
        ctx.crate_analyzer().run();
        ctx.solve();
        Compilation::Stop
    }
}

fn thrust_macros_path() -> Option<std::path::PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?;
    // When thrust-macros is a cargo dependency it lands in deps/ with a hash
    // suffix (e.g. libthrust_macros-<hash>.so), so check both locations.
    let search_dirs = [dir.to_path_buf(), dir.join("deps")];
    for search_dir in &search_dirs {
        for ext in ["so", "dylib", "dll"] {
            // First try the exact name (e.g. when built standalone).
            let candidate = search_dir.join(format!("libthrust_macros.{ext}"));
            if candidate.exists() {
                return Some(candidate);
            }
            // Then scan for libthrust_macros-<hash>.<ext>.
            if let Ok(entries) = std::fs::read_dir(search_dir) {
                for entry in entries.flatten() {
                    let name = entry.file_name();
                    let name = name.to_string_lossy();
                    if name.starts_with("libthrust_macros-") && name.ends_with(ext) {
                        return Some(entry.path());
                    }
                }
            }
        }
    }
    None
}

pub fn main() -> std::process::ExitCode {
    let mut args = std::env::args().collect::<Vec<_>>();

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

    if let Some(path) = thrust_macros_path() {
        args.push("--extern".to_owned());
        args.push(format!("thrust_macros={}", path.display()));
        tracing::debug!("linking thrust_macros from {}", path.display());
    } else {
        tracing::warn!("could not locate thrust_macros library");
    }

    rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut CompilerCalls {}))
}
