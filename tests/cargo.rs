//! Verifies whole cargo projects, the way Thrust is used on a project rather than on a
//! single file.
//!
//! Each directory under `tests/cargo/pass/` and `tests/cargo/fail/` is one cargo project,
//! built with `thrust-rustc` standing in for `rustc`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cargo")
}

/// The cargo projects expected to verify with the given outcome, one per directory.
fn projects(outcome: &str) -> Vec<PathBuf> {
    let dir = fixture_root().join(outcome);
    let mut projects: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("Cargo.toml").is_file())
        .collect();
    projects.sort();
    assert!(!projects.is_empty(), "no project in {}", dir.display());
    projects
}

/// Builds `project` with `thrust-rustc` in place of `rustc`.
///
/// The target directory is wiped first, so that cargo cannot reuse an earlier run's
/// fingerprint and report success without ever having invoked the verifier.
fn build(project: &Path) -> Output {
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/tests/cargo")
        .join(project.strip_prefix(fixture_root()).unwrap());
    if target_dir.exists() {
        std::fs::remove_dir_all(&target_dir).unwrap();
    }

    Command::new(env!("CARGO"))
        .arg("build")
        .current_dir(project)
        .env("RUSTC", env!("CARGO_BIN_EXE_thrust-rustc"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .output()
        .unwrap()
}

#[test]
fn pass_projects_verify() {
    for project in projects("pass") {
        let output = build(&project);
        assert!(
            output.status.success(),
            "{} did not verify:\n{}",
            project.display(),
            String::from_utf8_lossy(&output.stderr),
        );
    }
}

#[test]
fn fail_projects_report_unsat() {
    for project in projects("fail") {
        let output = build(&project);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{} verified unexpectedly",
            project.display(),
        );
        assert!(
            stderr.contains("verification error: Unsat"),
            "{} failed for another reason:\n{stderr}",
            project.display(),
        );
    }
}
