use std::process::{Command, Output};

fn cargo_check(fixture: &str) -> Output {
    let target_dir = tempfile::tempdir().unwrap();
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/cargo")
        .join(fixture);
    Command::new(env!("CARGO"))
        .args(["check", "--offline", "--locked", "--manifest-path"])
        .arg(fixture.join("Cargo.toml"))
        .env("RUSTC", env!("CARGO_BIN_EXE_thrust-rustc"))
        .env("RUSTFLAGS", "-C debug-assertions=false")
        .env("CARGO_TARGET_DIR", target_dir.path())
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("THRUST_OUTPUT_DIR")
        .output()
        .unwrap()
}

#[test]
fn cargo_check_passes_verification() {
    let output = cargo_check("pass");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn cargo_check_reports_verification_failure() {
    let output = cargo_check("fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(stderr.contains("verification error: Unsat"), "{stderr}");
}
