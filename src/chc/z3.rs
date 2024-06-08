#[derive(Debug, thiserror::Error)]
pub enum CheckSatError {
    #[error("unsat")]
    Unsat,
    #[error("z3 error")]
    Error(String),
    #[error("io error")]
    Io(#[from] std::io::Error),
}

const SMT2_FILE: &str = "refinement-analyzer.smt2";

pub fn check_sat(problem: &str) -> Result<(), CheckSatError> {
    use std::io::Write as _;
    let smt2 = format!("{}\n(check-sat)\n", problem);
    std::fs::write(SMT2_FILE, &smt2)?;
    let mut file = tempfile::NamedTempFile::new()?;
    write!(file, "{}", smt2)?;
    let output = std::process::Command::new("z3")
        .arg("fp.spacer.global=true")
        .arg(file.path())
        .output()?;
    drop(file);
    let result = std::str::from_utf8(&output.stdout).unwrap().trim();
    match result {
        "sat" => Ok(()),
        "unsat" => Err(CheckSatError::Unsat),
        _ => Err(CheckSatError::Error(result.to_owned())),
    }
}
