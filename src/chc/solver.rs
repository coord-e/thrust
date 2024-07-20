#[derive(Debug, thiserror::Error)]
pub enum CheckSatError {
    #[error("unsat")]
    Unsat,
    #[error("solver error: stdout: {stdout} stderr: {stderr}")]
    Error { stdout: String, stderr: String },
    #[error("timed out after {0:?}")]
    Timeout(std::time::Duration),
    #[error("io error")]
    Io(#[from] std::io::Error),
}

#[derive(Debug, Clone)]
pub struct Config {
    pub solver: String,
    pub solver_args: Vec<String>,
    pub temp_dir: std::path::PathBuf,
    pub timeout: Option<std::time::Duration>,
    pub smtlib2_output: Option<std::path::PathBuf>,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            solver: "z3".to_owned(),
            solver_args: vec!["fp.spacer.global=true".to_owned()],
            temp_dir: std::env::temp_dir(),
            timeout: Some(std::time::Duration::from_secs(30)),
            smtlib2_output: None,
        }
    }
}

impl Config {
    pub fn load_env() -> Config {
        let mut config = Config::default();
        if let Some(solver) = std::env::var("REFA_SOLVER").ok() {
            config.solver = solver;
        }
        if config.solver != "z3" {
            config.solver_args.clear();
        }
        if let Some(args) = std::env::var("REFA_SOLVER_ARGS").ok() {
            config.solver_args = args.split_whitespace().map(|s| s.to_owned()).collect();
        }
        if let Some(dir) = std::env::var("REFA_SOLVER_TEMP_DIR").ok() {
            config.temp_dir = dir.into();
        }
        if let Some(timeout) = std::env::var("REFA_SOLVER_TIMEOUT_SECS").ok() {
            let timeout_secs = timeout.parse().unwrap();
            if timeout_secs == 0 {
                config.timeout = None;
            } else {
                config.timeout = Some(std::time::Duration::from_secs(timeout_secs));
            }
        }
        if let Some(path) = std::env::var("REFA_SMTLIB2_OUTPUT").ok() {
            config.smtlib2_output = Some(path.into());
        }
        config
    }

    fn wait_solver(
        &self,
        mut child: std::process::Child,
    ) -> Result<(std::process::Output, std::time::Duration), CheckSatError> {
        let start = std::time::Instant::now();
        let deadline = self.timeout.map(|timeout| start + timeout);
        tracing::info!(timeout = ?self.timeout, pid = child.id(), "waiting solver");
        while child.try_wait()?.is_none() {
            if let Some(deadline) = deadline {
                if deadline < std::time::Instant::now() {
                    child.kill()?;
                    return Err(CheckSatError::Timeout(self.timeout.unwrap()));
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        let elapsed = std::time::Instant::now() - start;
        Ok((child.wait_with_output()?, elapsed))
    }

    pub fn check_sat(&self, problem: impl std::fmt::Display) -> Result<(), CheckSatError> {
        use std::io::Write as _;
        let smt2 = format!("{}\n(check-sat)\n", problem);
        let mut file = tempfile::Builder::new()
            .suffix(".smt2")
            .tempfile_in(&self.temp_dir)?;
        write!(file, "{}", smt2)?;

        let child = std::process::Command::new(&self.solver)
            .args(&self.solver_args)
            .arg(file.path())
            .stdout(std::process::Stdio::piped())
            .spawn()?;
        tracing::info!(solver = self.solver, args = ?self.solver_args, path = %file.path().display(), pid = child.id(), "spawned solver");

        let (output, elapsed) = self.wait_solver(child)?;
        if let Some(path) = &self.smtlib2_output {
            file.persist(path).map_err(|e| e.error)?;
        } else {
            drop(file);
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        tracing::info!(status = %output.status, stdout = stdout.trim(), stderr = stderr.trim(), ?elapsed, "solver exited");
        match stdout.trim() {
            "sat" if output.status.success() => Ok(()),
            "unsat" if output.status.success() => Err(CheckSatError::Unsat),
            _ => Err(CheckSatError::Error {
                stdout: stdout.into_owned(),
                stderr: stderr.into_owned(),
            }),
        }
    }
}
