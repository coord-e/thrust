#[derive(Debug, thiserror::Error)]
pub enum CheckSatError {
    #[error("unsat")]
    Unsat,
    #[error("solver error: stdout: {stdout} stderr: {stderr}")]
    Error { stdout: String, stderr: String },
    #[error("unknown output: {stdout}")]
    Unknown { stdout: String },
    #[error("timed out after {0:?}")]
    Timeout(std::time::Duration),
    #[error("io error")]
    Io(#[from] std::io::Error),
}

#[derive(Debug, Clone)]
pub struct CommandConfig {
    pub name: String,
    pub args: Vec<String>,
    pub timeout: Option<std::time::Duration>,
}

impl CommandConfig {
    fn load_args(&mut self, env: &str) {
        if let Ok(args) = std::env::var(env) {
            self.args = args.split_whitespace().map(|s| s.to_owned()).collect();
        }
    }

    fn load_timeout(&mut self, env: &str) {
        if let Ok(timeout) = std::env::var(env) {
            let timeout_secs = timeout.parse().unwrap();
            if timeout_secs == 0 {
                self.timeout = None;
            } else {
                self.timeout = Some(std::time::Duration::from_secs(timeout_secs));
            }
        }
    }

    fn wait_child(
        &self,
        child: std::process::Child,
    ) -> Result<(std::process::Output, std::time::Duration), CheckSatError> {
        use process_control::{ChildExt as _, Control as _};

        let start = std::time::Instant::now();
        tracing::info!(timeout = ?self.timeout, pid = child.id(), "waiting");
        let mut child = child.controlled_with_output().terminate_for_timeout();
        if let Some(timeout) = self.timeout {
            child = child.time_limit(timeout);
        }
        let output = match child.wait()? {
            None => return Err(CheckSatError::Timeout(self.timeout.unwrap())),
            Some(output) => output,
        };
        let elapsed = std::time::Instant::now() - start;
        Ok((output.into_std_lossy(), elapsed))
    }

    fn run(
        &self,
        path_arg: impl AsRef<std::path::Path>,
        stdout: impl Into<std::process::Stdio>,
    ) -> Result<String, CheckSatError> {
        let path_arg = path_arg.as_ref();
        let child = std::process::Command::new(&self.name)
            .args(&self.args)
            .arg(path_arg)
            .stdout(stdout)
            .spawn()?;
        tracing::info!(program = self.name, args = ?self.args, path = %path_arg.to_string_lossy(), pid = child.id(), "spawned");

        let (output, elapsed) = self.wait_child(child)?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        tracing::info!(status = %output.status, ?elapsed, "exited");
        if !output.status.success() {
            return Err(CheckSatError::Error {
                stdout: stdout.into_owned(),
                stderr: stderr.into_owned(),
            });
        }
        Ok(stdout.into_owned())
    }
}

#[derive(Debug, Clone)]
pub struct Config {
    pub solver: CommandConfig,
    pub preprocessor: Option<CommandConfig>,
    pub output_dir: Option<std::path::PathBuf>,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            solver: CommandConfig {
                name: "z3".to_owned(),
                args: vec!["fp.spacer.global=true".to_owned()],
                timeout: Some(std::time::Duration::from_secs(30)),
            },
            preprocessor: None,
            output_dir: None,
        }
    }
}

impl Config {
    pub fn from_env() -> Config {
        let mut config = Config::default();
        if let Ok(solver) = std::env::var("THRUST_SOLVER") {
            config.solver.name = solver;
        }
        if config.solver.name != "z3" {
            config.solver.args.clear();
        }
        config.solver.load_args("THRUST_SOLVER_ARGS");
        config.solver.load_timeout("THRUST_SOLVER_TIMEOUT_SECS");
        if let Ok(preproc) = std::env::var("THRUST_PREPROCESSOR") {
            let mut preproc_config = CommandConfig {
                name: preproc,
                args: vec![],
                timeout: Some(std::time::Duration::from_secs(30)),
            };
            preproc_config.load_args("THRUST_PREPROCESSOR_ARGS");
            preproc_config.load_timeout("THRUST_PREPROCESSOR_TIMEOUT_SECS");
            config.preprocessor = Some(preproc_config);
        }
        if let Ok(dir) = std::env::var("THRUST_OUTPUT_DIR") {
            config.output_dir = Some(dir.into());
        }
        config
    }

    pub fn check_sat(&self, problem: impl std::fmt::Display) -> Result<(), CheckSatError> {
        use std::io::{Seek as _, Write as _};
        let smt2 = format!("{}\n(check-sat)\n", problem);
        let mut file = tempfile::Builder::new()
            .prefix("thrust_tmp_")
            .suffix(".smt2")
            .tempfile()?;
        write!(file, "{}", smt2)?;
        file.flush()?;
        if let Some(dir) = &self.output_dir {
            std::fs::copy(&file, dir.join("thrust_output.smt2"))?;
        }

        if let Some(preproc) = &self.preprocessor {
            let output = preproc.run(file.path(), std::process::Stdio::piped())?;
            file.as_file_mut().set_len(0)?;
            file.rewind()?;
            write!(file, "{}", output)?;
            if let Some(dir) = &self.output_dir {
                std::fs::copy(&file, dir.join("preproc_output.smt2"))?;
            }
        }

        let output = self.solver.run(file.path(), std::process::Stdio::piped())?;
        drop(file);
        match output.trim() {
            "sat" => Ok(()),
            "unsat" => Err(CheckSatError::Unsat),
            _ => Err(CheckSatError::Unknown { stdout: output }),
        }
    }
}
