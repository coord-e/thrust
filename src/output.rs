//! Intermediate files Thrust writes out for inspection.
//!
//! Writing is enabled by the `THRUST_OUTPUT_DIR` environment variable, which names the
//! directory the files are placed in.

/// The directory to write intermediate files into, or `None` when writing is disabled.
pub fn dir() -> Option<std::path::PathBuf> {
    std::env::var_os("THRUST_OUTPUT_DIR").map(Into::into)
}
