use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use bamts_compiler::program::ProgramLoadError;
use bamts_compiler::project::canonical::canonicalize;

use crate::driver::DriverError;

/// Immutable process inputs captured for one CLI invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionContext {
    cwd: PathBuf,
    env: BTreeMap<OsString, OsString>,
    temp_dir: PathBuf,
}

impl ExecutionContext {
    /// Captures the process working directory and environment for one invocation.
    pub fn ambient() -> Result<Self, DriverError> {
        let cwd = std::env::current_dir().map_err(|source| DriverError::ReadSource {
            path: PathBuf::from("."),
            source,
        })?;
        let env = std::env::vars_os().collect();
        let temp_dir = std::env::temp_dir();
        let cwd = canonicalize_cwd(&cwd)?;
        let temp_dir = resolve_from(&cwd, temp_dir);
        Ok(Self { cwd, env, temp_dir })
    }

    /// Creates a context from explicit process inputs.
    pub fn new(
        cwd: impl AsRef<Path>,
        env: BTreeMap<OsString, OsString>,
    ) -> Result<Self, DriverError> {
        let cwd = canonicalize_cwd(cwd.as_ref())?;
        let temp_dir = resolve_from(&cwd, temp_dir_from_env(&env));
        Ok(Self { cwd, env, temp_dir })
    }

    /// Resolves an invocation-relative OS path without consulting process state.
    #[must_use]
    pub fn resolve_path(&self, path: impl AsRef<Path>) -> PathBuf {
        resolve_from(&self.cwd, path.as_ref().to_path_buf())
    }

    #[must_use]
    pub fn cwd(&self) -> &Path {
        &self.cwd
    }

    #[must_use]
    pub fn temp_dir(&self) -> &Path {
        &self.temp_dir
    }

    #[must_use]
    pub fn env(&self, key: impl AsRef<OsStr>) -> Option<&OsStr> {
        self.env.get(key.as_ref()).map(OsString::as_os_str)
    }

    pub fn envs(&self) -> impl Iterator<Item = (&OsStr, &OsStr)> {
        self.env
            .iter()
            .map(|(key, value)| (key.as_os_str(), value.as_os_str()))
    }
}

fn canonicalize_cwd(cwd: &Path) -> Result<PathBuf, DriverError> {
    canonicalize(cwd)
        .map_err(|error| DriverError::ProgramLoad(ProgramLoadError::InvalidRoot(error)))
}

fn resolve_from(cwd: &Path, path: PathBuf) -> PathBuf {
    if path.is_absolute() {
        path
    } else {
        cwd.join(path)
    }
}

#[cfg(unix)]
fn temp_dir_from_env(env: &BTreeMap<OsString, OsString>) -> PathBuf {
    env.get(OsStr::new("TMPDIR"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/tmp"))
}

/// The value of the variable `key`, found without regard to case: Windows spells
/// the search path `Path`, and an environment map compares keys exactly.
#[cfg(any(windows, test))]
pub(crate) fn env_ignoring_case<'a>(
    env: impl IntoIterator<Item = (&'a OsStr, &'a OsStr)>,
    key: &str,
) -> Option<&'a OsStr> {
    env.into_iter()
        .find(|(candidate, _)| candidate.to_string_lossy().eq_ignore_ascii_case(key))
        .map(|(_, value)| value)
}

#[cfg(windows)]
fn temp_dir_from_env(env: &BTreeMap<OsString, OsString>) -> PathBuf {
    let value = |key: &str| {
        env_ignoring_case(
            env.iter()
                .map(|(name, value)| (name.as_os_str(), value.as_os_str())),
            key,
        )
    };

    for key in ["TMP", "TEMP", "USERPROFILE"] {
        if let Some(path) = value(key) {
            return PathBuf::from(path);
        }
    }
    value("SystemRoot")
        .or_else(|| value("WINDIR"))
        .map(|root| PathBuf::from(root).join("Temp"))
        .unwrap_or_else(|| PathBuf::from(r"C:\Windows\Temp"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The variable that names the temporary directory on this platform.
    const TEMP_VARIABLE: &str = if cfg!(windows) { "TMP" } else { "TMPDIR" };

    #[test]
    fn explicit_context_resolves_relative_and_empty_temp_paths_from_cwd() {
        let directory = tempfile::tempdir().expect("temporary directory");
        for (value, expected) in [
            (OsString::from("tmp"), directory.path().join("tmp")),
            (OsString::new(), directory.path().to_path_buf()),
        ] {
            let context = ExecutionContext::new(
                directory.path(),
                BTreeMap::from([(OsString::from(TEMP_VARIABLE), value)]),
            )
            .expect("execution context");
            assert_eq!(context.temp_dir(), expected);
        }
    }

    #[test]
    fn explicit_context_resolves_relative_paths_from_cwd() {
        let directory = tempfile::tempdir().expect("temporary directory");
        let context =
            ExecutionContext::new(directory.path(), BTreeMap::new()).expect("execution context");
        assert_eq!(
            context.resolve_path("cache"),
            directory.path().join("cache")
        );
        assert_eq!(context.resolve_path(directory.path()), directory.path());
    }
}
