//! Historical TypeScript catalogs: which cells keep a measurement, and from where.
//!
//! The contract keeps TypeScript 6.0 and 5.9 inputs only while the stable 7.0.2
//! oracle still accepts them, and they never act as oracles: a historical tree
//! supplies inputs, never expected output.
//!
//! A historical cell takes the 7.0.2 measurement when 7.0.2 declares the same
//! input, byte for byte, and its receipt row says so. Every 6.0.2 input qualifies.
//! Any other cell has nothing to be compared with until it is run against the
//! oracle, so it stays a blocking row that names why, and never reads as a pass.

use std::{
    collections::BTreeMap,
    fs,
    io::ErrorKind,
    path::{Path, PathBuf},
};

use crate::{
    ErrorCode, Result, VerificationError,
    check_cells::CheckContext,
    lane::{LaneOutcome, LaneRequest},
    shard::ObligationKey,
    suite::{COMPILER_CATALOG, SnapshotAssets, observe_compiler_lane},
};

/// Catalogs measured through their 7.0.2 twin.
pub const HISTORICAL_CATALOGS: [&str; 2] = ["typescript-6.0.2", "typescript-5.9.3"];

/// Support files every `project/` case reads, relative to an authority tree.
const PROJECT_SUPPORT: &str = "tests/cases/projects";

/// What a reused row records about where its measurement came from.
const REUSED_FROM: &str = "typescript-7.0.2 cell with byte-identical input";

#[must_use]
pub fn is_historical(catalog: &str) -> bool {
    HISTORICAL_CATALOGS.contains(&catalog)
}

/// Measures one historical compiler cell.
///
/// # Errors
///
/// Returns an error when the cell's own input cannot be read, which means the
/// authority tree is damaged rather than that the cell failed.
pub fn observe_historical_lane(
    workspace: &Path,
    snapshot: &(impl SnapshotAssets + ?Sized),
    ctx: &CheckContext,
    request: &LaneRequest,
) -> Result<LaneOutcome> {
    let key = request.key();
    if let Some(reason) = reuse_blocker(workspace, key.catalog(), key.case())? {
        return Ok(LaneOutcome::BlockingFail {
            detail: format!("historical cell has no oracle comparison: {reason}"),
        });
    }
    let stable = ObligationKey::new(
        COMPILER_CATALOG,
        key.case(),
        key.configuration(),
        key.mode(),
        key.platform(),
    )?;
    let outcome = observe_compiler_lane(snapshot, ctx, &request.with_key(stable)?).lane_outcome();
    Ok(match outcome {
        LaneOutcome::Completed { artifacts } => LaneOutcome::Reused {
            artifacts,
            source: REUSED_FROM.to_owned(),
        },
        other => other,
    })
}

/// Why this case cannot take the 7.0.2 measurement, or `None` when it can.
fn reuse_blocker(workspace: &Path, catalog: &str, case: &str) -> Result<Option<String>> {
    let Some((runner, relative)) = case.split_once('/') else {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("case `{case}` has no authority path"),
        ));
    };
    let input = read_file(&authority_tree(workspace, catalog).join(relative))?;
    let stable_tree = authority_tree(workspace, COMPILER_CATALOG);
    let stable = match fs::read(stable_tree.join(relative)) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == ErrorKind::NotFound => {
            return Ok(Some("7.0.2 has no such input".to_owned()));
        }
        Err(error) => return Err(io_error(&stable_tree.join(relative), &error)),
    };
    if input != stable {
        return Ok(Some("its input differs from 7.0.2".to_owned()));
    }
    if runner == "project" {
        let own = read_tree(&authority_tree(workspace, catalog).join(PROJECT_SUPPORT))?;
        if own != read_tree(&stable_tree.join(PROJECT_SUPPORT))? {
            return Ok(Some("its project files differ from 7.0.2".to_owned()));
        }
    }
    Ok(None)
}

fn authority_tree(workspace: &Path, catalog: &str) -> PathBuf {
    workspace.join(format!("target/authority/{catalog}-tests"))
}

fn read_file(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| io_error(path, &error))
}

/// Every file under `root` by relative path. Finder's folder files are not input.
fn read_tree(root: &Path) -> Result<BTreeMap<PathBuf, Vec<u8>>> {
    let mut files = BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory).map_err(|error| io_error(&directory, &error))? {
            let path = entry.map_err(|error| io_error(&directory, &error))?.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.file_name().is_some_and(|name| name != ".DS_Store") {
                let relative = path.strip_prefix(root).unwrap_or(&path).to_path_buf();
                files.insert(relative, read_file(&path)?);
            }
        }
    }
    Ok(files)
}

fn io_error(path: &Path, error: &std::io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    const HISTORICAL: &str = "typescript-5.9.3";
    const CASE: &str = "compiler/tests/cases/compiler/a.ts";
    const PROJECT: &str = "project/tests/cases/project/a.json";

    fn workspace(name: &str) -> PathBuf {
        let root =
            std::env::temp_dir().join(format!("bamts-historical-{}-{name}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("scratch");
        root
    }

    fn write(root: &Path, catalog: &str, relative: &str, text: &str) {
        let path = authority_tree(root, catalog).join(relative);
        fs::create_dir_all(path.parent().expect("parent")).expect("directories");
        fs::write(path, text).expect("write");
    }

    fn both(root: &Path, relative: &str, text: &str) {
        write(root, HISTORICAL, relative, text);
        write(root, COMPILER_CATALOG, relative, text);
    }

    #[test]
    fn identical_input_takes_the_stable_measurement() {
        let root = workspace("identical");
        both(&root, "tests/cases/compiler/a.ts", "let a = 1;");
        assert_eq!(reuse_blocker(&root, HISTORICAL, CASE).expect("reads"), None);
        fs::remove_dir_all(root).expect("remove scratch");
    }

    #[test]
    fn one_changed_byte_blocks_reuse() {
        let root = workspace("changed");
        write(&root, HISTORICAL, "tests/cases/compiler/a.ts", "let a = 1;");
        write(
            &root,
            COMPILER_CATALOG,
            "tests/cases/compiler/a.ts",
            "let a = 2;",
        );
        let reason = reuse_blocker(&root, HISTORICAL, CASE).expect("reads");
        assert_eq!(reason.as_deref(), Some("its input differs from 7.0.2"));
        fs::remove_dir_all(root).expect("remove scratch");
    }

    #[test]
    fn an_input_7_0_2_dropped_cannot_be_reused() {
        let root = workspace("dropped");
        write(&root, HISTORICAL, "tests/cases/compiler/a.ts", "let a = 1;");
        let reason = reuse_blocker(&root, HISTORICAL, CASE).expect("reads");
        assert_eq!(reason.as_deref(), Some("7.0.2 has no such input"));
        fs::remove_dir_all(root).expect("remove scratch");
    }

    #[test]
    fn a_missing_historical_input_is_an_error_not_a_failed_cell() {
        let root = workspace("damaged");
        let error = reuse_blocker(&root, HISTORICAL, CASE).expect_err("damaged tree");
        assert_eq!(error.code(), ErrorCode::Io);
        fs::remove_dir_all(root).expect("remove scratch");
    }

    #[test]
    fn a_project_case_also_needs_its_support_files_identical() {
        let root = workspace("project");
        both(&root, "tests/cases/project/a.json", "{}");
        both(&root, "tests/cases/projects/a/a.ts", "let a = 1;");
        assert_eq!(
            reuse_blocker(&root, HISTORICAL, PROJECT).expect("reads"),
            None
        );

        write(
            &root,
            HISTORICAL,
            "tests/cases/projects/.DS_Store",
            "finder",
        );
        assert_eq!(
            reuse_blocker(&root, HISTORICAL, PROJECT).expect("reads"),
            None
        );

        write(
            &root,
            HISTORICAL,
            "tests/cases/projects/a/a.ts",
            "let a = 2;",
        );
        let reason = reuse_blocker(&root, HISTORICAL, PROJECT).expect("reads");
        assert_eq!(
            reason.as_deref(),
            Some("its project files differ from 7.0.2")
        );
        fs::remove_dir_all(root).expect("remove scratch");
    }

    #[test]
    fn only_the_two_historical_catalogs_are_historical() {
        assert!(is_historical("typescript-6.0.2"));
        assert!(is_historical("typescript-5.9.3"));
        assert!(!is_historical(COMPILER_CATALOG));
        assert!(!is_historical("test262"));
    }
}
