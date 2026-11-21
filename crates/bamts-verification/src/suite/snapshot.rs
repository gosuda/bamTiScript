use super::ci::build_provisional_ledger;
use super::{
    AssetKind, COMPILER_CATALOG, CompilerSnapshot, ImportedAsset, IndexEntry, SnapshotAssets,
    SuiteIndex, SuiteSnapshot, SyncOptions, VerifiedSuite,
};
use crate::catalog::ObservableKind;
use crate::lane::LaneBinding;
use crate::oracle_pins::{
    COMPILER_COMMIT, COMPILER_DIGEST, COMPILER_REPOSITORY, COMPILER_TAG, COMPILER_URL,
    NPM_INTEGRITY, NPM_SPECIFIER, OraclePins, SUITE_COMMIT, SUITE_DIGEST, SUITE_REPOSITORY,
    SUITE_URL, verify_oracle_pins,
};
use crate::schema::sha256_hex;
use crate::ts_ledger::{Facet, Partition, TsLedgerReader, TsLedgerWriter};
use crate::{ErrorCode, Result, VerificationError};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Component, Path, PathBuf},
    process::Command,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct PinDocument {
    npm_specifier: String,
    npm_integrity: String,
    compiler_repository: String,
    compiler_commit: String,
    compiler_tag: String,
    suite_repository: String,
    suite_commit: String,
}

impl PinDocument {
    fn from_pins(pins: &OraclePins) -> Self {
        Self {
            npm_specifier: pins.npm_specifier.clone(),
            npm_integrity: pins.npm_integrity.clone(),
            compiler_repository: pins.compiler_repository.clone(),
            compiler_commit: pins.compiler_commit.clone(),
            compiler_tag: pins.compiler_tag.clone(),
            suite_repository: pins.suite_repository.clone(),
            suite_commit: pins.suite_commit.clone(),
        }
    }

    fn expected() -> Self {
        Self::from_pins(&OraclePins::expected())
    }
}

/// Import / materialize a suite snapshot.
pub fn sync_suite(options: &SyncOptions) -> Result<SuiteSnapshot> {
    let pins = if options.verify_pin {
        if options.extracted_suite_root.is_some() {
            OraclePins::expected()
        } else {
            verify_oracle_pins(&options.workspace_root)?
        }
    } else {
        OraclePins::expected()
    };

    // Keep extraction temps alive until walks finish.
    let mut cleanup_suite: Option<TempDir> = None;
    let mut cleanup_compiler: Option<TempDir> = None;
    let assets = if let Some(root) = &options.extracted_suite_root {
        walk_extracted_tree(root)?
    } else {
        let archives = options.snapshot_root.join(".archives");
        fs::create_dir_all(&archives).map_err(|e| io_err(&archives, &e))?;
        let suite_archive = fetch_archive(SUITE_URL, SUITE_DIGEST, &archives)?;
        let compiler_archive = fetch_archive(COMPILER_URL, COMPILER_DIGEST, &archives)?;
        let suite_extracted = extract_archive(&suite_archive)?;
        let compiler_extracted = extract_archive(&compiler_archive)?;
        let suite_root = single_archive_root(suite_extracted.path())?;
        let compiler_root = single_archive_root(compiler_extracted.path())?;
        let mut assets = walk_extracted_tree(&suite_root)?;
        merge_compiler_license_notice(&mut assets, &compiler_root)?;
        cleanup_suite = Some(suite_extracted);
        cleanup_compiler = Some(compiler_extracted);
        assets
    };

    if !options.write_snapshot {
        let _ = (cleanup_suite, cleanup_compiler);
        return Err(VerificationError::new(
            ErrorCode::Usage,
            "sync requires --write-snapshot",
        ));
    }

    let snapshot = materialize_snapshot(&options.snapshot_root, &pins, &assets)?;
    let _ = (cleanup_suite, cleanup_compiler);
    verify_snapshot(&options.snapshot_root)?;
    Ok(snapshot)
}

/// Decodes case bytes to source text the way a TypeScript-compatible reader
/// does: a UTF-16 BE (`FE FF`) or LE (`FF FE`) byte-order mark selects UTF-16
/// decoding, a UTF-8 BOM (`EF BB BF`) is stripped, and the leading marker is
/// dropped. Malformed units decode lossily so the parser still observes a total
/// source — the parse facet proves recovery, not byte-perfect re-encoding.
pub fn decode_case_source(bytes: &[u8]) -> String {
    if let [0xFE, 0xFF, rest @ ..] = bytes {
        let units: Vec<u16> = rest
            .chunks(2)
            .map(|pair| u16::from_be_bytes([pair[0], pair.get(1).copied().unwrap_or(0)]))
            .collect();
        return String::from_utf16_lossy(&units);
    }
    if let [0xFF, 0xFE, rest @ ..] = bytes {
        let units: Vec<u16> = rest
            .chunks(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair.get(1).copied().unwrap_or(0)]))
            .collect();
        return String::from_utf16_lossy(&units);
    }
    let body = bytes.strip_prefix(&[0xEF, 0xBB, 0xBF]).unwrap_or(bytes);
    String::from_utf8_lossy(body).into_owned()
}

type PathClassification = Option<(AssetKind, Option<Partition>, Option<Facet>)>;

/// Classify a suite-relative logical path.
pub fn classify_logical_path(logical_path: &str) -> Result<PathClassification> {
    if logical_path.is_empty() {
        return Ok(None);
    }
    let path = Path::new(logical_path);
    if path.is_absolute() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("absolute path rejected: `{logical_path}`"),
        ));
    }
    for component in path.components() {
        match component {
            Component::Normal(_) => {}
            Component::CurDir => {}
            Component::ParentDir => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("path traversal rejected: `{logical_path}`"),
                ));
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("absolute path rejected: `{logical_path}`"),
                ));
            }
        }
    }

    let lower = logical_path.to_ascii_lowercase();
    if lower.contains("hereby")
        || lower.contains("internal/testutil")
        || lower.contains("/runners/")
        || lower.contains("\\runners\\")
    {
        return Ok(None);
    }

    if let Some(rest) = logical_path.strip_prefix("tests/cases/") {
        let partition = match rest.split('/').next().unwrap_or("") {
            "compiler" => Partition::Compiler,
            "conformance" => Partition::Conformance,
            "project" => Partition::Project,
            "projects" => Partition::Projects,
            "transpile" => Partition::Transpile,
            "unittests" => Partition::UnitTests,
            _ => return Ok(None),
        };
        if rest.contains('/') {
            return Ok(Some((AssetKind::CaseInput, Some(partition), None)));
        }
        return Ok(None);
    }
    if let Some(rest) = logical_path.strip_prefix("tests/lib/") {
        if rest.to_ascii_lowercase().ends_with(".d.ts") {
            return Ok(Some((AssetKind::SupportFile, None, None)));
        }
        return Ok(None);
    }

    if logical_path.starts_with("tests/baselines/reference/")
        || logical_path.starts_with("testdata/baselines/reference/")
    {
        let facet = baseline_facet_from_path(logical_path);
        return Ok(Some((AssetKind::BaselineFacet, None, facet)));
    }

    if logical_path == "testdata/submoduleAccepted.txt"
        || logical_path == "testdata/submoduleTriaged.txt"
    {
        return Ok(Some((AssetKind::DifferenceRecord, None, None)));
    }

    let basename = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    let base_upper = basename.to_ascii_uppercase();
    if base_upper.starts_with("LICENSE") || base_upper.starts_with("NOTICE") {
        return Ok(Some((AssetKind::LicenseNotice, None, None)));
    }

    Ok(None)
}

fn baseline_facet_from_path(path: &str) -> Option<Facet> {
    if path.ends_with(".errors.txt") {
        Some(Facet::Diagnostics)
    } else if path.ends_with(".types") {
        Some(Facet::Types)
    } else if path.ends_with(".symbols") {
        Some(Facet::Symbols)
    } else if path.ends_with(".d.ts") {
        Some(Facet::DtsEmit)
    } else if path.ends_with(".js") {
        Some(Facet::JsEmit)
    } else {
        None
    }
}

/// Walk an extracted suite tree into a deterministic asset map.
pub fn walk_extracted_tree(root: &Path) -> Result<BTreeMap<String, ImportedAsset>> {
    let mut assets = BTreeMap::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = fs::read_dir(&current).map_err(|e| io_err(&current, &e))?;
        let mut children = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            children.push(entry.path());
        }
        children.sort();
        for child in children {
            let meta = fs::symlink_metadata(&child).map_err(|e| io_err(&child, &e))?;
            let rel = child
                .strip_prefix(root)
                .map(|p| p.to_string_lossy().replace('\\', "/"))
                .unwrap_or_default();
            if meta.file_type().is_symlink() {
                if member_looks_allowlisted(&rel) {
                    return Err(VerificationError::new(
                        ErrorCode::ProvenanceMismatch,
                        format!("symlink rejected: `{}`", child.display()),
                    ));
                }
                continue;
            }
            if meta.is_dir() {
                stack.push(child);
                continue;
            }
            if !meta.is_file() {
                continue;
            }
            let Some((kind, partition, facet)) = classify_logical_path(&rel)? else {
                continue;
            };
            let bytes = fs::read(&child).map_err(|e| io_err(&child, &e))?;
            let digest_hex = sha256_hex(&bytes);
            if assets.contains_key(&rel) {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!("duplicate logical path `{rel}`"),
                ));
            }
            assets.insert(
                rel.clone(),
                ImportedAsset {
                    logical_path: rel,
                    kind,
                    digest_hex,
                    bytes,
                    facet,
                    partition,
                },
            );
        }
    }
    Ok(assets)
}

/// Import LICENSE/NOTICE assets from the pinned compiler archive under a `compiler/` prefix.
fn merge_compiler_license_notice(
    assets: &mut BTreeMap<String, ImportedAsset>,
    compiler_root: &Path,
) -> Result<()> {
    reject_extracted_symlinks(compiler_root)?;
    let mut stack = vec![compiler_root.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = fs::read_dir(&current).map_err(|e| io_err(&current, &e))?;
        let mut children = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            children.push(entry.path());
        }
        children.sort();
        for child in children {
            let meta = fs::symlink_metadata(&child).map_err(|e| io_err(&child, &e))?;
            if meta.file_type().is_symlink() {
                let basename = child
                    .file_name()
                    .and_then(|name| name.to_str())
                    .unwrap_or("")
                    .to_ascii_uppercase();
                if basename.starts_with("LICENSE") || basename.starts_with("NOTICE") {
                    return Err(VerificationError::new(
                        ErrorCode::ProvenanceMismatch,
                        format!("symlink rejected: `{}`", child.display()),
                    ));
                }
                continue;
            }
            if meta.is_dir() {
                stack.push(child);
                continue;
            }
            if !meta.is_file() {
                continue;
            }
            let basename = child
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("")
                .to_ascii_uppercase();
            if !(basename.starts_with("LICENSE") || basename.starts_with("NOTICE")) {
                continue;
            }
            let rel = child
                .strip_prefix(compiler_root)
                .map_err(|_| {
                    VerificationError::new(
                        ErrorCode::Schema,
                        format!("path escapes compiler root: `{}`", child.display()),
                    )
                })?
                .to_string_lossy()
                .replace('\\', "/");
            let logical = format!("compiler/{rel}");
            let Some((kind, partition, facet)) = classify_logical_path(&logical)? else {
                continue;
            };
            if !matches!(kind, AssetKind::LicenseNotice) {
                continue;
            }
            let bytes = fs::read(&child).map_err(|e| io_err(&child, &e))?;
            let digest_hex = sha256_hex(&bytes);
            if assets.contains_key(&logical) {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!("duplicate logical path `{logical}`"),
                ));
            }
            assets.insert(
                logical.clone(),
                ImportedAsset {
                    logical_path: logical,
                    kind,
                    digest_hex,
                    bytes,
                    facet,
                    partition,
                },
            );
        }
    }
    Ok(())
}

fn materialize_snapshot(
    snapshot_root: &Path,
    pins: &OraclePins,
    assets: &BTreeMap<String, ImportedAsset>,
) -> Result<SuiteSnapshot> {
    let cases_dir = snapshot_root.join("cases");
    let baselines_dir = snapshot_root.join("baselines");
    let notice_dir = snapshot_root.join("oracle/NOTICE");
    fs::create_dir_all(&cases_dir).map_err(|e| io_err(&cases_dir, &e))?;
    fs::create_dir_all(&baselines_dir).map_err(|e| io_err(&baselines_dir, &e))?;
    fs::create_dir_all(&notice_dir).map_err(|e| io_err(&notice_dir, &e))?;

    let mut index = SuiteIndex {
        entries: BTreeMap::new(),
    };

    for asset in assets.values() {
        match asset.kind {
            AssetKind::CaseInput | AssetKind::SupportFile => {
                store_blob(&cases_dir, &asset.digest_hex, &asset.bytes)?;
            }
            AssetKind::BaselineFacet => {
                store_blob(&baselines_dir, &asset.digest_hex, &asset.bytes)?;
            }
            AssetKind::DifferenceRecord => {
                store_blob(&baselines_dir, &asset.digest_hex, &asset.bytes)?;
            }
            AssetKind::LicenseNotice => {
                let dest = notice_dir.join(asset.logical_path.replace('/', "__"));
                if let Some(parent) = dest.parent() {
                    fs::create_dir_all(parent).map_err(|e| io_err(parent, &e))?;
                }
                write_then_verify(&dest, &asset.bytes)?;
            }
        }
        index.entries.insert(
            asset.logical_path.clone(),
            IndexEntry {
                logical_path: asset.logical_path.clone(),
                sha256: asset.digest_hex.clone(),
                asset_kind: asset.kind,
                facet: asset.facet,
                partition: asset.partition,
            },
        );
    }

    let ledger = build_provisional_ledger(pins, &index)?;
    let pin_bytes = canonicalize_json_bytes(&PinDocument::from_pins(pins))?;
    let index_bytes = canonicalize_json_bytes(&index)?;
    let ledger_bytes = TsLedgerWriter::to_vec(&ledger)?;

    let oracle_dir = snapshot_root.join("oracle");
    fs::create_dir_all(&oracle_dir).map_err(|e| io_err(&oracle_dir, &e))?;
    write_then_verify(&oracle_dir.join("pin.json"), &pin_bytes)?;
    write_then_verify(&snapshot_root.join("index.json"), &index_bytes)?;
    write_then_verify(&snapshot_root.join("ledger.json"), &ledger_bytes)?;

    let digest = sha256_hex_concat(&[&pin_bytes, &index_bytes, &ledger_bytes]);
    write_then_verify(
        &snapshot_root.join("snapshot.sha256"),
        format!("{digest}\n").as_bytes(),
    )?;

    Ok(SuiteSnapshot {
        root: snapshot_root.to_path_buf(),
        digest,
        index,
        ledger,
    })
}

pub(super) fn index_content_digest(index: &SuiteIndex) -> String {
    let mut hasher = Sha256::new();
    for (path, entry) in &index.entries {
        hasher.update(path.as_bytes());
        hasher.update(b"|");
        hasher.update(entry.sha256.as_bytes());
        hasher.update(b"\n");
    }
    hex_encode(hasher.finalize())
}

/// Re-verify blob digests and `snapshot.sha256`.
pub fn verify_snapshot(snapshot_root: &Path) -> Result<VerifiedSuite> {
    let snapshot_root =
        fs::canonicalize(snapshot_root).map_err(|error| io_err(snapshot_root, &error))?;
    let (pin_bytes, index_bytes, ledger_bytes) = read_snapshot_metadata_bytes(&snapshot_root)?;
    let expected = sha256_hex_concat(&[&pin_bytes, &index_bytes, &ledger_bytes]);
    let recorded = fs::read_to_string(snapshot_root.join("snapshot.sha256"))
        .map_err(|error| io_err(&snapshot_root.join("snapshot.sha256"), &error))?;
    let recorded = recorded.trim();
    if recorded != expected {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            format!("snapshot.sha256 mismatch: recorded `{recorded}`, computed `{expected}`"),
        ));
    }

    let (index, ledger) = parse_snapshot_metadata(&pin_bytes, &index_bytes, &ledger_bytes)?;
    for entry in index.entries.values() {
        if matches!(entry.asset_kind, AssetKind::LicenseNotice) {
            continue;
        }
        let _ = read_verified_index_entry(&snapshot_root, entry)?;
    }

    Ok(VerifiedSuite {
        snapshot: SuiteSnapshot {
            root: snapshot_root,
            digest: expected,
            index,
            ledger,
        },
        pin_bytes,
        index_bytes,
        ledger_bytes,
    })
}

/// Load a compiler snapshot from retained metadata only. Never walks the blob tree.
pub fn load_bound_compiler_snapshot(
    snapshot_root: &Path,
    binding: &LaneBinding,
) -> Result<CompilerSnapshot> {
    binding.validate()?;
    if !binding.has_snapshot() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "compiler worker request is missing snapshot binding",
        ));
    }
    let snapshot_root =
        fs::canonicalize(snapshot_root).map_err(|error| io_err(snapshot_root, &error))?;
    let (pin_bytes, index_bytes, ledger_bytes) = read_snapshot_metadata_bytes(&snapshot_root)?;
    binding.verify_snapshot(
        COMPILER_CATALOG,
        &snapshot_root,
        &pin_bytes,
        &index_bytes,
        &ledger_bytes,
    )?;
    verify_pin_document_bytes(&pin_bytes)?;
    let index: SuiteIndex = serde_json::from_slice(&index_bytes)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("index.json: {error}")))?;
    validate_suite_index(&index)?;
    Ok(CompilerSnapshot {
        root: snapshot_root,
        index,
    })
}

/// Read one selected snapshot asset once and consume only those digest-checked bytes.
pub fn read_verified_asset(snapshot: &SuiteSnapshot, logical_path: &str) -> Result<Vec<u8>> {
    read_verified_snapshot_asset(snapshot, logical_path)
}

pub(crate) fn read_verified_snapshot_asset(
    snapshot: &(impl SnapshotAssets + ?Sized),
    logical_path: &str,
) -> Result<Vec<u8>> {
    if !is_safe_logical_path(logical_path) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unsafe snapshot logical path `{logical_path}`"),
        ));
    }
    let entry = snapshot.index().entries.get(logical_path).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("snapshot has no asset `{logical_path}`"),
        )
    })?;
    if entry.logical_path != logical_path {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "index key `{logical_path}` does not match entry path `{}`",
                entry.logical_path
            ),
        ));
    }
    read_verified_index_entry(snapshot.root(), entry)
}

fn read_snapshot_metadata_bytes(snapshot_root: &Path) -> Result<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    let pin_path = snapshot_root.join("oracle/pin.json");
    let index_path = snapshot_root.join("index.json");
    let ledger_path = snapshot_root.join("ledger.json");
    let pin_bytes = fs::read(&pin_path).map_err(|error| io_err(&pin_path, &error))?;
    let index_bytes = fs::read(&index_path).map_err(|error| io_err(&index_path, &error))?;
    let ledger_bytes = fs::read(&ledger_path).map_err(|error| io_err(&ledger_path, &error))?;
    Ok((pin_bytes, index_bytes, ledger_bytes))
}

fn parse_snapshot_metadata(
    pin_bytes: &[u8],
    index_bytes: &[u8],
    ledger_bytes: &[u8],
) -> Result<(SuiteIndex, crate::ts_ledger::TsLedger)> {
    verify_pin_document_bytes(pin_bytes)?;
    let index: SuiteIndex = serde_json::from_slice(index_bytes)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("index.json: {error}")))?;
    validate_suite_index(&index)?;
    let ledger = TsLedgerReader::from_slice(ledger_bytes)?;
    Ok((index, ledger))
}

fn validate_suite_index(index: &SuiteIndex) -> Result<()> {
    for (path, entry) in &index.entries {
        if path != &entry.logical_path {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "index key `{path}` does not match entry path `{}`",
                    entry.logical_path
                ),
            ));
        }
        if !is_safe_logical_path(path) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("unsafe snapshot logical path `{path}`"),
            ));
        }
        crate::shard::require_sha256("index entry digest", &entry.sha256)?;
    }
    Ok(())
}

fn read_verified_index_entry(snapshot_root: &Path, entry: &IndexEntry) -> Result<Vec<u8>> {
    crate::shard::require_sha256("index entry digest", &entry.sha256)?;
    if entry.sha256.contains('/') || entry.sha256.contains('\\') {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "index digest for `{}` is not a path-safe blob name",
                entry.logical_path
            ),
        ));
    }
    let dir = match entry.asset_kind {
        AssetKind::CaseInput | AssetKind::SupportFile => snapshot_root.join("cases"),
        AssetKind::BaselineFacet | AssetKind::DifferenceRecord => snapshot_root.join("baselines"),
        AssetKind::LicenseNotice => {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "license asset `{}` is not a case or baseline blob",
                    entry.logical_path
                ),
            ));
        }
    };
    let path = dir.join(&entry.sha256);
    let bytes = fs::read(&path).map_err(|error| io_err(&path, &error))?;
    let actual = sha256_hex(&bytes);
    if actual != entry.sha256 {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "blob digest mismatch for `{}`: index `{}`, actual `{actual}`",
                entry.logical_path, entry.sha256
            ),
        ));
    }
    Ok(bytes)
}

pub(super) fn verify_pin_document(path: &Path) -> Result<()> {
    let bytes = fs::read(path).map_err(|e| io_err(path, &e))?;
    verify_pin_document_bytes(&bytes)
}

fn verify_pin_document_bytes(bytes: &[u8]) -> Result<()> {
    let doc: PinDocument = serde_json::from_slice(bytes)
        .map_err(|e| VerificationError::new(ErrorCode::Json, format!("pin.json: {e}")))?;
    let expected = PinDocument::expected();
    if doc.npm_specifier != expected.npm_specifier
        || doc.npm_integrity != expected.npm_integrity
        || doc.compiler_repository != expected.compiler_repository
        || doc.compiler_commit != expected.compiler_commit
        || doc.compiler_tag != expected.compiler_tag
        || doc.suite_repository != expected.suite_repository
        || doc.suite_commit != expected.suite_commit
    {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            "oracle/pin.json does not match pinned TypeScript 7.0.2 identity",
        ));
    }
    // Touch constants so pin drift against module constants is obvious to readers.
    let _ = (
        NPM_SPECIFIER,
        NPM_INTEGRITY,
        COMPILER_REPOSITORY,
        COMPILER_COMMIT,
        COMPILER_TAG,
        SUITE_REPOSITORY,
        SUITE_COMMIT,
    );
    Ok(())
}

pub(super) fn case_inputs_from_index(index: &SuiteIndex) -> BTreeSet<String> {
    index
        .entries
        .values()
        .filter(|entry| matches!(entry.asset_kind, AssetKind::CaseInput))
        .map(|entry| entry.logical_path.clone())
        .collect()
}

fn store_blob(dir: &Path, digest_hex: &str, bytes: &[u8]) -> Result<()> {
    let path = dir.join(digest_hex);
    if path.exists() {
        let existing = fs::read(&path).map_err(|e| io_err(&path, &e))?;
        if existing != bytes {
            return Err(VerificationError::new(
                ErrorCode::Digest,
                format!("content mismatch for blob `{digest_hex}`"),
            ));
        }
        return Ok(());
    }
    write_then_verify(&path, bytes)
}

pub(super) fn write_then_verify(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| io_err(parent, &e))?;
    }
    fs::write(path, bytes).map_err(|e| io_err(path, &e))?;
    let read_back = fs::read(path).map_err(|e| io_err(path, &e))?;
    if read_back != bytes {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!("write-then-verify failed for `{}`", path.display()),
        ));
    }
    Ok(())
}

pub(crate) fn fetch_archive(url: &str, expected_digest: &str, cache_dir: &Path) -> Result<PathBuf> {
    let cache_path = cache_dir.join(format!("{expected_digest}.tar.gz"));
    if cache_path.exists() {
        let bytes = fs::read(&cache_path).map_err(|e| io_err(&cache_path, &e))?;
        let actual = sha256_hex(&bytes);
        if actual == expected_digest {
            return Ok(cache_path);
        }
        fs::remove_file(&cache_path).map_err(|e| io_err(&cache_path, &e))?;
    }

    let status = Command::new("curl")
        .args(["-fsSL", "--output"])
        .arg(&cache_path)
        .arg(url)
        .status()
        .map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                VerificationError::new(ErrorCode::ToolMissing, "curl is not available on PATH")
            } else {
                VerificationError::new(
                    ErrorCode::ToolFailed,
                    format!("failed to spawn curl: {error}"),
                )
            }
        })?;
    if !status.success() {
        let _ = fs::remove_file(&cache_path);
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("curl failed fetching `{url}` with {status}"),
        ));
    }
    let bytes = fs::read(&cache_path).map_err(|e| io_err(&cache_path, &e))?;
    let actual = sha256_hex(&bytes);
    if actual != expected_digest {
        let _ = fs::remove_file(&cache_path);
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "archive digest mismatch for `{url}`: expected `{expected_digest}`, got `{actual}`"
            ),
        ));
    }
    Ok(cache_path)
}

pub(crate) fn extract_archive(archive: &Path) -> Result<TempDir> {
    // Each archive extracts into its own temp dir. Without a per-archive
    // discriminator the suite and compiler extractions collide on the same
    // path (same prefix + pid), and the second extraction wipes the first.
    let discriminator = &sha256_hex(archive.to_string_lossy().as_bytes())[..8];
    let temp = TempDir::new(&format!("bamts-suite-extract-{discriminator}"))?;
    let listed = Command::new("tar")
        .args(["-tzf"])
        .arg(archive)
        .output()
        .map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                VerificationError::new(ErrorCode::ToolMissing, "tar is not available on PATH")
            } else {
                VerificationError::new(
                    ErrorCode::ToolFailed,
                    format!("failed to spawn tar: {error}"),
                )
            }
        })?;
    if !listed.status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "tar -tzf failed: {}",
                String::from_utf8_lossy(&listed.stderr)
            ),
        ));
    }
    let listing = String::from_utf8_lossy(&listed.stdout);
    for member in listing.lines() {
        reject_tar_member(member)?;
    }

    let verbose = Command::new("tar")
        .args(["-tvzf"])
        .arg(archive)
        .output()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("failed to spawn tar verbose list: {error}"),
            )
        })?;
    if !verbose.status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "tar -tvzf failed: {}",
                String::from_utf8_lossy(&verbose.stderr)
            ),
        ));
    }
    let verbose_listing = String::from_utf8_lossy(&verbose.stdout);
    for line in verbose_listing.lines() {
        reject_tar_verbose_line(line)?;
    }

    let status = Command::new("tar")
        .args([
            "-xzf",
            archive.to_str().ok_or_else(|| {
                VerificationError::new(ErrorCode::Io, "archive path is not UTF-8")
            })?,
            "--no-same-owner",
            "--no-same-permissions",
            "-C",
        ])
        .arg(temp.path())
        .status()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("failed to spawn tar extract: {error}"),
            )
        })?;
    if !status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("tar extract failed with {status}"),
        ));
    }
    reject_extracted_symlinks(temp.path())?;
    Ok(temp)
}

fn reject_tar_member(member: &str) -> Result<()> {
    if member.is_empty() {
        return Ok(());
    }
    if member.starts_with('/') || member.contains("://") {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            format!("archive member absolute path rejected: `{member}`"),
        ));
    }
    for part in member.split('/') {
        if part == ".." {
            return Err(VerificationError::new(
                ErrorCode::ProvenanceMismatch,
                format!("archive member traversal rejected: `{member}`"),
            ));
        }
    }
    Ok(())
}

pub(super) fn reject_tar_verbose_line(line: &str) -> Result<()> {
    let trimmed = line.trim_start();
    if trimmed.is_empty() {
        return Ok(());
    }
    if matches!(trimmed.chars().next(), Some('-') | Some('d')) {
        return Ok(());
    }
    Err(VerificationError::new(
        ErrorCode::ProvenanceMismatch,
        format!("archive member link/special type rejected: `{line}`"),
    ))
}

fn member_looks_allowlisted(member: &str) -> bool {
    let lower = member.to_ascii_lowercase().replace('\\', "/");
    if lower.contains("tests/cases/")
        || lower.contains("tests/baselines/")
        || lower.contains("testdata/")
    {
        return true;
    }
    let base = Path::new(&lower)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    base.starts_with("license") || base.starts_with("notice")
}

fn reject_extracted_symlinks(root: &Path) -> Result<()> {
    // Do not fail the whole archive on incidental symlinks outside imported
    // paths; walk/import refuse to follow or read them.
    let mut stack = vec![root.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = match fs::read_dir(&current) {
            Ok(entries) => entries,
            Err(error) => return Err(io_err(&current, &error)),
        };
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            let path = entry.path();
            let meta = fs::symlink_metadata(&path).map_err(|e| io_err(&path, &e))?;
            if meta.file_type().is_symlink() {
                return Err(VerificationError::new(
                    ErrorCode::ProvenanceMismatch,
                    format!("extracted symlink rejected: `{}`", path.display()),
                ));
            }
            if meta.is_dir() {
                stack.push(path);
            }
        }
    }
    Ok(())
}

pub(crate) fn single_archive_root(extract_root: &Path) -> Result<PathBuf> {
    let mut dirs = Vec::new();
    for entry in fs::read_dir(extract_root).map_err(|e| io_err(extract_root, &e))? {
        let entry = entry.map_err(|e| io_err(extract_root, &e))?;
        let meta = fs::symlink_metadata(entry.path()).map_err(|e| io_err(&entry.path(), &e))?;
        if meta.is_dir() {
            dirs.push(entry.path());
        }
    }
    if dirs.len() != 1 {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            format!(
                "expected exactly one archive root under `{}`, found {}",
                extract_root.display(),
                dirs.len()
            ),
        ));
    }
    Ok(dirs.remove(0))
}

pub(crate) struct TempDir {
    path: PathBuf,
}

impl TempDir {
    pub(crate) fn new(prefix: &str) -> Result<Self> {
        static TEMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "{prefix}-{}-{}",
            std::process::id(),
            TEMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        if path.exists() {
            fs::remove_dir_all(&path).map_err(|e| io_err(&path, &e))?;
        }
        fs::create_dir_all(&path).map_err(|e| io_err(&path, &e))?;
        Ok(Self { path })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn canonicalize_json_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    let mut json = serde_json::to_value(value)
        .map_err(|e| VerificationError::new(ErrorCode::Json, format!("{e}")))?;
    sort_json_keys(&mut json);
    let text = serde_json::to_string_pretty(&json)
        .map_err(|e| VerificationError::new(ErrorCode::Json, format!("{e}")))?;
    let canonical = text
        .lines()
        .map(|line| line.trim_end().replace('\r', ""))
        .collect::<Vec<_>>()
        .join("\n");
    Ok(canonical.into_bytes())
}

fn sort_json_keys(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Object(map) => {
            map.sort_keys();
            for member in map.values_mut() {
                sort_json_keys(member);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                sort_json_keys(item);
            }
        }
        _ => {}
    }
}

pub(super) fn sha256_hex_concat(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hex_encode(hasher.finalize())
}

fn hex_encode(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

pub(super) fn io_err(path: &Path, error: &io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

/// Materialize from an extracted tree without network (test seam).
pub fn materialize_from_extracted(
    snapshot_root: &Path,
    extracted_suite_root: &Path,
) -> Result<SuiteSnapshot> {
    sync_suite(&SyncOptions {
        verify_pin: true,
        write_snapshot: true,
        workspace_root: PathBuf::from("."),
        snapshot_root: snapshot_root.to_path_buf(),
        extracted_suite_root: Some(extracted_suite_root.to_path_buf()),
    })
}

pub(super) fn compiler_snapshot_input(case: &str) -> Option<&str> {
    let (input, partition) = if let Some(input) = case.strip_prefix("compiler/") {
        (input, "tests/cases/compiler/")
    } else {
        (
            case.strip_prefix("conformance/")?,
            "tests/cases/conformance/",
        )
    };
    if !input.starts_with(partition) || !is_safe_logical_path(input) {
        return None;
    }
    Some(input)
}

pub(super) fn is_safe_logical_path(path: &str) -> bool {
    !path.is_empty()
        && !path.starts_with('/')
        && path
            .split('/')
            .all(|part| !part.is_empty() && part != "." && part != "..")
}

pub(super) fn split_configuration(configuration: &str) -> Option<(&str, &str)> {
    let (variant, observable) = configuration.split_once('#')?;
    if variant.is_empty() || observable.is_empty() || observable.contains('#') {
        None
    } else {
        Some((variant, observable))
    }
}

pub(super) fn observable_kind(name: &str) -> Option<ObservableKind> {
    match name {
        "parse" => Some(ObservableKind::Parse),
        "diagnostics" => Some(ObservableKind::Diagnostics),
        "javascript" => Some(ObservableKind::JavaScript),
        "declaration" => Some(ObservableKind::Declaration),
        "source-map" => Some(ObservableKind::SourceMap),
        "trace" => Some(ObservableKind::Trace),
        "build-info" => Some(ObservableKind::BuildInfo),
        "types" => Some(ObservableKind::Types),
        "symbols" => Some(ObservableKind::Symbols),
        "runtime" => Some(ObservableKind::Runtime),
        _ => None,
    }
}

pub(super) fn read_snapshot_case(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> Result<String> {
    let bytes = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)?;
    Ok(decode_case_source(&bytes))
}
