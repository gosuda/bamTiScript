//! Pinned Unicode emoji source materialization and deterministic table generation.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    ErrorCode, VerificationError,
    schema::{SourcePin, SourcesDocument},
    source_fetch::ArchiveBackend,
};

const SOURCES_LEDGER: &str = "vendor/sources.toml";
const GENERATED_TABLE: &str =
    "crates/bamts-runtime/src/intrinsics/builtins/regexp_v/emoji_tables.rs";
const IDENTITY_FILE: &str = ".bamti-source.json";
const GENERATOR_VERSION: &str = "bamts-verification unicode/v1";
const EMOJI_SEQUENCES: &str = "unicode-emoji-sequences";
const EMOJI_ZWJ_SEQUENCES: &str = "unicode-emoji-zwj-sequences";
const RAW_SOURCES: [(&str, &str); 2] = [
    (EMOJI_SEQUENCES, "emoji-sequences.txt"),
    (EMOJI_ZWJ_SEQUENCES, "emoji-zwj-sequences.txt"),
];
const PROPERTY_NAMES: [&str; 6] = [
    "Basic_Emoji",
    "Emoji_Keycap_Sequence",
    "RGI_Emoji_Flag_Sequence",
    "RGI_Emoji_Modifier_Sequence",
    "RGI_Emoji_Tag_Sequence",
    "RGI_Emoji_ZWJ_Sequence",
];
static NEXT_STAGING: AtomicU64 = AtomicU64::new(0);

pub type UnicodeResult<T> = std::result::Result<T, UnicodeError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnicodeErrorKind {
    Io,
    Ledger,
    Digest,
    MalformedRow,
    Invariant,
    Drift,
    Source,
}

#[derive(Debug)]
pub struct UnicodeError {
    kind: UnicodeErrorKind,
    detail: String,
}

impl UnicodeError {
    fn new(kind: UnicodeErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    pub const fn kind(&self) -> UnicodeErrorKind {
        self.kind
    }
}

impl fmt::Display for UnicodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "unicode {:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for UnicodeError {}

impl From<UnicodeError> for VerificationError {
    fn from(error: UnicodeError) -> Self {
        let code = match error.kind {
            UnicodeErrorKind::Io => ErrorCode::Io,
            UnicodeErrorKind::Digest => ErrorCode::Digest,
            UnicodeErrorKind::Drift | UnicodeErrorKind::Invariant => ErrorCode::SetMismatch,
            UnicodeErrorKind::Ledger | UnicodeErrorKind::MalformedRow => ErrorCode::Schema,
            UnicodeErrorKind::Source => ErrorCode::ToolFailed,
        };
        VerificationError::new(code, error.to_string())
    }
}

/// A pinned raw file from the source ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawFile {
    pub name: String,
    pub pin: String,
    pub url: String,
    pub digest: String,
    pub file_name: String,
}

impl RawFile {
    pub fn new(source: &SourcePin, file_name: impl Into<String>) -> UnicodeResult<Self> {
        let file_name = file_name.into();
        if source.digest_algorithm != "sha256"
            || source.digest.len() != 64
            || !source
                .digest
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
        {
            return Err(UnicodeError::new(
                UnicodeErrorKind::Ledger,
                format!(
                    "source `{}` requires a lowercase sha256 digest",
                    source.name
                ),
            ));
        }
        if source.name.is_empty()
            || source.pin.is_empty()
            || source.url.is_empty()
            || file_name.is_empty()
            || Path::new(&file_name).components().count() != 1
        {
            return Err(UnicodeError::new(
                UnicodeErrorKind::Ledger,
                format!("source `{}` has an invalid raw-file identity", source.name),
            ));
        }
        Ok(Self {
            name: source.name.clone(),
            pin: source.pin.clone(),
            url: source.url.clone(),
            digest: source.digest.clone(),
            file_name,
        })
    }

    pub fn directory(&self, root: &Path) -> PathBuf {
        root.join("target/authority").join(&self.name)
    }

    pub fn path(&self, root: &Path) -> PathBuf {
        self.directory(root).join(&self.file_name)
    }

    /// Downloads, authenticates, and atomically publishes this raw file and receipt.
    pub fn materialize<B: ArchiveBackend>(
        &self,
        root: &Path,
        backend: &B,
    ) -> UnicodeResult<PathBuf> {
        let destination = self.directory(root);
        if destination.exists() {
            self.verify(root)?;
            return Ok(self.path(root));
        }

        let parent = destination.parent().ok_or_else(|| {
            UnicodeError::new(UnicodeErrorKind::Io, "raw source has no parent directory")
        })?;
        fs::create_dir_all(parent).map_err(|error| io_error(parent, error))?;
        let serial = NEXT_STAGING.fetch_add(1, Ordering::Relaxed);
        let staging = parent.join(format!(
            ".{}-{}-{serial}.tmp",
            self.name,
            std::process::id()
        ));
        if staging.exists() {
            fs::remove_dir_all(&staging).map_err(|error| io_error(&staging, error))?;
        }
        fs::create_dir(&staging).map_err(|error| io_error(&staging, error))?;
        let staged_file = staging.join(&self.file_name);

        let result = (|| {
            backend
                .fetch(&self.url, &staged_file)
                .map_err(|error| UnicodeError::new(UnicodeErrorKind::Source, error.to_string()))?;
            verify_digest(&staged_file, &self.digest, &self.name)?;
            let receipt = RawIdentity::from_raw(self);
            write_json(&staging.join(IDENTITY_FILE), &receipt)?;
            fs::rename(&staging, &destination).map_err(|error| io_error(&destination, error))?;
            Ok(self.path(root))
        })();
        if result.is_err() && staging.exists() {
            let _ = fs::remove_dir_all(&staging);
        }
        result
    }

    /// Authenticates both the identity receipt and the materialized bytes.
    pub fn verify(&self, root: &Path) -> UnicodeResult<()> {
        let directory = self.directory(root);
        let metadata =
            fs::symlink_metadata(&directory).map_err(|error| io_error(&directory, error))?;
        if !metadata.is_dir() || metadata.file_type().is_symlink() {
            return Err(UnicodeError::new(
                UnicodeErrorKind::Io,
                format!("{} is not a raw source directory", directory.display()),
            ));
        }
        let receipt_path = directory.join(IDENTITY_FILE);
        let receipt_metadata =
            fs::symlink_metadata(&receipt_path).map_err(|error| io_error(&receipt_path, error))?;
        if !receipt_metadata.is_file() || receipt_metadata.file_type().is_symlink() {
            return Err(UnicodeError::new(
                UnicodeErrorKind::Ledger,
                format!(
                    "{} is not a regular identity receipt",
                    receipt_path.display()
                ),
            ));
        }
        let receipt_bytes =
            fs::read(&receipt_path).map_err(|error| io_error(&receipt_path, error))?;
        let receipt: RawIdentity = serde_json::from_slice(&receipt_bytes).map_err(|error| {
            UnicodeError::new(
                UnicodeErrorKind::Ledger,
                format!("{}: {error}", receipt_path.display()),
            )
        })?;
        if receipt != RawIdentity::from_raw(self) {
            return Err(UnicodeError::new(
                UnicodeErrorKind::Ledger,
                format!("{} does not match its source pin", receipt_path.display()),
            ));
        }
        verify_digest(&self.path(root), &self.digest, &self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawIdentity {
    schema: String,
    name: String,
    pin: String,
    url: String,
    digest_algorithm: String,
    digest: String,
    file: String,
}

impl RawIdentity {
    fn from_raw(raw: &RawFile) -> Self {
        Self {
            schema: "bamti.raw-file/v1".to_owned(),
            name: raw.name.clone(),
            pin: raw.pin.clone(),
            url: raw.url.clone(),
            digest_algorithm: "sha256".to_owned(),
            digest: raw.digest.clone(),
            file: raw.file_name.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnicodeReport {
    pub source_count: usize,
    pub destination: PathBuf,
}

pub fn fetch<B: ArchiveBackend>(root: &Path, backend: &B) -> UnicodeResult<UnicodeReport> {
    let sources = raw_files(root)?;
    for source in &sources {
        source.materialize(root, backend)?;
    }
    Ok(UnicodeReport {
        source_count: sources.len(),
        destination: root.join("target/authority"),
    })
}

pub fn emit(root: &Path, destination: Option<&Path>) -> UnicodeResult<UnicodeReport> {
    let destination = destination
        .map(|path| {
            if path.is_absolute() {
                path.to_owned()
            } else {
                root.join(path)
            }
        })
        .unwrap_or_else(|| root.join(GENERATED_TABLE));
    let bytes = generate(root)?;
    atomic_write(&destination, &bytes)?;
    Ok(UnicodeReport {
        source_count: RAW_SOURCES.len(),
        destination,
    })
}

pub fn verify(root: &Path) -> UnicodeResult<UnicodeReport> {
    let destination = root.join(GENERATED_TABLE);
    let expected = fs::read(&destination).map_err(|error| io_error(&destination, error))?;
    let actual = generate(root)?;
    if actual != expected {
        return Err(UnicodeError::new(
            UnicodeErrorKind::Drift,
            format!(
                "{} differs from deterministic Unicode generation",
                destination.display()
            ),
        ));
    }
    Ok(UnicodeReport {
        source_count: RAW_SOURCES.len(),
        destination,
    })
}

pub fn generate(root: &Path) -> UnicodeResult<Vec<u8>> {
    let sources = raw_files(root)?;
    let mut properties = empty_properties();
    let mut all_rows = PropertyData::default();

    for source in &sources {
        source.verify(root)?;
        let path = source.path(root);
        let bytes = fs::read(&path).map_err(|error| io_error(&path, error))?;
        let text = std::str::from_utf8(&bytes).map_err(|error| {
            UnicodeError::new(
                UnicodeErrorKind::MalformedRow,
                format!("{} is not UTF-8: {error}", path.display()),
            )
        })?;
        parse_source(&path, text, &mut properties, &mut all_rows)?;
    }

    for property in properties.values_mut() {
        property.normalize();
    }
    all_rows.normalize();
    let mut union = PropertyData::default();
    for property in properties.values() {
        union.extend(property);
    }
    union.normalize();
    if union != all_rows {
        return Err(UnicodeError::new(
            UnicodeErrorKind::Invariant,
            "RGI_Emoji is not the union of its six string properties",
        ));
    }

    render(&sources, &properties, &union)
}

fn raw_files(root: &Path) -> UnicodeResult<Vec<RawFile>> {
    let ledger_path = root.join(SOURCES_LEDGER);
    let bytes = fs::read(&ledger_path).map_err(|error| io_error(&ledger_path, error))?;
    let text = std::str::from_utf8(&bytes).map_err(|error| {
        UnicodeError::new(
            UnicodeErrorKind::Ledger,
            format!("{} is not UTF-8: {error}", ledger_path.display()),
        )
    })?;
    let document: SourcesDocument = toml::from_str(text).map_err(|error| {
        UnicodeError::new(
            UnicodeErrorKind::Ledger,
            format!("{}: {error}", ledger_path.display()),
        )
    })?;
    if document.schema != "bamti.sources/v1" {
        return Err(UnicodeError::new(
            UnicodeErrorKind::Ledger,
            format!("{} has unsupported schema", ledger_path.display()),
        ));
    }
    let mut by_name = BTreeMap::new();
    for source in document.source {
        let name = source.name.clone();
        if by_name.insert(name.clone(), source).is_some() {
            return Err(UnicodeError::new(
                UnicodeErrorKind::Ledger,
                format!("duplicate source `{name}`"),
            ));
        }
    }
    RAW_SOURCES
        .iter()
        .map(|(name, file_name)| {
            let pin = by_name.get(*name).ok_or_else(|| {
                UnicodeError::new(UnicodeErrorKind::Ledger, format!("missing source `{name}`"))
            })?;
            RawFile::new(pin, *file_name)
        })
        .collect()
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct PropertyData {
    points: Vec<(u32, u32)>,
    strings: BTreeSet<Vec<u32>>,
}

impl PropertyData {
    fn extend(&mut self, other: &Self) {
        self.points.extend_from_slice(&other.points);
        self.strings.extend(other.strings.iter().cloned());
    }

    fn normalize(&mut self) {
        self.points.sort_unstable();
        let mut merged: Vec<(u32, u32)> = Vec::with_capacity(self.points.len());
        for (start, end) in self.points.drain(..) {
            if let Some((_, previous_end)) = merged.last_mut()
                && start <= previous_end.saturating_add(1)
            {
                *previous_end = (*previous_end).max(end);
            } else {
                merged.push((start, end));
            }
        }
        self.points = merged;
    }
}

fn empty_properties() -> BTreeMap<&'static str, PropertyData> {
    PROPERTY_NAMES
        .into_iter()
        .map(|name| (name, PropertyData::default()))
        .collect()
}

fn parse_source(
    path: &Path,
    text: &str,
    properties: &mut BTreeMap<&'static str, PropertyData>,
    all_rows: &mut PropertyData,
) -> UnicodeResult<()> {
    for (index, original) in text.lines().enumerate() {
        let row = original.split('#').next().unwrap_or_default().trim();
        if row.is_empty() {
            continue;
        }
        let mut fields = row.split(';').map(str::trim);
        let code_points = fields.next().unwrap_or_default();
        let property_name = fields.next().unwrap_or_default();
        let metadata = fields.next().unwrap_or_default();
        if fields.next().is_some()
            || code_points.is_empty()
            || property_name.is_empty()
            || metadata.is_empty()
        {
            return malformed(
                path,
                index + 1,
                original,
                "expected `code points ; property ; metadata`",
            );
        }
        let property = properties.get_mut(property_name).ok_or_else(|| {
            UnicodeError::new(
                UnicodeErrorKind::MalformedRow,
                format!(
                    "{}:{}: unsupported property `{property_name}` in `{original}`",
                    path.display(),
                    index + 1
                ),
            )
        })?;
        let parsed = parse_code_points(path, index + 1, original, code_points)?;
        match parsed {
            ParsedRow::Range(start, end) => {
                property.points.push((start, end));
                all_rows.points.push((start, end));
            }
            ParsedRow::String(sequence) => {
                property.strings.insert(sequence.clone());
                all_rows.strings.insert(sequence);
            }
        }
    }
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
enum ParsedRow {
    Range(u32, u32),
    String(Vec<u32>),
}

fn parse_code_points(
    path: &Path,
    line: usize,
    original: &str,
    field: &str,
) -> UnicodeResult<ParsedRow> {
    let tokens: Vec<&str> = field.split_whitespace().collect();
    if tokens.is_empty() {
        return malformed(path, line, original, "empty code-point field");
    }
    if tokens.len() == 1 {
        let token = tokens[0];
        if let Some((start, end)) = token.split_once("..") {
            if start.is_empty() || end.is_empty() || end.contains("..") {
                return malformed(path, line, original, "malformed code-point range");
            }
            let start = scalar(path, line, original, start)?;
            let end = scalar(path, line, original, end)?;
            if start > end {
                return malformed(path, line, original, "descending code-point range");
            }
            return Ok(ParsedRow::Range(start, end));
        }
        return Ok(ParsedRow::Range(
            scalar(path, line, original, token)?,
            scalar(path, line, original, token)?,
        ));
    }
    if tokens.iter().any(|token| token.contains("..")) {
        return malformed(
            path,
            line,
            original,
            "ranges cannot appear in a string sequence",
        );
    }
    let sequence = tokens
        .into_iter()
        .map(|token| scalar(path, line, original, token))
        .collect::<UnicodeResult<Vec<_>>>()?;
    Ok(ParsedRow::String(sequence))
}

fn scalar(path: &Path, line: usize, original: &str, token: &str) -> UnicodeResult<u32> {
    let value = u32::from_str_radix(token, 16)
        .map_err(|_| malformed_error(path, line, original, "invalid hexadecimal code point"))?;
    if value > 0x10_FFFF || (0xD800..=0xDFFF).contains(&value) {
        return Err(malformed_error(
            path,
            line,
            original,
            "code point is not a Unicode scalar value",
        ));
    }
    Ok(value)
}

fn malformed<T>(path: &Path, line: usize, original: &str, detail: &str) -> UnicodeResult<T> {
    Err(malformed_error(path, line, original, detail))
}

fn malformed_error(path: &Path, line: usize, original: &str, detail: &str) -> UnicodeError {
    UnicodeError::new(
        UnicodeErrorKind::MalformedRow,
        format!("{}:{line}: {detail}: `{original}`", path.display()),
    )
}

fn render(
    sources: &[RawFile],
    properties: &BTreeMap<&'static str, PropertyData>,
    rgi: &PropertyData,
) -> UnicodeResult<Vec<u8>> {
    let mut output = String::new();
    output.push_str("// @generated by ");
    output.push_str(GENERATOR_VERSION);
    output.push_str("; DO NOT EDIT.\n");
    for source in sources {
        output.push_str(&format!(
            "// Source: {} {} {} sha256={}\n",
            source.name, source.pin, source.url, source.digest
        ));
    }
    output.push_str("\n#[derive(Debug, Clone, Copy)]\n");
    output.push_str("pub(crate) struct StringProperty {\n");
    output.push_str("    pub points: &'static [(u32, u32)],\n");
    output.push_str("    pub strings: &'static [&'static [u32]],\n");
    output.push_str("}\n\n");

    for (name, rust_name) in [
        ("Basic_Emoji", "BASIC_EMOJI"),
        ("Emoji_Keycap_Sequence", "EMOJI_KEYCAP_SEQUENCE"),
        ("RGI_Emoji_Flag_Sequence", "RGI_EMOJI_FLAG_SEQUENCE"),
        ("RGI_Emoji_Modifier_Sequence", "RGI_EMOJI_MODIFIER_SEQUENCE"),
        ("RGI_Emoji_Tag_Sequence", "RGI_EMOJI_TAG_SEQUENCE"),
        ("RGI_Emoji_ZWJ_Sequence", "RGI_EMOJI_ZWJ_SEQUENCE"),
    ] {
        let property = properties.get(name).ok_or_else(|| {
            UnicodeError::new(
                UnicodeErrorKind::Invariant,
                format!("missing generated property `{name}`"),
            )
        })?;
        render_property(&mut output, rust_name, property);
    }
    render_property(&mut output, "RGI_EMOJI", rgi);
    Ok(output.into_bytes())
}

fn render_property(output: &mut String, name: &str, property: &PropertyData) {
    let points_name = format!("{name}_POINTS");
    let strings_name = format!("{name}_STRINGS");
    output.push_str(&format!("static {points_name}: &[(u32, u32)] = &[\n"));
    for (start, end) in &property.points {
        output.push_str(&format!("    (0x{start:X}, 0x{end:X}),\n"));
    }
    output.push_str("];\n");
    output.push_str(&format!("static {strings_name}: &[&[u32]] = &[\n"));
    for sequence in &property.strings {
        output.push_str("    &[");
        for (index, code_point) in sequence.iter().enumerate() {
            if index != 0 {
                output.push_str(", ");
            }
            output.push_str(&format!("0x{code_point:X}"));
        }
        output.push_str("],\n");
    }
    output.push_str("];\n");
    output.push_str(&format!(
        "pub(crate) static {name}: StringProperty = StringProperty {{ points: {points_name}, strings: {strings_name} }};\n\n"
    ));
}

fn verify_digest(path: &Path, expected: &str, name: &str) -> UnicodeResult<()> {
    let bytes = fs::read(path).map_err(|error| io_error(path, error))?;
    let actual = hex(&Sha256::digest(&bytes));
    if actual != expected {
        return Err(UnicodeError::new(
            UnicodeErrorKind::Digest,
            format!("source `{name}` digest mismatch: expected {expected}, found {actual}"),
        ));
    }
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

fn write_json(path: &Path, value: &impl Serialize) -> UnicodeResult<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| {
        UnicodeError::new(
            UnicodeErrorKind::Ledger,
            format!("encode raw identity: {error}"),
        )
    })?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| io_error(path, error))
}

fn atomic_write(destination: &Path, bytes: &[u8]) -> UnicodeResult<()> {
    let parent = destination.parent().ok_or_else(|| {
        UnicodeError::new(UnicodeErrorKind::Io, "generated destination has no parent")
    })?;
    fs::create_dir_all(parent).map_err(|error| io_error(parent, error))?;
    let serial = NEXT_STAGING.fetch_add(1, Ordering::Relaxed);
    let temporary = parent.join(format!(
        ".{}-{}-{serial}.tmp",
        destination
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("emoji-tables"),
        std::process::id()
    ));
    fs::write(&temporary, bytes).map_err(|error| io_error(&temporary, error))?;
    let result = fs::rename(&temporary, destination).map_err(|error| io_error(destination, error));
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

fn io_error(path: &Path, error: std::io::Error) -> UnicodeError {
    UnicodeError::new(UnicodeErrorKind::Io, format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_rows_fail_with_typed_error() {
        let mut properties = empty_properties();
        let mut all = PropertyData::default();
        let error = parse_source(
            Path::new("broken.txt"),
            "1F600..110000 ; Basic_Emoji ; invalid\n",
            &mut properties,
            &mut all,
        )
        .expect_err("out-of-range scalar must fail");
        assert_eq!(error.kind(), UnicodeErrorKind::MalformedRow);
        assert!(error.to_string().contains("broken.txt:1"));
    }

    #[test]
    fn digest_mismatches_fail_with_typed_error() {
        let path =
            std::env::temp_dir().join(format!("bamts-unicode-digest-{}", std::process::id()));
        fs::write(&path, b"not the pinned source").unwrap();
        let error = verify_digest(&path, &"0".repeat(64), "fixture")
            .expect_err("digest mismatch must fail");
        let _ = fs::remove_file(path);
        assert_eq!(error.kind(), UnicodeErrorKind::Digest);
    }

    #[test]
    fn normalization_sorts_deduplicates_and_merges() {
        let mut property = PropertyData {
            points: vec![(3, 4), (1, 1), (2, 3), (8, 8), (8, 8)],
            strings: BTreeSet::from([vec![2, 1], vec![1, 2], vec![1, 2]]),
        };
        property.normalize();
        assert_eq!(property.points, vec![(1, 4), (8, 8)]);
        assert_eq!(
            property.strings.into_iter().collect::<Vec<_>>(),
            vec![vec![1, 2], vec![2, 1]]
        );
    }

    #[test]
    fn generated_shape_has_seven_exact_properties() {
        let sources = vec![
            RawFile {
                name: EMOJI_SEQUENCES.to_owned(),
                pin: "16.0".to_owned(),
                url: "https://example.invalid/emoji-sequences.txt".to_owned(),
                digest: "0".repeat(64),
                file_name: "emoji-sequences.txt".to_owned(),
            },
            RawFile {
                name: EMOJI_ZWJ_SEQUENCES.to_owned(),
                pin: "16.0".to_owned(),
                url: "https://example.invalid/emoji-zwj-sequences.txt".to_owned(),
                digest: "1".repeat(64),
                file_name: "emoji-zwj-sequences.txt".to_owned(),
            },
        ];
        let mut properties = empty_properties();
        for (index, property) in properties.values_mut().enumerate() {
            property.points.push((index as u32, index as u32));
            property.normalize();
        }
        let mut union = PropertyData::default();
        for property in properties.values() {
            union.extend(property);
        }
        union.normalize();
        let generated = String::from_utf8(render(&sources, &properties, &union).unwrap()).unwrap();
        for name in [
            "BASIC_EMOJI",
            "EMOJI_KEYCAP_SEQUENCE",
            "RGI_EMOJI_FLAG_SEQUENCE",
            "RGI_EMOJI_MODIFIER_SEQUENCE",
            "RGI_EMOJI_TAG_SEQUENCE",
            "RGI_EMOJI_ZWJ_SEQUENCE",
            "RGI_EMOJI",
        ] {
            assert_eq!(
                generated
                    .lines()
                    .filter(|line| line.starts_with(&format!("pub(crate) static {name}:")))
                    .count(),
                1
            );
        }
        assert!(!generated.contains("timestamp"));
    }
}
