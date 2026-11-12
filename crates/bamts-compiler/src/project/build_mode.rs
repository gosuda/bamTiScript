use super::references::{ReferenceError, ReferenceGraph, ReferenceNode};
use super::{JsonValue, PathError, ProjectConfig, ProjectRoot};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

/// Options that mirror the `tsc -b` command-line switches.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BuildOptions {
    /// `--clean`: remove the project's declared outputs and build info.
    pub clean: bool,
    /// `--dry`: list what would be done without mutating the file system.
    pub dry_run: bool,
    /// `--force`: ignore incremental state and rebuild every project.
    pub force: bool,
    /// `--verbose`: emit a progress log.
    pub verbose: bool,
    /// stopBuildOnErrors: abandon the whole schedule on the first failure.
    ///
    /// When this is cleared the engine still blocks every transitive dependent
    /// of a failed project, but keeps building projects that do not depend on
    /// it. This is the default behavior.
    pub stop_on_error: bool,
}

/// A failure that prevents the build engine from completing its schedule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    /// A reference-graph error (cycle, composite/declaration mismatch, ...).
    Reference(ReferenceError),
    /// A path escaped the project root or was otherwise invalid.
    Path(PathError),
    /// A referenced project is not part of the graph.
    MissingReference { from: PathBuf, to: PathBuf },
    /// A project required for scheduling has no graph node.
    MissingProject { path: PathBuf },
    /// A host-provided operation failed.
    Host { message: Arc<str> },
    /// A stored `.tsbuildinfo` could not be decoded.
    BuildInfoDecode(BuildInfoDecodeError),
    /// A `BuildInfo` value could not be encoded canonically.
    BuildInfoEncode(BuildInfoEncodeError),
}

impl fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reference(source) => source.fmt(formatter),
            Self::Path(source) => source.fmt(formatter),
            Self::MissingReference { from, to } => write!(
                formatter,
                "project {} references {} which is not in the build graph",
                from.display(),
                to.display()
            ),
            Self::MissingProject { path } => {
                write!(formatter, "project {} has no graph node", path.display())
            }
            Self::Host { message } => formatter.write_str(message),
            Self::BuildInfoDecode(source) => source.fmt(formatter),
            Self::BuildInfoEncode(source) => source.fmt(formatter),
        }
    }
}

impl std::error::Error for BuildError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Reference(source) => Some(source),
            Self::Path(source) => Some(source),
            Self::BuildInfoDecode(source) => Some(source),
            Self::BuildInfoEncode(source) => Some(source),
            _ => None,
        }
    }
}

impl From<ReferenceError> for BuildError {
    fn from(source: ReferenceError) -> Self {
        Self::Reference(source)
    }
}

impl From<PathError> for BuildError {
    fn from(source: PathError) -> Self {
        Self::Path(source)
    }
}

impl From<BuildInfoDecodeError> for BuildError {
    fn from(source: BuildInfoDecodeError) -> Self {
        Self::BuildInfoDecode(source)
    }
}

impl From<BuildInfoEncodeError> for BuildError {
    fn from(source: BuildInfoEncodeError) -> Self {
        Self::BuildInfoEncode(source)
    }
}

/// The deterministic incremental build state kept for one project.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BuildInfo {
    /// Schema version for the on-disk representation.
    pub version: Arc<str>,
    /// Canonical signature of the compiler-options JSON object.
    pub options: Arc<str>,
    /// Source-file signatures, keyed by absolute source path.
    pub sources: BTreeMap<PathBuf, Arc<str>>,
    /// The outputs that were produced by the last successful build.
    pub outputs: BTreeSet<PathBuf>,
    /// Overall signature used for one-shot up-to-date checks.
    pub signature: Arc<str>,
}

/// The only schema version this build understands.
pub const BUILD_INFO_SCHEMA: &str = "bamts-build-1";

/// Length of a `project_signature` value: FNV-1a rendered as `{:016x}`.
const SIGNATURE_HEX_LEN: usize = 16;

/// Length of a `source_signature` value: SHA-256 rendered as lower-case hex.
const SOURCE_DIGEST_HEX_LEN: usize = 64;

/// A `BuildInfo` value that cannot be written in the canonical form.
///
/// Encoding is fallible on purpose: a lossy fallback would silently corrupt
/// incremental identity, and a value that cannot be encoded canonically is a
/// programming error in the producer, not a recoverable input.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildInfoEncodeError {
    /// The value carries a schema version this build cannot write.
    UnsupportedVersion { found: String },
    /// The overall signature is not a canonical `project_signature` value.
    InvalidSignature { value: String },
    /// A source signature is not a canonical `source_signature` value.
    InvalidSourceDigest { path: PathBuf, value: String },
    /// A path is not UTF-8, is empty, or contains a `.`/`..` component.
    InvalidPath { path: PathBuf },
}

impl fmt::Display for BuildInfoEncodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedVersion { found } => write!(
                formatter,
                "cannot encode build info schema {found:?}, expected {BUILD_INFO_SCHEMA:?}"
            ),
            Self::InvalidSignature { value } => {
                write!(formatter, "invalid build info signature {value:?}")
            }
            Self::InvalidSourceDigest { path, value } => write!(
                formatter,
                "invalid source signature {value:?} for {}",
                path.display()
            ),
            Self::InvalidPath { path } => {
                write!(formatter, "invalid build info path {}", path.display())
            }
        }
    }
}

impl std::error::Error for BuildInfoEncodeError {}

/// A stored `.tsbuildinfo` that is not the canonical encoding of a `BuildInfo`.
///
/// Every variant is a hard rejection: the decoder accepts exactly the byte
/// strings that `BuildInfo::encode` produces, so any deviation means the state
/// was truncated, hand-edited, or written by a different implementation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildInfoDecodeError {
    /// The input carried no bytes at all.
    Empty,
    /// The input is not valid UTF-8.
    InvalidUtf8 { offset: usize },
    /// The input ended in the middle of the grammar.
    Truncated { offset: usize },
    /// The expected literal was not present.
    Expected {
        offset: usize,
        expected: &'static str,
    },
    /// A string used an escape or raw byte the encoder never emits.
    NonCanonicalString { offset: usize },
    /// The schema version is not the one this build writes.
    UnsupportedVersion { found: String },
    /// The overall signature is not a canonical `project_signature` value.
    InvalidSignature { value: String },
    /// A source signature is not a canonical `source_signature` value.
    InvalidSourceDigest { path: PathBuf, value: String },
    /// A path is empty or contains a `.`/`..` component.
    InvalidPath { path: String },
    /// The same path appeared twice in one collection.
    DuplicatePath { path: PathBuf },
    /// Paths were not in ascending order, so the state is not canonical.
    UnsortedPath { previous: PathBuf, found: PathBuf },
    /// Bytes followed the encoded value.
    TrailingBytes { offset: usize },
}

impl fmt::Display for BuildInfoDecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("empty build info"),
            Self::InvalidUtf8 { offset } => {
                write!(formatter, "build info is not UTF-8 at byte {offset}")
            }
            Self::Truncated { offset } => {
                write!(formatter, "build info truncated at byte {offset}")
            }
            Self::Expected { offset, expected } => write!(
                formatter,
                "build info expected {expected:?} at byte {offset}"
            ),
            Self::NonCanonicalString { offset } => write!(
                formatter,
                "build info string is not canonically escaped at byte {offset}"
            ),
            Self::UnsupportedVersion { found } => write!(
                formatter,
                "unsupported build info schema {found:?}, expected {BUILD_INFO_SCHEMA:?}"
            ),
            Self::InvalidSignature { value } => {
                write!(formatter, "invalid build info signature {value:?}")
            }
            Self::InvalidSourceDigest { path, value } => write!(
                formatter,
                "invalid source signature {value:?} for {}",
                path.display()
            ),
            Self::InvalidPath { path } => write!(formatter, "invalid build info path {path:?}"),
            Self::DuplicatePath { path } => {
                write!(formatter, "duplicate build info path {}", path.display())
            }
            Self::UnsortedPath { previous, found } => write!(
                formatter,
                "build info path {} follows {} out of order",
                found.display(),
                previous.display()
            ),
            Self::TrailingBytes { offset } => {
                write!(
                    formatter,
                    "unexpected bytes after build info at byte {offset}"
                )
            }
        }
    }
}

impl std::error::Error for BuildInfoDecodeError {}

impl BuildInfo {
    /// Writes the canonical, versioned byte encoding of this state.
    ///
    /// The encoding is a single-line JSON object with a fixed key order and no
    /// whitespace, so equal `BuildInfo` values always produce equal bytes and
    /// the bytes are independent of insertion order.  Collections are written
    /// as arrays in `BTreeMap`/`BTreeSet` order, which makes the ordering part
    /// of the format instead of an implicit property of the writer.
    pub fn encode(&self) -> Result<Vec<u8>, BuildInfoEncodeError> {
        if &*self.version != BUILD_INFO_SCHEMA {
            return Err(BuildInfoEncodeError::UnsupportedVersion {
                found: self.version.to_string(),
            });
        }
        if !is_lower_hex(&self.signature, SIGNATURE_HEX_LEN) {
            return Err(BuildInfoEncodeError::InvalidSignature {
                value: self.signature.to_string(),
            });
        }

        let mut out = String::new();
        out.push_str("{\"version\":");
        push_json_string(&mut out, &self.version);
        out.push_str(",\"options\":");
        push_json_string(&mut out, &self.options);
        out.push_str(",\"signature\":");
        push_json_string(&mut out, &self.signature);

        out.push_str(",\"sources\":[");
        for (index, (path, digest)) in self.sources.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            if !is_lower_hex(digest, SOURCE_DIGEST_HEX_LEN) {
                return Err(BuildInfoEncodeError::InvalidSourceDigest {
                    path: path.clone(),
                    value: digest.to_string(),
                });
            }
            out.push('[');
            push_json_string(&mut out, encode_path(path)?);
            out.push(',');
            push_json_string(&mut out, digest);
            out.push(']');
        }

        out.push_str("],\"outputs\":[");
        for (index, path) in self.outputs.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            push_json_string(&mut out, encode_path(path)?);
        }
        out.push_str("]}");

        Ok(out.into_bytes())
    }

    /// Reads the canonical byte encoding produced by [`BuildInfo::encode`].
    ///
    /// The grammar is matched literal by literal, so reordered keys, inserted
    /// whitespace, missing or extra keys, and trailing bytes are all rejected
    /// structurally rather than normalised away.  No intermediate value tree is
    /// built: the reader walks the input once.
    pub fn decode(bytes: &[u8]) -> Result<BuildInfo, BuildInfoDecodeError> {
        if bytes.is_empty() {
            return Err(BuildInfoDecodeError::Empty);
        }
        let input =
            std::str::from_utf8(bytes).map_err(|error| BuildInfoDecodeError::InvalidUtf8 {
                offset: error.valid_up_to(),
            })?;
        let mut reader = Reader { input, position: 0 };

        reader.expect("{\"version\":")?;
        let version = reader.read_string()?;
        if version != BUILD_INFO_SCHEMA {
            return Err(BuildInfoDecodeError::UnsupportedVersion { found: version });
        }

        reader.expect(",\"options\":")?;
        let options = reader.read_string()?;

        reader.expect(",\"signature\":")?;
        let signature = reader.read_string()?;
        if !is_lower_hex(&signature, SIGNATURE_HEX_LEN) {
            return Err(BuildInfoDecodeError::InvalidSignature { value: signature });
        }

        reader.expect(",\"sources\":[")?;
        let mut sources: BTreeMap<PathBuf, Arc<str>> = BTreeMap::new();
        let mut previous: Option<PathBuf> = None;
        if reader.peek() != Some(b']') {
            loop {
                reader.expect("[")?;
                let path = decode_path(&reader.read_string()?)?;
                reader.expect(",")?;
                let digest = reader.read_string()?;
                if !is_lower_hex(&digest, SOURCE_DIGEST_HEX_LEN) {
                    return Err(BuildInfoDecodeError::InvalidSourceDigest {
                        path,
                        value: digest,
                    });
                }
                reader.expect("]")?;
                check_ascending(&mut previous, &path)?;
                sources.insert(path, Arc::from(digest));
                if reader.peek() == Some(b',') {
                    reader.expect(",")?;
                    continue;
                }
                break;
            }
        }
        reader.expect("]")?;

        reader.expect(",\"outputs\":[")?;
        let mut outputs: BTreeSet<PathBuf> = BTreeSet::new();
        let mut previous: Option<PathBuf> = None;
        if reader.peek() != Some(b']') {
            loop {
                let path = decode_path(&reader.read_string()?)?;
                check_ascending(&mut previous, &path)?;
                outputs.insert(path);
                if reader.peek() == Some(b',') {
                    reader.expect(",")?;
                    continue;
                }
                break;
            }
        }
        reader.expect("]")?;
        reader.expect("}")?;

        if reader.position != reader.input.len() {
            return Err(BuildInfoDecodeError::TrailingBytes {
                offset: reader.position,
            });
        }

        Ok(BuildInfo {
            version: Arc::from(BUILD_INFO_SCHEMA),
            options: Arc::from(options),
            sources,
            outputs,
            signature: Arc::from(signature),
        })
    }
}

/// A single-pass cursor over the canonical encoding.
struct Reader<'a> {
    input: &'a str,
    position: usize,
}

impl Reader<'_> {
    fn peek(&self) -> Option<u8> {
        self.input.as_bytes().get(self.position).copied()
    }

    fn expect(&mut self, literal: &'static str) -> Result<(), BuildInfoDecodeError> {
        let end = self.position + literal.len();
        let actual = self.input.as_bytes().get(self.position..end);
        match actual {
            Some(bytes) if bytes == literal.as_bytes() => {
                self.position = end;
                Ok(())
            }
            Some(_) => Err(BuildInfoDecodeError::Expected {
                offset: self.position,
                expected: literal,
            }),
            None => Err(BuildInfoDecodeError::Truncated {
                offset: self.position,
            }),
        }
    }

    /// Reads one string, accepting only the escapes `push_json_string` emits.
    fn read_string(&mut self) -> Result<String, BuildInfoDecodeError> {
        self.expect("\"")?;
        let mut out = String::new();
        loop {
            let bytes = self.input.as_bytes();
            let byte = *bytes
                .get(self.position)
                .ok_or(BuildInfoDecodeError::Truncated {
                    offset: self.position,
                })?;
            match byte {
                b'"' => {
                    self.position += 1;
                    return Ok(out);
                }
                b'\\' => {
                    let escape =
                        *bytes
                            .get(self.position + 1)
                            .ok_or(BuildInfoDecodeError::Truncated {
                                offset: self.position + 1,
                            })?;
                    let plain = match escape {
                        b'"' => Some('"'),
                        b'\\' => Some('\\'),
                        b'n' => Some('\n'),
                        b'r' => Some('\r'),
                        b't' => Some('\t'),
                        b'b' => Some('\u{08}'),
                        b'f' => Some('\u{0c}'),
                        b'u' => None,
                        _ => {
                            return Err(BuildInfoDecodeError::NonCanonicalString {
                                offset: self.position,
                            });
                        }
                    };
                    if let Some(c) = plain {
                        out.push(c);
                        self.position += 2;
                        continue;
                    }
                    let digits = bytes.get(self.position + 2..self.position + 6).ok_or(
                        BuildInfoDecodeError::Truncated {
                            offset: self.position + 2,
                        },
                    )?;
                    let mut value = 0u32;
                    for digit in digits {
                        let nibble = match digit {
                            b'0'..=b'9' => u32::from(digit - b'0'),
                            b'a'..=b'f' => u32::from(digit - b'a') + 10,
                            _ => {
                                return Err(BuildInfoDecodeError::NonCanonicalString {
                                    offset: self.position,
                                });
                            }
                        };
                        value = value * 16 + nibble;
                    }
                    // The encoder only reaches `\u` for control characters that
                    // have no shorter escape, so anything else is non-canonical.
                    let shorter = matches!(value, 0x08 | 0x09 | 0x0a | 0x0c | 0x0d);
                    if value >= 0x20 || shorter {
                        return Err(BuildInfoDecodeError::NonCanonicalString {
                            offset: self.position,
                        });
                    }
                    let c =
                        char::from_u32(value).ok_or(BuildInfoDecodeError::NonCanonicalString {
                            offset: self.position,
                        })?;
                    out.push(c);
                    self.position += 6;
                }
                b if b < 0x20 => {
                    return Err(BuildInfoDecodeError::NonCanonicalString {
                        offset: self.position,
                    });
                }
                _ => {
                    let c = self.input[self.position..].chars().next().ok_or(
                        BuildInfoDecodeError::Truncated {
                            offset: self.position,
                        },
                    )?;
                    out.push(c);
                    self.position += c.len_utf8();
                }
            }
        }
    }
}

/// Rejects duplicate and out-of-order paths.
///
/// Comparison uses `PathBuf` ordering, which is what `BTreeMap`/`BTreeSet` use,
/// so accepting an input guarantees that re-encoding it reproduces the same
/// byte sequence.  Raw string ordering would not: `Path` compares by component.
fn check_ascending(
    previous: &mut Option<PathBuf>,
    path: &PathBuf,
) -> Result<(), BuildInfoDecodeError> {
    if let Some(prior) = previous.as_ref() {
        if prior == path {
            return Err(BuildInfoDecodeError::DuplicatePath { path: path.clone() });
        }
        if path < prior {
            return Err(BuildInfoDecodeError::UnsortedPath {
                previous: prior.clone(),
                found: path.clone(),
            });
        }
    }
    *previous = Some(path.clone());
    Ok(())
}

fn decode_path(raw: &str) -> Result<PathBuf, BuildInfoDecodeError> {
    let path = PathBuf::from(raw);
    if raw.is_empty() || !path.is_absolute() || has_traversal(&path) {
        return Err(BuildInfoDecodeError::InvalidPath {
            path: raw.to_string(),
        });
    }
    Ok(path)
}

fn encode_path(path: &Path) -> Result<&str, BuildInfoEncodeError> {
    let raw = path
        .to_str()
        .ok_or_else(|| BuildInfoEncodeError::InvalidPath {
            path: path.to_path_buf(),
        })?;
    if raw.is_empty() || !path.is_absolute() || has_traversal(path) {
        return Err(BuildInfoEncodeError::InvalidPath {
            path: path.to_path_buf(),
        });
    }
    Ok(raw)
}

fn has_traversal(path: &Path) -> bool {
    path.components()
        .any(|component| matches!(component, Component::CurDir | Component::ParentDir))
}

fn is_lower_hex(value: &str, len: usize) -> bool {
    value.len() == len
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// The files produced by a single project compilation.
///
/// `BTreeMap` is used intentionally so that output order is deterministic and
/// independent of insertion order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BuildOutputs {
    pub files: BTreeMap<PathBuf, Vec<u8>>,
}

/// One action emitted by the build engine.
///
/// The action list is the canonical deterministic record of what the engine
/// decided to do for a given input state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildAction {
    Build(PathBuf),
    WouldBuild(PathBuf),
    Skip(PathBuf),
    Clean(PathBuf),
    WouldClean(PathBuf),
    Fail(PathBuf),
    Blocked(PathBuf),
}

/// The result of a build or clean run.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BuildReport {
    /// Deterministic, ordered list of actions taken or planned.
    pub actions: Vec<BuildAction>,
    /// Verbose progress log, if requested.
    pub log: Vec<Arc<str>>,
    /// The first project whose compilation failed, if any.
    pub failed: Option<PathBuf>,
}

impl BuildReport {
    /// Returns the projects that were actually built.
    #[must_use]
    pub fn built(&self) -> Vec<&PathBuf> {
        self.actions
            .iter()
            .filter_map(|a| match a {
                BuildAction::Build(p) => Some(p),
                _ => None,
            })
            .collect()
    }

    /// Returns the projects that were skipped as up to date.
    #[must_use]
    pub fn skipped(&self) -> Vec<&PathBuf> {
        self.actions
            .iter()
            .filter_map(|a| match a {
                BuildAction::Skip(p) => Some(p),
                _ => None,
            })
            .collect()
    }

    /// Returns the outputs that were removed or would have been removed.
    #[must_use]
    pub fn cleaned(&self) -> Vec<&PathBuf> {
        self.actions
            .iter()
            .filter_map(|a| match a {
                BuildAction::Clean(p) | BuildAction::WouldClean(p) => Some(p),
                _ => None,
            })
            .collect()
    }
}

/// A caller-supplied environment that performs the concrete file-system and
/// compilation work for the build engine.
pub trait BuildHost {
    /// Returns the canonical options signature for `project`.
    fn options_signature(&mut self, project: &Path) -> Result<Arc<str>, BuildError>;

    /// Returns the current source-file signatures for `project`.
    fn source_signatures(
        &mut self,
        project: &Path,
        node: &ReferenceNode,
    ) -> Result<BTreeMap<PathBuf, Arc<str>>, BuildError>;

    /// Returns the output paths that the build would remove for `project`.
    fn declared_outputs(&mut self, project: &Path, node: &ReferenceNode) -> BTreeSet<PathBuf>;

    /// Returns the bytes of an existing output, if any.
    fn read_output(&mut self, path: &Path) -> Option<Vec<u8>>;

    /// Removes an existing output.
    fn remove_output(&mut self, path: &Path) -> Result<(), BuildError>;

    /// Writes a new file (not necessarily atomically; the engine handles the
    /// temp/rename dance for outputs).
    fn write_file(&mut self, path: &Path, content: &[u8]) -> Result<(), BuildError>;

    /// Atomically renames `from` to `to`.
    fn rename(&mut self, from: &Path, to: &Path) -> Result<(), BuildError>;

    /// Reads the bytes of a stored `.tsbuildinfo`, if any.
    ///
    /// Hosts are byte-dumb: the engine owns the canonical encoding, so a host
    /// never parses or produces build-info structure itself.
    fn read_build_info(&mut self, path: &Path) -> Option<Vec<u8>>;

    /// Writes the exact bytes of a `.tsbuildinfo`.
    fn write_build_info(&mut self, path: &Path, bytes: &[u8]) -> Result<(), BuildError>;

    /// Compiles one project and returns the outputs to write.
    fn compile(&mut self, project: &Path) -> Result<BuildOutputs, BuildError>;
}

/// Canonicalises a `JsonValue` into a deterministic, whitespace-free JSON
/// string.  Object keys are emitted in declaration order; the input is already
/// sorted by the canonical graph construction in `references.rs`.
pub fn canonical_json(value: &JsonValue) -> String {
    match value {
        JsonValue::Null => "null".to_string(),
        JsonValue::Bool(b) => b.to_string(),
        JsonValue::Number(n) => n.to_string(),
        JsonValue::String(s) => json_string(s),
        JsonValue::Array(items) => {
            let inner: Vec<String> = items.iter().map(canonical_json).collect();
            format!("[{}]", inner.join(","))
        }
        JsonValue::Object(obj) => {
            let inner: Vec<String> = obj
                .entries()
                .iter()
                .map(|(key, value)| format!("{}:{}", json_string(key), canonical_json(value)))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
    }
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    push_json_string(&mut out, s);
    out
}

fn push_json_string(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0C}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                use std::fmt::Write;
                write!(out, "\\u{:04x}", c as u32).expect("writing to String cannot fail");
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Computes a canonical options signature from the raw `compilerOptions` value.
pub fn options_signature(config: &ProjectConfig) -> Arc<str> {
    match config.raw().get("compilerOptions") {
        Some(JsonValue::Object(obj)) => Arc::from(canonical_json(&JsonValue::Object(obj.clone()))),
        _ => Arc::from("null"),
    }
}

/// Computes the canonical SHA-256 identity of source text.
///
/// The digest is defined over the exact UTF-8 bytes used by the parser.  Hosts
/// call this function rather than choosing an incremental hash algorithm, so
/// plain project and build-mode state remain interchangeable.
pub fn source_signature(text: &str) -> Arc<str> {
    let digest = Sha256::digest(text.as_bytes());
    let mut out = String::with_capacity(SOURCE_DIGEST_HEX_LEN);
    for byte in digest {
        use std::fmt::Write;
        write!(out, "{byte:02x}").expect("writing to String cannot fail");
    }
    Arc::from(out)
}

const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

fn feed(hash: &mut u64, bytes: &[u8]) {
    for &byte in bytes {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(FNV_PRIME);
    }
}

/// Computes a pure, deterministic project signature from the inputs that the
/// build is sensitive to: project path, options, source signatures, and the
/// signatures of all referenced upstream projects.
pub fn project_signature(
    node: &ReferenceNode,
    options: &str,
    sources: &BTreeMap<PathBuf, Arc<str>>,
    upstream: &BTreeMap<PathBuf, Arc<str>>,
) -> Arc<str> {
    let mut hash = FNV_OFFSET_BASIS;
    feed(&mut hash, b"project");
    feed(&mut hash, node.path.to_string_lossy().as_bytes());
    feed(&mut hash, b"options");
    feed(&mut hash, options.as_bytes());
    feed(&mut hash, b"sources");
    for (path, signature) in sources {
        feed(&mut hash, b"file");
        feed(&mut hash, path.to_string_lossy().as_bytes());
        feed(&mut hash, b"signature");
        feed(&mut hash, signature.as_bytes());
    }
    feed(&mut hash, b"upstream");
    for (path, signature) in upstream {
        feed(&mut hash, b"dep");
        feed(&mut hash, path.to_string_lossy().as_bytes());
        feed(&mut hash, b"signature");
        feed(&mut hash, signature.as_bytes());
    }
    Arc::from(format!("{:016x}", hash))
}

/// Pure up-to-date check for one project.
///
/// `outputs_present` is the set of output files currently known to exist.
/// The verdict is identical for identical inputs because all collections are
/// sorted and the signature is a pure function of its arguments.
pub fn is_project_up_to_date(
    build_info: &BuildInfo,
    node: &ReferenceNode,
    options: &Arc<str>,
    sources: &BTreeMap<PathBuf, Arc<str>>,
    upstream: &BTreeMap<PathBuf, Arc<str>>,
    outputs_present: &BTreeSet<PathBuf>,
) -> bool {
    if build_info.options.as_ref() != options.as_ref() {
        return false;
    }
    if &build_info.sources != sources {
        return false;
    }

    if !build_info.outputs.is_subset(outputs_present) {
        return false;
    }
    let expected = project_signature(node, options, sources, upstream);
    build_info.signature == expected
}

/// Returns a sibling `.tmp` path that can be used for an atomic write.
pub fn temp_path(target: &Path) -> PathBuf {
    let mut temp = target.as_os_str().to_os_string();
    temp.push(".tmp");
    PathBuf::from(temp)
}

/// Executes a `tsc -b` build or clean run over the canonical project graph.
pub fn execute(
    graph: &ReferenceGraph,
    host: &mut dyn BuildHost,
    root: &ProjectRoot,
    options: &BuildOptions,
) -> Result<BuildReport, BuildError> {
    if options.clean {
        return clean(graph, host, root, options);
    }

    if let Some(error) = graph.validate().into_iter().next() {
        return Err(error.into());
    }
    let order = graph.topological_order()?;
    let mut report = BuildReport::default();
    let mut signatures: BTreeMap<PathBuf, Arc<str>> = BTreeMap::new();
    let mut failed_or_blocked: BTreeSet<PathBuf> = BTreeSet::new();

    for (index, project) in order.iter().enumerate() {
        let node = graph
            .node(project)
            .ok_or_else(|| BuildError::MissingProject {
                path: project.clone(),
            })?;

        // Validate that every declared reference is actually present in the
        // graph.  A missing reference is an unrecoverable graph error.
        for reference in node.references.iter() {
            let target = reference.path();
            if graph.node(target).is_none() {
                return Err(BuildError::MissingReference {
                    from: project.clone(),
                    to: target.to_path_buf(),
                });
            }
        }

        if node
            .references
            .iter()
            .any(|reference| failed_or_blocked.contains(reference.path()))
        {
            report.actions.push(BuildAction::Blocked(project.clone()));
            failed_or_blocked.insert(project.clone());
            if options.verbose {
                report.log.push(Arc::from(format!(
                    "{} blocked by a failed dependency",
                    project.display()
                )));
            }
            continue;
        }

        if options.verbose {
            report
                .log
                .push(Arc::from(format!("checking {}", project.display())));
        }

        let current_options = host.options_signature(project)?;
        let source_signatures = host.source_signatures(project, node)?;
        let mut upstream = BTreeMap::new();
        for reference in node.references.iter() {
            let target = reference.path();
            if let Some(signature) = signatures.get(&target.to_path_buf()) {
                upstream.insert(target.to_path_buf(), signature.clone());
            }
        }

        let signature = project_signature(node, &current_options, &source_signatures, &upstream);

        let mut previous_outputs = BTreeSet::new();
        let up_to_date = if options.force {
            false
        } else if let Some(info_path) = &node.build_info_path {
            root.confine(info_path)?;
            if let Some(bytes) = host.read_build_info(info_path) {
                let build_info = BuildInfo::decode(&bytes)?;
                previous_outputs = build_info.outputs.clone();
                let declared = host.declared_outputs(project, node);
                let outputs_present: BTreeSet<_> = declared
                    .iter()
                    .filter(|p| host.read_output(p).is_some())
                    .cloned()
                    .collect();
                is_project_up_to_date(
                    &build_info,
                    node,
                    &current_options,
                    &source_signatures,
                    &upstream,
                    &outputs_present,
                )
            } else {
                false
            }
        } else {
            false
        };

        if up_to_date {
            if options.verbose {
                report.log.push(Arc::from(format!(
                    "skipping {} (up to date)",
                    project.display()
                )));
            }
            report.actions.push(BuildAction::Skip(project.clone()));
            signatures.insert(project.clone(), signature);
            continue;
        }

        if options.dry_run {
            if options.verbose {
                report
                    .log
                    .push(Arc::from(format!("would build {}", project.display())));
            }
            report
                .actions
                .push(BuildAction::WouldBuild(project.clone()));
            signatures.insert(project.clone(), signature);
            continue;
        }

        let outputs = match host.compile(project) {
            Ok(o) => o,
            Err(e) => {
                if options.verbose {
                    report.log.push(Arc::from(format!(
                        "failed to build {}: {}",
                        project.display(),
                        e
                    )));
                }
                report.actions.push(BuildAction::Fail(project.clone()));
                report.failed.get_or_insert_with(|| project.clone());
                failed_or_blocked.insert(project.clone());
                if options.stop_on_error {
                    for remaining in order.iter().skip(index + 1) {
                        report.actions.push(BuildAction::Blocked(remaining.clone()));
                        if options.verbose {
                            report.log.push(Arc::from(format!(
                                "{} blocked by failure in {}",
                                remaining.display(),
                                project.display()
                            )));
                        }
                    }
                    return Ok(report);
                }
                continue;
            }
        };

        if options.verbose {
            report
                .log
                .push(Arc::from(format!("building {}", project.display())));
        }

        // Atomic, deterministic output emission: every output is written to a
        // temporary sibling file and renamed into place.  Files are emitted in
        // sorted order because `outputs.files` is a `BTreeMap`.
        for (out_path, content) in &outputs.files {
            root.confine(out_path)?;
            let temp = temp_path(out_path);
            host.write_file(&temp, content)?;
            host.rename(&temp, out_path)?;
            if options.verbose {
                report.log.push(Arc::from(format!(
                    "wrote {} ({} bytes)",
                    out_path.display(),
                    content.len()
                )));
            }
        }
        let new_outputs: BTreeSet<_> = outputs.files.keys().cloned().collect();
        for stale in previous_outputs.difference(&new_outputs) {
            root.confine(stale)?;
            host.remove_output(stale)?;
        }

        let build_info = BuildInfo {
            version: Arc::from(BUILD_INFO_SCHEMA),
            options: current_options,
            sources: source_signatures,
            outputs: outputs.files.keys().cloned().collect(),
            signature: Arc::clone(&signature),
        };

        if let Some(info_path) = &node.build_info_path {
            root.confine(info_path)?;
            let bytes = build_info.encode()?;
            host.write_build_info(info_path, &bytes)?;
            if options.verbose {
                report.log.push(Arc::from(format!(
                    "wrote build info {}",
                    info_path.display()
                )));
            }
        }

        report.actions.push(BuildAction::Build(project.clone()));
        signatures.insert(project.clone(), signature);
    }

    Ok(report)
}

/// Cleans every project in the graph in reverse topological order.
pub fn clean(
    graph: &ReferenceGraph,
    host: &mut dyn BuildHost,
    root: &ProjectRoot,
    options: &BuildOptions,
) -> Result<BuildReport, BuildError> {
    let order = graph.topological_order()?;
    let mut report = BuildReport::default();

    for project in order.iter().rev() {
        let node = graph
            .node(project)
            .ok_or_else(|| BuildError::MissingProject {
                path: project.clone(),
            })?;

        let mut to_remove: BTreeSet<PathBuf> = host.declared_outputs(project, node);
        if let Some(info_path) = &node.build_info_path {
            to_remove.insert(info_path.clone());
        }

        for out_path in to_remove {
            root.confine(&out_path)?;
            if options.dry_run {
                if options.verbose {
                    report
                        .log
                        .push(Arc::from(format!("would clean {}", out_path.display())));
                }
                report.actions.push(BuildAction::WouldClean(out_path));
            } else {
                if options.verbose {
                    report
                        .log
                        .push(Arc::from(format!("cleaning {}", out_path.display())));
                }
                host.remove_output(&out_path)?;
                report.actions.push(BuildAction::Clean(out_path));
            }
        }
    }

    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::super::references::ReferenceGraph;
    use super::super::test_paths::{abs, abs_json, abs_text};
    use super::super::tsconfig::TsConfig;
    use super::super::{ProjectConfig, ProjectRoot};
    use super::*;

    fn test_root() -> ProjectRoot {
        ProjectRoot::new(abs("/workspace/test")).expect("absolute test root")
    }

    fn parse_tsconfig(root: &ProjectRoot, path: impl AsRef<Path>, source: &str) -> TsConfig {
        TsConfig::parse(root, path, source).expect("valid test tsconfig")
    }

    fn parse_config(root: &ProjectRoot, path: impl AsRef<Path>, source: &str) -> ProjectConfig {
        ProjectConfig::parse(root, path, source).expect("valid test config")
    }

    struct InMemoryHost {
        configs: BTreeMap<PathBuf, ProjectConfig>,
        source_signatures: BTreeMap<PathBuf, BTreeMap<PathBuf, Arc<str>>>,
        declared_outputs: BTreeMap<PathBuf, BTreeSet<PathBuf>>,
        outputs: BTreeMap<PathBuf, Vec<u8>>,
        build_infos: BTreeMap<PathBuf, Vec<u8>>,
        compile_outputs: BTreeMap<PathBuf, BuildOutputs>,
        compile_errors: BTreeSet<PathBuf>,
        compile_calls: Vec<PathBuf>,
        rename_log: Vec<(PathBuf, PathBuf)>,
    }

    impl InMemoryHost {
        fn new() -> Self {
            Self {
                configs: BTreeMap::new(),
                source_signatures: BTreeMap::new(),
                declared_outputs: BTreeMap::new(),
                outputs: BTreeMap::new(),
                build_infos: BTreeMap::new(),
                compile_outputs: BTreeMap::new(),
                compile_errors: BTreeSet::new(),
                compile_calls: Vec::new(),
                rename_log: Vec::new(),
            }
        }

        fn with_config(mut self, project: &Path, config: ProjectConfig) -> Self {
            self.configs.insert(project.to_path_buf(), config);
            self
        }

        fn with_source_signatures(
            mut self,
            project: &Path,
            signatures: BTreeMap<PathBuf, Arc<str>>,
        ) -> Self {
            self.source_signatures
                .insert(project.to_path_buf(), signatures);
            self
        }

        fn with_declared_outputs(mut self, project: &Path, outputs: BTreeSet<PathBuf>) -> Self {
            self.declared_outputs.insert(project.to_path_buf(), outputs);
            self
        }

        fn with_compile_output(mut self, project: &Path, output: BuildOutputs) -> Self {
            self.compile_outputs.insert(project.to_path_buf(), output);
            self
        }

        fn with_output(mut self, path: PathBuf, content: Vec<u8>) -> Self {
            self.outputs.insert(path, content);
            self
        }
        fn with_compile_error(mut self, project: &Path) -> Self {
            self.compile_errors.insert(project.to_path_buf());
            self
        }

        fn with_build_info(mut self, path: &Path, info: BuildInfo) -> Self {
            let bytes = info.encode().expect("valid canonical test build info");
            self.build_infos.insert(path.to_path_buf(), bytes);
            self
        }
    }

    impl BuildHost for InMemoryHost {
        fn options_signature(&mut self, project: &Path) -> Result<Arc<str>, BuildError> {
            Ok(self
                .configs
                .get(&project.to_path_buf())
                .map(super::options_signature)
                .unwrap_or_else(|| Arc::from("null")))
        }

        fn source_signatures(
            &mut self,
            project: &Path,
            _node: &ReferenceNode,
        ) -> Result<BTreeMap<PathBuf, Arc<str>>, BuildError> {
            Ok(self
                .source_signatures
                .get(&project.to_path_buf())
                .cloned()
                .unwrap_or_default())
        }

        fn declared_outputs(&mut self, project: &Path, _node: &ReferenceNode) -> BTreeSet<PathBuf> {
            self.declared_outputs
                .get(&project.to_path_buf())
                .cloned()
                .unwrap_or_default()
        }

        fn read_output(&mut self, path: &Path) -> Option<Vec<u8>> {
            self.outputs.get(&path.to_path_buf()).cloned()
        }

        fn remove_output(&mut self, path: &Path) -> Result<(), BuildError> {
            self.outputs.remove(&path.to_path_buf());
            Ok(())
        }

        fn write_file(&mut self, path: &Path, content: &[u8]) -> Result<(), BuildError> {
            self.outputs.insert(path.to_path_buf(), content.to_vec());
            Ok(())
        }

        fn rename(&mut self, from: &Path, to: &Path) -> Result<(), BuildError> {
            let content =
                self.outputs
                    .remove(&from.to_path_buf())
                    .ok_or_else(|| BuildError::Host {
                        message: Arc::from(format!("no temporary file {}", from.display())),
                    })?;
            self.outputs.insert(to.to_path_buf(), content);
            self.rename_log.push((from.to_path_buf(), to.to_path_buf()));
            Ok(())
        }
        fn read_build_info(&mut self, path: &Path) -> Option<Vec<u8>> {
            self.build_infos.get(&path.to_path_buf()).cloned()
        }

        fn write_build_info(&mut self, path: &Path, bytes: &[u8]) -> Result<(), BuildError> {
            self.build_infos.insert(path.to_path_buf(), bytes.to_vec());
            Ok(())
        }

        fn compile(&mut self, project: &Path) -> Result<BuildOutputs, BuildError> {
            self.compile_calls.push(project.to_path_buf());
            if self.compile_errors.contains(&project.to_path_buf()) {
                return Err(BuildError::Host {
                    message: Arc::from("compile error"),
                });
            }
            Ok(self
                .compile_outputs
                .get(&project.to_path_buf())
                .cloned()
                .unwrap_or_default())
        }
    }

    fn lib_path() -> PathBuf {
        abs("/workspace/test/lib/tsconfig.json")
    }

    fn app_path() -> PathBuf {
        abs("/workspace/test/app/tsconfig.json")
    }

    fn build_output(path: impl AsRef<Path>) -> BuildOutputs {
        let mut files = BTreeMap::new();
        files.insert(path.as_ref().to_path_buf(), vec![b'j', b's']);
        BuildOutputs { files }
    }

    #[test]
    fn force_builds_dependencies_first() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let app = parse_tsconfig(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), parse_config(&root, lib_path(), r#"{}"#))
            .with_config(
                &app_path(),
                parse_config(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#),
            )
            .with_compile_output(&lib_path(), build_output(abs("/workspace/test/lib/lib.js")))
            .with_compile_output(&app_path(), build_output(abs("/workspace/test/app/app.js")));

        let options = BuildOptions {
            force: true,
            ..BuildOptions::default()
        };
        let report = execute(&graph, &mut host, &root, &options).unwrap();

        assert_eq!(report.built(), vec![&lib_path(), &app_path()]);
        assert_eq!(host.compile_calls, vec![lib_path(), app_path()]);
    }

    #[test]
    fn dry_run_does_not_compile_or_write_outputs() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let app = parse_tsconfig(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), parse_config(&root, lib_path(), r#"{}"#))
            .with_config(
                &app_path(),
                parse_config(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#),
            )
            .with_compile_output(&lib_path(), build_output(abs("/workspace/test/lib/lib.js")))
            .with_compile_output(&app_path(), build_output(abs("/workspace/test/app/app.js")));

        let options = BuildOptions {
            dry_run: true,
            ..BuildOptions::default()
        };
        let report = execute(&graph, &mut host, &root, &options).unwrap();

        assert!(
            report
                .actions
                .iter()
                .all(|a| matches!(a, BuildAction::WouldBuild(_)))
        );
        assert!(host.compile_calls.is_empty());
        assert!(host.outputs.is_empty());
    }

    #[test]
    fn incremental_skips_unchanged_projects() {
        let root = test_root();
        let lib = parse_tsconfig(
            &root,
            lib_path(),
            r#"{"compilerOptions": {"composite": true}}"#,
        );
        let app = parse_tsconfig(
            &root,
            app_path(),
            r#"{"references": [{"path": "../lib"}], "compilerOptions": {"composite": true}}"#,
        );
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let lib_info = graph
            .node(lib_path().as_path())
            .unwrap()
            .build_info_path
            .clone()
            .unwrap();
        let app_info = graph
            .node(app_path().as_path())
            .unwrap()
            .build_info_path
            .clone()
            .unwrap();

        let lib_sources =
            BTreeMap::from([(abs("/workspace/test/lib/a.ts"), source_signature("lib v1"))]);
        let app_sources =
            BTreeMap::from([(abs("/workspace/test/app/b.ts"), source_signature("app v1"))]);

        let lib_config = parse_config(
            &root,
            lib_path(),
            r#"{"compilerOptions": {"composite": true}}"#,
        );
        let app_config = parse_config(
            &root,
            app_path(),
            r#"{"references": [{"path": "../lib"}], "compilerOptions": {"composite": true}}"#,
        );

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), lib_config.clone())
            .with_config(&app_path(), app_config.clone())
            .with_source_signatures(&lib_path(), lib_sources.clone())
            .with_source_signatures(&app_path(), app_sources.clone())
            .with_compile_output(&lib_path(), build_output(abs("/workspace/test/lib/lib.js")))
            .with_compile_output(&app_path(), build_output(abs("/workspace/test/app/app.js")))
            .with_declared_outputs(
                &lib_path(),
                BTreeSet::from([abs("/workspace/test/lib/lib.js")]),
            )
            .with_declared_outputs(
                &app_path(),
                BTreeSet::from([abs("/workspace/test/app/app.js")]),
            );

        // First build.
        let first = execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();
        assert_eq!(first.built(), vec![&lib_path(), &app_path()]);

        // Prepare the stored build info for the second run.
        let lib_sig = project_signature(
            graph.node(lib_path().as_path()).unwrap(),
            &options_signature(&lib_config),
            &lib_sources,
            &BTreeMap::new(),
        );
        let app_node = graph.node(app_path().as_path()).unwrap();
        let mut upstream = BTreeMap::new();
        upstream.insert(lib_path(), lib_sig.clone());
        let app_sig = project_signature(
            app_node,
            &options_signature(&app_config),
            &app_sources,
            &upstream,
        );

        host = host
            .with_build_info(
                &lib_info,
                BuildInfo {
                    version: Arc::from(BUILD_INFO_SCHEMA),
                    options: options_signature(&lib_config),
                    sources: lib_sources,
                    outputs: BTreeSet::from([abs("/workspace/test/lib/lib.js")]),
                    signature: lib_sig,
                },
            )
            .with_build_info(
                &app_info,
                BuildInfo {
                    version: Arc::from(BUILD_INFO_SCHEMA),
                    options: options_signature(&app_config),
                    sources: app_sources,
                    outputs: BTreeSet::from([abs("/workspace/test/app/app.js")]),
                    signature: app_sig,
                },
            );

        // Second build with identical inputs is fully up to date.
        let second = execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();
        assert_eq!(second.skipped(), vec![&lib_path(), &app_path()]);
        assert!(second.built().is_empty());
    }

    #[test]
    fn incremental_rebuilds_after_source_change() {
        let root = test_root();
        let lib = parse_tsconfig(
            &root,
            lib_path(),
            r#"{"compilerOptions": {"composite": true}}"#,
        );
        let app = parse_tsconfig(
            &root,
            app_path(),
            r#"{"references": [{"path": "../lib"}], "compilerOptions": {"composite": true}}"#,
        );
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let lib_info = graph
            .node(lib_path().as_path())
            .unwrap()
            .build_info_path
            .clone()
            .unwrap();

        let lib_sources =
            BTreeMap::from([(abs("/workspace/test/lib/a.ts"), source_signature("lib v1"))]);
        let lib_config = parse_config(
            &root,
            lib_path(),
            r#"{"compilerOptions": {"composite": true}}"#,
        );

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), lib_config.clone())
            .with_source_signatures(&lib_path(), lib_sources.clone())
            .with_compile_output(&lib_path(), build_output(abs("/workspace/test/lib/lib.js")))
            .with_declared_outputs(
                &lib_path(),
                BTreeSet::from([abs("/workspace/test/lib/lib.js")]),
            );

        execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();

        let lib_sig = project_signature(
            graph.node(lib_path().as_path()).unwrap(),
            &options_signature(&lib_config),
            &lib_sources,
            &BTreeMap::new(),
        );

        let mut changed_sources = lib_sources;
        changed_sources.insert(abs("/workspace/test/lib/a.ts"), source_signature("lib v2"));

        host = host
            .with_source_signatures(&lib_path(), changed_sources.clone())
            .with_build_info(
                &lib_info,
                BuildInfo {
                    version: Arc::from(BUILD_INFO_SCHEMA),
                    options: options_signature(&lib_config),
                    sources: changed_sources.clone(),
                    outputs: BTreeSet::from([abs("/workspace/test/lib/lib.js")]),
                    signature: lib_sig,
                },
            );

        let report = execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();
        assert_eq!(report.built(), vec![&lib_path(), &app_path()]);
    }

    #[test]
    fn failure_propagates_to_dependents() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let app = parse_tsconfig(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), parse_config(&root, lib_path(), r#"{}"#))
            .with_config(
                &app_path(),
                parse_config(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#),
            )
            .with_compile_error(&lib_path());

        let report = execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();

        assert!(matches!(report.actions[0], BuildAction::Fail(_)));
        assert!(
            report.actions[1..]
                .iter()
                .all(|a| matches!(a, BuildAction::Blocked(_)))
        );
        assert_eq!(report.failed, Some(lib_path()));
        assert!(
            !report
                .actions
                .iter()
                .any(|a| matches!(a, BuildAction::Build(_)))
        );
    }

    #[test]
    fn clean_removes_outputs_in_reverse_topological_order() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let app = parse_tsconfig(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let lib_out = abs("/workspace/test/lib/lib.js");
        let app_out = abs("/workspace/test/app/app.js");

        let mut host = InMemoryHost::new()
            .with_declared_outputs(&lib_path(), BTreeSet::from([lib_out.clone()]))
            .with_declared_outputs(&app_path(), BTreeSet::from([app_out.clone()]));

        let options = BuildOptions {
            clean: true,
            ..BuildOptions::default()
        };
        let report = clean(&graph, &mut host, &root, &options).unwrap();

        assert_eq!(report.cleaned(), vec![&app_out, &lib_out]);
    }

    #[test]
    fn dry_clean_does_not_remove() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let app = parse_tsconfig(&root, app_path(), r#"{"references": [{"path": "../lib"}]}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();

        let lib_out = abs("/workspace/test/lib/lib.js");
        let app_out = abs("/workspace/test/app/app.js");

        let mut host = InMemoryHost::new()
            .with_declared_outputs(&lib_path(), BTreeSet::from([lib_out.clone()]))
            .with_declared_outputs(&app_path(), BTreeSet::from([app_out.clone()]))
            .with_output(lib_out.clone(), vec![b'j', b's'])
            .with_output(app_out.clone(), vec![b'j', b's']);

        let options = BuildOptions {
            clean: true,
            dry_run: true,
            ..BuildOptions::default()
        };
        let report = clean(&graph, &mut host, &root, &options).unwrap();

        assert_eq!(report.cleaned(), vec![&app_out, &lib_out]);
        assert!(!host.outputs.is_empty()); // outputs still present
    }

    #[test]
    fn clean_rejects_escaping_outputs() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&lib]).unwrap();

        let mut host = InMemoryHost::new()
            .with_declared_outputs(&lib_path(), BTreeSet::from([abs("/outside/root.js")]));

        let options = BuildOptions {
            clean: true,
            ..BuildOptions::default()
        };
        let err = clean(&graph, &mut host, &root, &options).unwrap_err();
        assert!(matches!(err, BuildError::Path(_)));
    }

    #[test]
    fn verbose_emits_ordered_log() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&lib]).unwrap();

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), parse_config(&root, lib_path(), r#"{}"#))
            .with_compile_output(&lib_path(), build_output(abs("/workspace/test/lib/lib.js")));

        let options = BuildOptions {
            verbose: true,
            ..BuildOptions::default()
        };
        let report = execute(&graph, &mut host, &root, &options).unwrap();

        assert!(!report.log.is_empty());
        assert!(report.log.iter().any(|m| m.contains("checking")));
        assert!(report.log.iter().any(|m| m.contains("building")));
    }

    #[test]
    fn identical_state_produces_identical_report() {
        let root = test_root();
        let lib = parse_tsconfig(
            &root,
            lib_path(),
            r#"{"compilerOptions": {"composite": true}}"#,
        );
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&lib]).unwrap();

        let lib_info = graph
            .node(lib_path().as_path())
            .unwrap()
            .build_info_path
            .clone()
            .unwrap();
        let lib_config = parse_config(
            &root,
            lib_path(),
            r#"{"compilerOptions": {"composite": true}}"#,
        );
        let lib_sources =
            BTreeMap::from([(abs("/workspace/test/lib/a.ts"), source_signature("lib v1"))]);
        let lib_sig = project_signature(
            graph.node(lib_path().as_path()).unwrap(),
            &options_signature(&lib_config),
            &lib_sources,
            &BTreeMap::new(),
        );

        let build_info = BuildInfo {
            version: Arc::from(BUILD_INFO_SCHEMA),
            options: options_signature(&lib_config),
            sources: lib_sources.clone(),
            outputs: BTreeSet::from([abs("/workspace/test/lib/lib.js")]),
            signature: lib_sig,
        };

        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), lib_config)
            .with_source_signatures(&lib_path(), lib_sources)
            .with_build_info(&lib_info, build_info)
            .with_declared_outputs(
                &lib_path(),
                BTreeSet::from([abs("/workspace/test/lib/lib.js")]),
            )
            .with_output(abs("/workspace/test/lib/lib.js"), vec![b'j', b's']);

        let first = execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();
        let second = execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();
        assert_eq!(first, second);
        assert_eq!(first.actions, vec![BuildAction::Skip(lib_path())]);
    }

    #[test]
    fn atomic_output_uses_temp_and_rename() {
        let root = test_root();
        let lib = parse_tsconfig(&root, lib_path(), r#"{}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&lib]).unwrap();

        let out = abs("/workspace/test/lib/lib.js");
        let mut host = InMemoryHost::new()
            .with_config(&lib_path(), parse_config(&root, lib_path(), r#"{}"#))
            .with_compile_output(&lib_path(), build_output(&out));

        execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();

        assert!(host.outputs.contains_key(&out));
        let expected_temp = temp_path(&out);
        assert!(
            host.rename_log
                .iter()
                .any(|(from, to)| from == &expected_temp && to == &out)
        );
    }
    fn sample_build_info() -> BuildInfo {
        BuildInfo {
            version: Arc::from(BUILD_INFO_SCHEMA),
            options: Arc::from(r#"{"composite":true,"strict":false}"#),
            sources: BTreeMap::from([
                (
                    abs("/workspace/test/app/a.ts"),
                    source_signature("export const a = 1;"),
                ),
                (
                    abs("/workspace/test/app/b.ts"),
                    source_signature("export const b = 2;"),
                ),
            ]),
            outputs: BTreeSet::from([
                abs("/workspace/test/app/a.js"),
                abs("/workspace/test/app/b.js"),
            ]),
            signature: Arc::from("0123456789abcdef"),
        }
    }

    #[test]
    fn build_info_codec_round_trip_is_byte_identical() {
        let info = sample_build_info();
        let first = info.encode().unwrap();
        let decoded = BuildInfo::decode(&first).unwrap();
        let second = decoded.encode().unwrap();

        assert_eq!(decoded, info);
        assert_eq!(second, first);
    }

    #[test]
    fn build_info_encoding_is_independent_of_insertion_order() {
        let canonical = sample_build_info();
        let mut reversed_sources = BTreeMap::new();
        for (path, digest) in canonical.sources.iter().rev() {
            reversed_sources.insert(path.clone(), digest.clone());
        }
        let mut reversed_outputs = BTreeSet::new();
        for path in canonical.outputs.iter().rev() {
            reversed_outputs.insert(path.clone());
        }
        let reordered = BuildInfo {
            sources: reversed_sources,
            outputs: reversed_outputs,
            ..canonical.clone()
        };

        assert_eq!(reordered.encode().unwrap(), canonical.encode().unwrap());
    }

    #[test]
    fn build_info_decoder_rejects_every_truncated_prefix() {
        let bytes = sample_build_info().encode().unwrap();
        for end in 0..bytes.len() {
            assert!(
                BuildInfo::decode(&bytes[..end]).is_err(),
                "prefix ending at byte {end} unexpectedly decoded"
            );
        }
    }

    #[test]
    fn build_info_decoder_rejects_unknown_version() {
        let mut text = String::from_utf8(sample_build_info().encode().unwrap()).unwrap();
        text = text.replacen(BUILD_INFO_SCHEMA, "bamts-build-2", 1);

        assert_eq!(
            BuildInfo::decode(text.as_bytes()),
            Err(BuildInfoDecodeError::UnsupportedVersion {
                found: "bamts-build-2".to_string()
            })
        );
    }

    #[test]
    fn build_info_decoder_rejects_noncanonical_and_trailing_bytes() {
        let bytes = sample_build_info().encode().unwrap();
        let mut whitespace = bytes.clone();
        whitespace.insert(1, b' ');
        assert!(matches!(
            BuildInfo::decode(&whitespace),
            Err(BuildInfoDecodeError::Expected { .. })
        ));

        let mut trailing = bytes;
        trailing.push(b'\n');
        assert!(matches!(
            BuildInfo::decode(&trailing),
            Err(BuildInfoDecodeError::TrailingBytes { .. })
        ));
    }

    #[test]
    fn build_info_decoder_rejects_duplicate_and_unsorted_paths() {
        let digest = source_signature("source");
        let a = abs_json("/workspace/a.ts");
        let duplicate = format!(
            "{{\"version\":\"{BUILD_INFO_SCHEMA}\",\"options\":\"null\",\"signature\":\"0123456789abcdef\",\"sources\":[[\"{a}\",\"{digest}\"],[\"{a}\",\"{digest}\"]],\"outputs\":[]}}"
        );
        assert_eq!(
            BuildInfo::decode(duplicate.as_bytes()),
            Err(BuildInfoDecodeError::DuplicatePath {
                path: abs("/workspace/a.ts")
            })
        );

        let b = abs_json("/workspace/b.ts");
        let unsorted = format!(
            "{{\"version\":\"{BUILD_INFO_SCHEMA}\",\"options\":\"null\",\"signature\":\"0123456789abcdef\",\"sources\":[[\"{b}\",\"{digest}\"],[\"{a}\",\"{digest}\"]],\"outputs\":[]}}"
        );
        assert_eq!(
            BuildInfo::decode(unsorted.as_bytes()),
            Err(BuildInfoDecodeError::UnsortedPath {
                previous: abs("/workspace/b.ts"),
                found: abs("/workspace/a.ts")
            })
        );
    }

    #[test]
    fn build_info_decoder_rejects_invalid_digest_and_path() {
        let a = abs_json("/workspace/a.ts");
        let invalid_digest = format!(
            "{{\"version\":\"{BUILD_INFO_SCHEMA}\",\"options\":\"null\",\"signature\":\"0123456789abcdef\",\"sources\":[[\"{a}\",\"g{}\"]],\"outputs\":[]}}",
            "0".repeat(SOURCE_DIGEST_HEX_LEN - 1)
        );
        assert!(matches!(
            BuildInfo::decode(invalid_digest.as_bytes()),
            Err(BuildInfoDecodeError::InvalidSourceDigest { .. })
        ));

        let digest = source_signature("source");
        let outside = abs_json("/workspace/../outside.ts");
        let traversal = format!(
            "{{\"version\":\"{BUILD_INFO_SCHEMA}\",\"options\":\"null\",\"signature\":\"0123456789abcdef\",\"sources\":[[\"{outside}\",\"{digest}\"]],\"outputs\":[]}}"
        );
        assert_eq!(
            BuildInfo::decode(traversal.as_bytes()),
            Err(BuildInfoDecodeError::InvalidPath {
                path: abs_text("/workspace/../outside.ts")
            })
        );
    }

    #[test]
    fn source_signature_matches_sha256_vectors() {
        assert_eq!(
            &*source_signature(""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            &*source_signature("abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn source_digest_mutation_invalidates_incremental_state() {
        let root = test_root();
        let lib = parse_tsconfig(
            &root,
            lib_path(),
            r#"{"compilerOptions":{"composite":true}}"#,
        );
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&lib]).unwrap();
        let node = graph.node(lib_path().as_path()).unwrap();
        let config = parse_config(
            &root,
            lib_path(),
            r#"{"compilerOptions":{"composite":true}}"#,
        );
        let options = options_signature(&config);
        let source_path = abs("/workspace/test/lib/a.ts");
        let sources = BTreeMap::from([(source_path.clone(), source_signature("original"))]);
        let outputs = BTreeSet::from([abs("/workspace/test/lib/lib.js")]);
        let signature = project_signature(node, &options, &sources, &BTreeMap::new());
        let info = BuildInfo {
            version: Arc::from(BUILD_INFO_SCHEMA),
            options: options.clone(),
            sources: sources.clone(),
            outputs: outputs.clone(),
            signature,
        };
        assert!(is_project_up_to_date(
            &info,
            node,
            &options,
            &sources,
            &BTreeMap::new(),
            &outputs
        ));

        let original_digest = source_signature("original");
        let mutated_digest = source_signature("mutated");
        let mut bytes = String::from_utf8(info.encode().unwrap()).unwrap();
        bytes = bytes.replacen(&*original_digest, &mutated_digest, 1);
        let mutated = BuildInfo::decode(bytes.as_bytes()).unwrap();
        assert!(!is_project_up_to_date(
            &mutated,
            node,
            &options,
            &sources,
            &BTreeMap::new(),
            &outputs
        ));
    }

    #[test]
    fn host_stores_the_exact_canonical_bytes() {
        let root = test_root();
        let lib = parse_tsconfig(
            &root,
            lib_path(),
            r#"{"compilerOptions":{"composite":true}}"#,
        );
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&lib]).unwrap();
        let info_path = graph
            .node(lib_path().as_path())
            .unwrap()
            .build_info_path
            .clone()
            .unwrap();
        let source_path = abs("/workspace/test/lib/a.ts");
        let source_signatures =
            BTreeMap::from([(source_path, source_signature("export const a = 1;"))]);
        let output_path = abs("/workspace/test/lib/lib.js");
        let mut host = InMemoryHost::new()
            .with_config(
                &lib_path(),
                parse_config(
                    &root,
                    lib_path(),
                    r#"{"compilerOptions":{"composite":true}}"#,
                ),
            )
            .with_source_signatures(&lib_path(), source_signatures)
            .with_compile_output(&lib_path(), build_output(&output_path))
            .with_declared_outputs(&lib_path(), BTreeSet::from([output_path]));

        execute(&graph, &mut host, &root, &BuildOptions::default()).unwrap();
        let stored = host.build_infos.get(&info_path).unwrap();
        let decoded = BuildInfo::decode(stored).unwrap();
        assert_eq!(&decoded.encode().unwrap(), stored);
    }
}
