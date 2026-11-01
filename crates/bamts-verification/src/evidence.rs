//! Closed evidence types and strict JSONL streaming.
//!
//! A document is exactly one header, then zero-or-more strictly increasing
//! rows, then one footer.  Readers reject blank, malformed, duplicate,
//! out-of-order, and trailing records, and they refuse any JSON value that
//! does not consume the whole line.  Publication writes a sibling temporary
//! file and only then renames it into place; check mode never mutates the
//! destination.  K-way merge keeps one live row per shard.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::{self, BufRead, BufReader, Write},
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    ErrorCode, Result, VerificationError,
    corpus::NORMALIZED_ENV,
    shard::{ObligationKey, ShardIdentity, ShardSpec, hex_digest, require_sha256, require_token},
};

const EVIDENCE_SCHEMA: &str = "bamti.evidence/v2";
const RUNNER_VERSION: &str = "a2.2";

/// Schema tag bound into every evidence header.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EvidenceSchema {
    #[serde(rename = "bamti.evidence/v2")]
    V2,
}

impl EvidenceSchema {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        EVIDENCE_SCHEMA
    }
}

/// Closed terminal states.  `Pass` is recorded only after parent derivation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum TerminalState {
    Pass,
    BlockingFail,
    InapplicableLanguageService,
    InapplicableOutOfScopeHostFeature,
    InapplicableV8Internal,
    InapplicableCatalogError,
    ExternalBlocked,
    Timeout,
    Signal,
    ProtocolError,
    WorkerCrash,
}

impl TerminalState {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::BlockingFail => "BLOCKING_FAIL",
            Self::InapplicableLanguageService => "INAPPLICABLE_LANGUAGE_SERVICE",
            Self::InapplicableOutOfScopeHostFeature => "INAPPLICABLE_OUT_OF_SCOPE_HOST_FEATURE",
            Self::InapplicableV8Internal => "INAPPLICABLE_V8_INTERNAL",
            Self::InapplicableCatalogError => "INAPPLICABLE_CATALOG_ERROR",
            Self::ExternalBlocked => "EXTERNAL_BLOCKED",
            Self::Timeout => "TIMEOUT",
            Self::Signal => "SIGNAL",
            Self::ProtocolError => "PROTOCOL_ERROR",
            Self::WorkerCrash => "WORKER_CRASH",
        }
    }

    #[must_use]
    pub const fn is_pass(self) -> bool {
        matches!(self, Self::Pass)
    }
}

/// Working-directory policy recorded with a receipt.  Closed: no raw paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WorkingDirectoryPolicy {
    RepositoryRoot,
}

/// Toolchain pin bound into every v2 run binding.
///
/// Records the exact Rust toolchain that compiled the harness and candidate
/// binary, so a receipt set is stale when either the `rustc` version or the
/// `rust-toolchain.toml` content changes — even if the source tree is clean.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolchainPin {
    rustc_version: String,
    rust_toolchain_toml_digest: String,
}

impl ToolchainPin {
    pub fn new(
        rustc_version: impl Into<String>,
        rust_toolchain_toml_digest: impl Into<String>,
    ) -> Result<Self> {
        let pin = Self {
            rustc_version: rustc_version.into(),
            rust_toolchain_toml_digest: rust_toolchain_toml_digest.into(),
        };
        pin.validate()?;
        Ok(pin)
    }

    pub(crate) fn validate(&self) -> Result<()> {
        require_token("rustc_version", &self.rustc_version)?;
        require_sha256(
            "rust_toolchain_toml_digest",
            &self.rust_toolchain_toml_digest,
        )?;
        Ok(())
    }

    #[must_use]
    pub fn rustc_version(&self) -> &str {
        &self.rustc_version
    }

    #[must_use]
    pub fn rust_toolchain_toml_digest(&self) -> &str {
        &self.rust_toolchain_toml_digest
    }
}

/// Binding shared by every shard of one run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunBinding {
    authority_digest: String,
    candidate_tree_digest: String,
    candidate_binary_digest: String,
    harness_digest: String,
    environment: Vec<String>,
    runner_version: String,
    toolchain: ToolchainPin,
}
impl RunBinding {
    pub fn new(
        authority_digest: impl Into<String>,
        candidate_tree_digest: impl Into<String>,
        candidate_binary_digest: impl Into<String>,
        harness_digest: impl Into<String>,
        toolchain: ToolchainPin,
    ) -> Result<Self> {
        let binding = Self {
            authority_digest: authority_digest.into(),
            candidate_tree_digest: candidate_tree_digest.into(),
            candidate_binary_digest: candidate_binary_digest.into(),
            harness_digest: harness_digest.into(),
            environment: NORMALIZED_ENV
                .iter()
                .map(|entry| (*entry).to_owned())
                .collect(),
            runner_version: RUNNER_VERSION.to_owned(),
            toolchain,
        };
        binding.validate()?;
        Ok(binding)
    }

    pub(crate) fn validate(&self) -> Result<()> {
        self.validate_common()?;
        if self.runner_version != RUNNER_VERSION {
            return Err(schema(format!(
                "runner_version `{}` is not `{RUNNER_VERSION}`",
                self.runner_version
            )));
        }
        Ok(())
    }

    fn validate_common(&self) -> Result<()> {
        require_sha256("authority_digest", &self.authority_digest)?;
        require_sha256("candidate_tree_digest", &self.candidate_tree_digest)?;
        require_sha256("candidate_binary_digest", &self.candidate_binary_digest)?;
        require_sha256("harness_digest", &self.harness_digest)?;
        self.toolchain.validate()?;
        if self.environment.len() != NORMALIZED_ENV.len()
            || self
                .environment
                .iter()
                .zip(NORMALIZED_ENV)
                .any(|(actual, expected)| actual != expected)
        {
            return Err(schema(
                "evidence environment must equal the canonical normalized environment",
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn authority_digest(&self) -> &str {
        &self.authority_digest
    }

    #[must_use]
    pub fn environment(&self) -> &[String] {
        &self.environment
    }

    #[must_use]
    pub fn toolchain(&self) -> &ToolchainPin {
        &self.toolchain
    }

    pub(crate) fn first_mismatch_field(&self, actual: &Self) -> Option<&'static str> {
        [
            (
                "authority_digest",
                self.authority_digest == actual.authority_digest,
            ),
            (
                "candidate_tree_digest",
                self.candidate_tree_digest == actual.candidate_tree_digest,
            ),
            (
                "candidate_binary_digest",
                self.candidate_binary_digest == actual.candidate_binary_digest,
            ),
            (
                "harness_digest",
                self.harness_digest == actual.harness_digest,
            ),
            ("environment", self.environment == actual.environment),
            (
                "runner_version",
                self.runner_version == actual.runner_version,
            ),
            ("toolchain", self.toolchain == actual.toolchain),
        ]
        .into_iter()
        .find_map(|(field, matches)| (!matches).then_some(field))
    }

    #[cfg(test)]
    pub(crate) fn same_run_as(&self, other: &Self) -> bool {
        self.candidate_tree_digest == other.candidate_tree_digest
            && self.candidate_binary_digest == other.candidate_binary_digest
            && self.harness_digest == other.harness_digest
            && self.environment == other.environment
            && self.runner_version == other.runner_version
            && self.toolchain == other.toolchain
    }
}
/// Exact workflow execution that produced one receipt matrix.
///
/// Content digests bind the candidate; this binding additionally prevents
/// shards from another workflow, rerun, commit, host, or runtime image from
/// being merged into the same receipt set.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExecutionBinding {
    workflow: String,
    run_id: String,
    run_attempt: u32,
    source_sha: String,
    job: String,
    host: String,
    runtime: String,
}

impl ExecutionBinding {
    pub fn new(
        workflow: impl Into<String>,
        run_id: impl Into<String>,
        run_attempt: u32,
        source_sha: impl Into<String>,
        job: impl Into<String>,
        host: impl Into<String>,
        runtime: impl Into<String>,
    ) -> Result<Self> {
        let binding = Self {
            workflow: workflow.into(),
            run_id: run_id.into(),
            run_attempt,
            source_sha: source_sha.into(),
            job: job.into(),
            host: host.into(),
            runtime: runtime.into(),
        };
        binding.validate()?;
        Ok(binding)
    }

    #[cfg(test)]
    pub(crate) fn local_for_tests() -> Self {
        Self {
            workflow: "local-test".to_owned(),
            run_id: "local-test".to_owned(),
            run_attempt: 1,
            source_sha: "0000000000000000000000000000000000000000".to_owned(),
            job: "local-test".to_owned(),
            host: "local-test".to_owned(),
            runtime: "local-test".to_owned(),
        }
    }

    pub fn validate(&self) -> Result<()> {
        for (field, value) in [
            ("workflow", self.workflow.as_str()),
            ("run_id", self.run_id.as_str()),
            ("job", self.job.as_str()),
            ("host", self.host.as_str()),
            ("runtime", self.runtime.as_str()),
        ] {
            require_token(field, value)?;
        }
        if self.run_attempt == 0 {
            return Err(schema("run_attempt must be greater than zero"));
        }
        if self.source_sha.len() != 40
            || !self
                .source_sha
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(schema(
                "source_sha must be a lowercase 40-character Git SHA",
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn first_mismatch_field(&self, actual: &Self) -> Option<&'static str> {
        [
            ("workflow", self.workflow == actual.workflow),
            ("run_id", self.run_id == actual.run_id),
            ("run_attempt", self.run_attempt == actual.run_attempt),
            ("source_sha", self.source_sha == actual.source_sha),
            ("job", self.job == actual.job),
            ("host", self.host == actual.host),
            ("runtime", self.runtime == actual.runtime),
        ]
        .into_iter()
        .find_map(|(field, matches)| (!matches).then_some(field))
    }
}

/// Header bound to one shard of one catalog run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceHeader {
    schema: EvidenceSchema,
    shard: ShardIdentity,
    binding: RunBinding,
    execution: ExecutionBinding,
}

impl EvidenceHeader {
    pub fn new(
        shard: ShardIdentity,
        binding: RunBinding,
        execution: ExecutionBinding,
    ) -> Result<Self> {
        let header = Self {
            schema: EvidenceSchema::V2,
            shard,
            binding,
            execution,
        };
        header.validate()?;
        Ok(header)
    }

    pub(crate) fn validate(&self) -> Result<()> {
        self.binding.validate()?;
        self.execution.validate()?;
        ShardSpec::new(self.shard.spec().index(), self.shard.spec().count())?;
        if self.shard.expected_count() == 0 || self.shard.catalog_len() == 0 {
            return Err(schema("evidence header cannot describe an empty shard"));
        }
        if self.shard.spec().count() as usize > self.shard.catalog_len() {
            return Err(schema("shard count exceeds catalog length"));
        }
        require_sha256("catalog_digest", self.shard.catalog_digest())?;
        require_sha256("obligation_set_digest", self.shard.obligation_set_digest())?;
        Ok(())
    }

    #[must_use]
    pub fn shard(&self) -> &ShardIdentity {
        &self.shard
    }

    #[must_use]
    pub fn binding(&self) -> &RunBinding {
        &self.binding
    }
    #[must_use]
    pub fn execution(&self) -> &ExecutionBinding {
        &self.execution
    }

    pub fn unsharded(self) -> Result<Self> {
        let spec = ShardSpec::unsharded();
        let shard = ShardIdentity::from_parts(
            spec,
            self.shard.catalog_digest().to_owned(),
            self.shard.catalog_len(),
            self.shard.catalog_len(),
            self.shard.catalog_digest().to_owned(),
        )?;
        Self::new(shard, self.binding, self.execution)
    }
}

/// One receipt row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceRow {
    key: ObligationKey,
    argv: Vec<String>,
    working_directory: WorkingDirectoryPolicy,
    observables: BTreeSet<String>,
    artifacts: BTreeMap<String, String>,
    state: TerminalState,
    duration_ms: u64,
    detail: String,
}

impl EvidenceRow {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        key: ObligationKey,
        argv: Vec<String>,
        working_directory: WorkingDirectoryPolicy,
        observables: BTreeSet<String>,
        artifacts: BTreeMap<String, String>,
        state: TerminalState,
        duration_ms: u64,
        detail: impl Into<String>,
    ) -> Result<Self> {
        let row = Self {
            key,
            argv,
            working_directory,
            observables,
            artifacts,
            state,
            duration_ms,
            detail: detail.into(),
        };
        row.validate()?;
        Ok(row)
    }

    pub(crate) fn validate(&self) -> Result<()> {
        self.key.validate()?;
        if self.observables.is_empty() {
            return Err(schema(format!(
                "obligation `{}` declares no observables",
                self.key
            )));
        }
        for observable in &self.observables {
            require_token("observable", observable)?;
        }
        if self.state.is_pass() {
            if self.artifacts.len() != self.observables.len()
                || self
                    .observables
                    .iter()
                    .any(|observable| !self.artifacts.contains_key(observable))
            {
                return Err(schema(format!(
                    "PASS row `{}` artifacts must equal declared observables",
                    self.key
                )));
            }
            for (name, digest) in &self.artifacts {
                require_sha256(name, digest)?;
            }
        } else if !self.artifacts.is_empty() {
            for (name, digest) in &self.artifacts {
                if !self.observables.contains(name) {
                    return Err(schema(format!(
                        "row `{}` records undeclared artifact `{name}`",
                        self.key
                    )));
                }
                require_sha256(name, digest)?;
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn key(&self) -> &ObligationKey {
        &self.key
    }

    #[must_use]
    pub fn argv(&self) -> &[String] {
        &self.argv
    }

    #[must_use]
    pub fn state(&self) -> TerminalState {
        self.state
    }

    #[must_use]
    pub fn observables(&self) -> &BTreeSet<String> {
        &self.observables
    }

    #[must_use]
    pub fn artifacts(&self) -> &BTreeMap<String, String> {
        &self.artifacts
    }

    /// The diagnostic text recorded with the state; empty on a clean `PASS`.
    #[must_use]
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

/// Footer that closes a stream.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceFooter {
    row_count: usize,
    obligation_set_digest: String,
}

impl EvidenceFooter {
    pub fn new(row_count: usize, obligation_set_digest: impl Into<String>) -> Result<Self> {
        let digest = obligation_set_digest.into();
        require_sha256("obligation_set_digest", &digest)?;
        Ok(Self {
            row_count,
            obligation_set_digest: digest,
        })
    }

    #[must_use]
    pub fn row_count(&self) -> usize {
        self.row_count
    }

    #[must_use]
    pub fn obligation_set_digest(&self) -> &str {
        &self.obligation_set_digest
    }
}

/// One JSONL record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "record", content = "body", deny_unknown_fields)]
pub enum EvidenceRecord {
    #[serde(rename = "header")]
    Header(EvidenceHeader),
    #[serde(rename = "row")]
    Row(EvidenceRow),
    #[serde(rename = "footer")]
    Footer(EvidenceFooter),
}

/// Replace the destination or compare against it without mutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PublishMode {
    Replace,
    Check,
}

/// Streaming JSONL writer.  Memory is one row plus running digest state.
pub struct EvidenceWriter<W> {
    write: W,
    header: EvidenceHeader,
    last_key: Option<ObligationKey>,
    rows_seen: usize,
    hasher: Sha256,
    finished: bool,
}

impl<W: Write> EvidenceWriter<W> {
    pub fn new(mut write: W, header: EvidenceHeader) -> Result<Self> {
        header.validate()?;
        write_record(&mut write, &EvidenceRecord::Header(header.clone()))?;
        Ok(Self {
            write,
            header,
            last_key: None,
            rows_seen: 0,
            hasher: Sha256::new(),
            finished: false,
        })
    }

    pub fn write_row(&mut self, row: &EvidenceRow) -> Result<()> {
        if self.finished {
            return Err(schema("cannot write a row after the evidence footer"));
        }
        row.validate()?;
        if let Some(previous) = &self.last_key
            && row.key() <= previous
        {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!(
                    "evidence rows are not strictly increasing: `{previous}` then `{}`",
                    row.key()
                ),
            ));
        }
        if self.rows_seen >= self.header.shard().expected_count() {
            return Err(schema(format!(
                "shard {}/{} has extra row `{}`",
                self.header.shard().spec().index(),
                self.header.shard().spec().count(),
                row.key()
            )));
        }
        self.hasher.update(row.key().canonical_bytes());
        self.hasher.update([0x0a]);
        write_record(&mut self.write, &EvidenceRecord::Row(row.clone()))?;
        self.last_key = Some(row.key().clone());
        self.rows_seen += 1;
        Ok(())
    }

    pub fn finish(mut self) -> Result<()> {
        if self.finished {
            return Ok(());
        }
        if self.rows_seen != self.header.shard().expected_count() {
            return Err(VerificationError::new(
                ErrorCode::SetMismatch,
                format!(
                    "shard {}/{} expected {} rows, wrote {}",
                    self.header.shard().spec().index(),
                    self.header.shard().spec().count(),
                    self.header.shard().expected_count(),
                    self.rows_seen
                ),
            ));
        }
        let digest = hex_digest(self.hasher.clone());
        if digest != self.header.shard().obligation_set_digest() {
            return Err(VerificationError::new(
                ErrorCode::Digest,
                "written obligation-set digest does not match the shard header",
            ));
        }
        let footer = EvidenceFooter::new(self.rows_seen, digest)?;
        write_record(&mut self.write, &EvidenceRecord::Footer(footer))?;
        self.write.flush().map_err(io_err)?;
        Ok(())
    }
}

/// Streaming JSONL reader.  Memory is one line plus running digest state.
#[derive(Debug)]
pub struct EvidenceReader<R> {
    reader: R,
    header: EvidenceHeader,
    last_key: Option<ObligationKey>,
    rows_seen: usize,
    hasher: Sha256,
    finished: bool,
}

impl EvidenceReader<BufReader<File>> {
    pub fn open(path: &Path) -> Result<Self> {
        let file = File::open(path).map_err(|error| io_path(path, error))?;
        Self::from_reader(BufReader::new(file))
    }
}

impl<R: BufRead> EvidenceReader<R> {
    pub fn from_reader(mut reader: R) -> Result<Self> {
        let header_line = read_required_line(&mut reader, "header")?;
        let record = parse_record(&header_line)?;
        let EvidenceRecord::Header(header) = record else {
            return Err(schema("evidence stream must start with a header record"));
        };
        header.validate()?;
        Ok(Self {
            reader,
            header,
            last_key: None,
            rows_seen: 0,
            hasher: Sha256::new(),
            finished: false,
        })
    }

    #[must_use]
    pub fn header(&self) -> &EvidenceHeader {
        &self.header
    }

    pub fn next_row(&mut self) -> Result<Option<EvidenceRow>> {
        if self.finished {
            return Ok(None);
        }
        let line = match read_jsonl_line(&mut self.reader)? {
            None => return Err(schema("evidence stream ended before a footer record")),
            Some(line) => line,
        };
        match parse_record(&line)? {
            EvidenceRecord::Header(_) => Err(schema("evidence stream contains a second header")),
            EvidenceRecord::Row(row) => {
                row.validate()?;
                if let Some(previous) = &self.last_key
                    && row.key() <= previous
                {
                    return Err(VerificationError::new(
                        ErrorCode::Duplicate,
                        format!(
                            "evidence rows are not strictly increasing: `{previous}` then `{}`",
                            row.key()
                        ),
                    ));
                }
                if self.rows_seen >= self.header.shard().expected_count() {
                    return Err(schema(format!(
                        "shard {}/{} has extra row `{}`",
                        self.header.shard().spec().index(),
                        self.header.shard().spec().count(),
                        row.key()
                    )));
                }
                self.hasher.update(row.key().canonical_bytes());
                self.hasher.update([0x0a]);
                self.last_key = Some(row.key().clone());
                self.rows_seen += 1;
                Ok(Some(row))
            }
            EvidenceRecord::Footer(footer) => {
                footer_matches(
                    &self.header,
                    self.rows_seen,
                    hex_digest(self.hasher.clone()),
                    &footer,
                )?;
                if read_jsonl_line(&mut self.reader)?.is_some() {
                    return Err(schema(
                        "evidence stream has trailing records after the footer",
                    ));
                }
                self.finished = true;
                Ok(None)
            }
        }
    }

    pub fn finish(mut self) -> Result<EvidenceFooter> {
        while self.next_row()?.is_some() {}
        if !self.finished {
            return Err(schema("evidence stream ended before a footer record"));
        }
        EvidenceFooter::new(self.rows_seen, hex_digest(self.hasher))
    }
}

/// Publishes a closed evidence document.  Check mode never mutates `dest`.
pub fn publish_evidence(
    dest: &Path,
    header: EvidenceHeader,
    rows: &[EvidenceRow],
    mode: PublishMode,
) -> Result<()> {
    publish_streaming(dest, header, rows.iter().cloned(), mode, None)
}

/// Like [`publish_evidence`], with an optional injected write failure for tests.
pub fn publish_streaming_with_fault(
    dest: &Path,
    header: EvidenceHeader,
    rows: Vec<EvidenceRow>,
    mode: PublishMode,
    fail_after_bytes: Option<usize>,
) -> Result<()> {
    publish_streaming(dest, header, rows, mode, fail_after_bytes)
}

fn publish_streaming<I>(
    dest: &Path,
    header: EvidenceHeader,
    rows: I,
    mode: PublishMode,
    fail_after_bytes: Option<usize>,
) -> Result<()>
where
    I: IntoIterator<Item = EvidenceRow>,
{
    let parent = dest
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|error| io_path(parent, error))?;
    let temp = sibling_temp(dest);
    let outcome = (|| {
        let file = File::create(&temp).map_err(|error| io_path(&temp, error))?;
        let mut write = FaultyWrite {
            inner: file,
            written: 0,
            fail_after_bytes,
        };
        let mut writer = EvidenceWriter::new(&mut write, header)?;
        for row in rows {
            writer.write_row(&row)?;
        }
        writer.finish()?;
        Ok(())
    })();
    if let Err(error) = outcome {
        let _ = fs::remove_file(&temp);
        return Err(error);
    }
    match mode {
        PublishMode::Replace => {
            fs::rename(&temp, dest).map_err(|error| io_path(dest, error))?;
        }
        PublishMode::Check => {
            let published = fs::read(&temp).map_err(|error| io_path(&temp, error))?;
            let _ = fs::remove_file(&temp);
            let existing = fs::read(dest).map_err(|error| io_path(dest, error))?;
            if published != existing {
                return Err(VerificationError::new(
                    ErrorCode::Digest,
                    format!(
                        "{} differs from the published evidence image",
                        dest.display()
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// K-way merge of shard documents against the canonical catalog order.
///
/// Memory is one live row per shard plus the destination writer.
pub fn merge_shards(
    paths: &[PathBuf],
    catalog: &[ObligationKey],
    dest: &Path,
    mode: PublishMode,
) -> Result<()> {
    crate::shard::validate_catalog(catalog)?;
    if paths.is_empty() {
        return Err(schema("merge requires at least one shard"));
    }
    let mut readers = Vec::with_capacity(paths.len());
    let mut heads: Vec<Option<EvidenceRow>> = Vec::with_capacity(paths.len());
    let mut by_index: BTreeMap<u32, usize> = BTreeMap::new();
    let mut binding = None;
    let mut execution = None;
    let mut catalog_digest = None;
    let mut shard_count = None;
    for (slot, path) in paths.iter().enumerate() {
        let mut reader = EvidenceReader::open(path)?;
        let spec = reader.header().shard().spec();
        if reader.header().shard().catalog_len() != catalog.len() {
            return Err(VerificationError::new(
                ErrorCode::SetMismatch,
                "shard catalog length does not match the merge catalog",
            ));
        }
        match shard_count {
            None => shard_count = Some(spec.count()),
            Some(count) if count != spec.count() => {
                return Err(schema("merged shards do not share a matrix count"));
            }
            Some(_) => {}
        }
        if spec.count() as usize != paths.len() {
            return Err(schema("merge requires the complete shard matrix"));
        }
        if by_index.insert(spec.index(), slot).is_some() {
            return Err(schema(format!("duplicate shard index {}", spec.index())));
        }
        let digest = reader.header().shard().catalog_digest().to_owned();
        match &catalog_digest {
            None => catalog_digest = Some(digest),
            Some(expected) if expected != &digest => {
                return Err(VerificationError::new(
                    ErrorCode::Digest,
                    "shard catalog digests do not agree",
                ));
            }
            Some(_) => {}
        }
        match &binding {
            None => binding = Some(reader.header().binding().clone()),
            Some(expected) => {
                if let Some(field) = expected.first_mismatch_field(reader.header().binding()) {
                    return Err(VerificationError::new(
                        ErrorCode::Digest,
                        format!("merged shard run binding differs at `{field}`"),
                    ));
                }
            }
        }
        let actual_execution = reader.header().execution();
        match &execution {
            None => execution = Some(actual_execution.clone()),
            Some(expected) => {
                if let Some(field) = expected.first_mismatch_field(actual_execution) {
                    return Err(VerificationError::new(
                        ErrorCode::Digest,
                        format!("merged shard execution binding differs at `{field}`"),
                    ));
                }
            }
        }
        let head = reader.next_row()?;
        readers.push(reader);
        heads.push(head);
    }
    let count = shard_count.ok_or_else(|| schema("merge produced no shard count"))?;
    if by_index.len() != count as usize {
        return Err(schema("merge is missing one or more shard indices"));
    }
    let expected_digest = crate::shard::digest_obligation_set(catalog.iter());
    if catalog_digest.as_deref() != Some(expected_digest.as_str()) {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            "merge catalog digest does not match the provided catalog",
        ));
    }
    let header = EvidenceHeader::new(
        ShardIdentity::from_parts(
            ShardSpec::unsharded(),
            expected_digest.clone(),
            catalog.len(),
            catalog.len(),
            expected_digest,
        )?,
        binding.ok_or_else(|| schema("merge produced no run binding"))?,
        execution.ok_or_else(|| schema("merge produced no execution binding"))?,
    )?;
    let parent = dest
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|error| io_path(parent, error))?;
    let temp = sibling_temp(dest);
    let outcome = (|| {
        let file = File::create(&temp).map_err(|error| io_path(&temp, error))?;
        let mut writer = EvidenceWriter::new(file, header)?;
        for (index, key) in catalog.iter().enumerate() {
            let owner = (index as u32) % count;
            let slot = *by_index
                .get(&owner)
                .ok_or_else(|| schema(format!("no shard owns catalog index {index}")))?;
            let Some(row) = heads[slot].take() else {
                return Err(VerificationError::new(
                    ErrorCode::SetMismatch,
                    format!("missing shard row for `{key}`"),
                ));
            };
            if row.key() != key {
                return Err(VerificationError::new(
                    ErrorCode::SetMismatch,
                    format!("expected `{key}` from shard {owner}, found `{}`", row.key()),
                ));
            }
            writer.write_row(&row)?;
            heads[slot] = readers[slot].next_row()?;
        }
        for (index, head) in heads.iter().enumerate() {
            if head.is_some() {
                return Err(schema(format!(
                    "shard {index} has leftover rows after merge"
                )));
            }
        }
        for reader in readers {
            reader.finish()?;
        }
        writer.finish()?;
        Ok(())
    })();
    if let Err(error) = outcome {
        let _ = fs::remove_file(&temp);
        return Err(error);
    }
    match mode {
        PublishMode::Replace => fs::rename(&temp, dest).map_err(|error| io_path(dest, error))?,
        PublishMode::Check => {
            let published = fs::read(&temp).map_err(|error| io_path(&temp, error))?;
            let _ = fs::remove_file(&temp);
            let existing = fs::read(dest).map_err(|error| io_path(dest, error))?;
            if published != existing {
                return Err(VerificationError::new(
                    ErrorCode::Digest,
                    "merged evidence does not match the destination",
                ));
            }
        }
    }
    Ok(())
}

struct FaultyWrite<W> {
    inner: W,
    written: usize,
    fail_after_bytes: Option<usize>,
}

impl<W: Write> Write for FaultyWrite<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if let Some(limit) = self.fail_after_bytes
            && self.written + buf.len() > limit
        {
            return Err(io::Error::other("injected evidence write failure"));
        }
        let wrote = self.inner.write(buf)?;
        self.written += wrote;
        Ok(wrote)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

fn footer_matches(
    header: &EvidenceHeader,
    rows_seen: usize,
    digest: String,
    footer: &EvidenceFooter,
) -> Result<()> {
    if rows_seen != header.shard().expected_count() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "stream row count {rows_seen} does not match expected {}",
                header.shard().expected_count()
            ),
        ));
    }
    if footer.row_count() != rows_seen {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            "footer row_count does not match the stream",
        ));
    }
    if digest != header.shard().obligation_set_digest() || digest != footer.obligation_set_digest()
    {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            "footer obligation-set digest does not match the stream",
        ));
    }
    Ok(())
}

fn write_record<W: Write>(write: &mut W, record: &EvidenceRecord) -> Result<()> {
    serde_json::to_writer(&mut *write, record).map_err(|error| {
        let code = if error.is_io() {
            ErrorCode::Io
        } else {
            ErrorCode::Json
        };
        VerificationError::new(code, format!("encode evidence record: {error}"))
    })?;
    write.write_all(b"\n").map_err(io_err)?;
    Ok(())
}

fn parse_record(line: &str) -> Result<EvidenceRecord> {
    let mut deserializer = serde_json::Deserializer::from_str(line);
    let record = EvidenceRecord::deserialize(&mut deserializer).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("malformed evidence record: {error}"),
        )
    })?;
    deserializer
        .end()
        .map_err(|_| schema("evidence record has trailing junk"))?;
    Ok(record)
}

fn read_required_line<R: BufRead>(reader: &mut R, what: &str) -> Result<String> {
    match read_jsonl_line(reader)? {
        None => Err(schema(format!("evidence stream ended before {what}"))),
        Some(line) => Ok(line),
    }
}

fn read_jsonl_line<R: BufRead>(reader: &mut R) -> Result<Option<String>> {
    let mut line = String::new();
    let read = reader.read_line(&mut line).map_err(io_err)?;
    if read == 0 {
        return Ok(None);
    }
    if line.contains('\r') {
        return Err(schema("evidence stream contains a CR character"));
    }
    if !line.ends_with('\n') {
        return Err(schema("evidence stream contains a partial line"));
    }
    line.pop();
    if line.is_empty() {
        return Err(schema("evidence stream contains a blank line"));
    }
    Ok(Some(line))
}

fn sibling_temp(dest: &Path) -> PathBuf {
    let name = dest
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("evidence.jsonl");
    dest.with_file_name(format!(".{name}.tmp"))
}

fn schema(detail: impl Into<String>) -> VerificationError {
    VerificationError::new(ErrorCode::Schema, detail)
}

fn io_err(error: io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, error.to_string())
}

fn io_path(path: &Path, error: io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::{ExecutionMode, ShardIdentity, ShardSpec};
    use std::time::{SystemTime, UNIX_EPOCH};

    const DIGEST: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    struct Scratch {
        root: PathBuf,
    }

    impl Scratch {
        fn new(label: &str) -> Self {
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("time")
                .as_nanos();
            let root = std::env::temp_dir().join(format!("bamts-evidence-{label}-{nanos}"));
            fs::create_dir_all(&root).expect("scratch");
            Self { root }
        }

        fn file(&self, name: &str) -> PathBuf {
            self.root.join(name)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    fn key(index: usize) -> ObligationKey {
        ObligationKey::new(
            "typescript-7.0.2",
            format!("case-{index:04}"),
            "default",
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key")
    }

    fn keys(len: usize) -> Vec<ObligationKey> {
        (0..len).map(key).collect()
    }

    fn toolchain_pin() -> ToolchainPin {
        ToolchainPin::new("rustc-1.97.1", DIGEST).expect("toolchain pin")
    }

    fn binding() -> RunBinding {
        RunBinding::new(DIGEST, DIGEST, DIGEST, DIGEST, toolchain_pin()).expect("binding")
    }

    fn row(index: usize, state: TerminalState) -> EvidenceRow {
        let mut artifacts = BTreeMap::new();
        if state.is_pass() {
            artifacts.insert("stdout".to_owned(), DIGEST.to_owned());
        }
        EvidenceRow::new(
            key(index),
            vec!["run".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            BTreeSet::from(["stdout".to_owned()]),
            artifacts,
            state,
            1,
            "",
        )
        .expect("row")
    }

    fn write_unsharded(path: &Path, catalog: &[ObligationKey], rows: &[EvidenceRow]) {
        let shard = ShardIdentity::plan(ShardSpec::unsharded(), catalog).expect("plan");
        let header = EvidenceHeader::new(shard, binding(), ExecutionBinding::local_for_tests())
            .expect("header");
        publish_evidence(path, header, rows, PublishMode::Replace).expect("publish");
    }

    fn write_shard(
        path: &Path,
        catalog: &[ObligationKey],
        index: u32,
        count: u32,
        rows: &[EvidenceRow],
    ) {
        write_shard_with_binding(path, catalog, index, count, rows, binding());
    }

    fn write_shard_with_binding(
        path: &Path,
        catalog: &[ObligationKey],
        index: u32,
        count: u32,
        rows: &[EvidenceRow],
        binding: RunBinding,
    ) {
        write_shard_with_execution(
            path,
            catalog,
            index,
            count,
            rows,
            binding,
            ExecutionBinding::local_for_tests(),
        );
    }

    fn write_shard_with_execution(
        path: &Path,
        catalog: &[ObligationKey],
        index: u32,
        count: u32,
        rows: &[EvidenceRow],
        binding: RunBinding,
        execution: ExecutionBinding,
    ) {
        let spec = ShardSpec::new(index, count).expect("spec");
        let shard = ShardIdentity::plan(spec, catalog).expect("plan");
        let header = EvidenceHeader::new(shard, binding, execution).expect("header");
        let owned: Vec<EvidenceRow> = spec
            .member_indices(catalog.len())
            .map(|member| rows[member].clone())
            .collect();
        publish_evidence(path, header, &owned, PublishMode::Replace).expect("publish");
    }

    fn consume(path: &Path) -> Result<()> {
        EvidenceReader::open(path)?.finish().map(|_| ())
    }

    #[test]
    fn missing_or_swapped_shard_fails_closure() {
        let catalog = keys(6);
        let rows: Vec<EvidenceRow> = (0..6)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("swap");
        let mut paths = Vec::new();
        for index in 0..3 {
            let path = scratch.file(&format!("shard-{index}.jsonl"));
            write_shard(&path, &catalog, index, 3, &rows);
            paths.push(path);
        }
        let dest = scratch.file("merged.jsonl");
        merge_shards(&paths, &catalog, &dest, PublishMode::Replace).expect("complete merge");

        let missing: Vec<PathBuf> = paths.iter().take(2).cloned().collect();
        assert!(
            merge_shards(
                &missing,
                &catalog,
                &scratch.file("missing.jsonl"),
                PublishMode::Replace
            )
            .is_err()
        );

        let shard0 = fs::read_to_string(&paths[0]).expect("read 0");
        let shard1 = fs::read_to_string(&paths[1]).expect("read 1");
        let header0 = shard0.lines().next().expect("header");
        let mut spliced = String::new();
        spliced.push_str(header0);
        spliced.push('\n');
        for line in shard1.lines().skip(1) {
            spliced.push_str(line);
            spliced.push('\n');
        }
        let swapped = scratch.file("swapped.jsonl");
        fs::write(&swapped, spliced).expect("write swap");
        assert!(consume(&swapped).is_err());
        let mixed = vec![swapped, paths[1].clone(), paths[2].clone()];
        assert!(
            merge_shards(
                &mixed,
                &catalog,
                &scratch.file("mixed.jsonl"),
                PublishMode::Replace
            )
            .is_err()
        );
    }

    #[test]
    fn merge_shards_rejects_mixed_run_binding() {
        const OTHER: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

        let catalog = keys(4);
        let rows: Vec<EvidenceRow> = (0..4)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("mixed-binding");
        let dest = scratch.file("merged.jsonl");
        fs::write(&dest, b"prior-ledger").expect("prior destination");

        for (label, stale) in [
            (
                "authority",
                RunBinding::new(OTHER, DIGEST, DIGEST, DIGEST, toolchain_pin()).expect("authority"),
            ),
            (
                "candidate-tree",
                RunBinding::new(DIGEST, OTHER, DIGEST, DIGEST, toolchain_pin()).expect("tree"),
            ),
        ] {
            let first = scratch.file(&format!("{label}-0.jsonl"));
            let second = scratch.file(&format!("{label}-1.jsonl"));
            write_shard_with_binding(&first, &catalog, 0, 2, &rows, binding());
            write_shard_with_binding(&second, &catalog, 1, 2, &rows, stale);

            let error = merge_shards(&[first, second], &catalog, &dest, PublishMode::Replace)
                .expect_err("mixed binding must fail");
            assert_eq!(error.code(), ErrorCode::Digest);
            assert_eq!(
                fs::read(&dest).expect("destination preserved"),
                b"prior-ledger"
            );
        }
    }

    #[test]
    fn merge_shards_rejects_foreign_workflow_attempt() {
        let catalog = keys(4);
        let rows: Vec<EvidenceRow> = (0..4)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("foreign-attempt");
        let first = scratch.file("attempt-2-shard-0.jsonl");
        let second = scratch.file("attempt-3-shard-1.jsonl");
        let execution = ExecutionBinding::new(
            ".github/workflows/ci.yml",
            "41",
            2,
            "0123456789abcdef0123456789abcdef01234567",
            "conformance",
            "runner-1",
            "node-v24.18.0 rustc-1.91.0",
        )
        .expect("execution");
        let foreign = ExecutionBinding::new(
            ".github/workflows/ci.yml",
            "41",
            3,
            "0123456789abcdef0123456789abcdef01234567",
            "conformance",
            "runner-1",
            "node-v24.18.0 rustc-1.91.0",
        )
        .expect("foreign execution");
        write_shard_with_execution(&first, &catalog, 0, 2, &rows, binding(), execution);
        write_shard_with_execution(&second, &catalog, 1, 2, &rows, binding(), foreign);

        let error = merge_shards(
            &[first, second],
            &catalog,
            &scratch.file("merged.jsonl"),
            PublishMode::Replace,
        )
        .expect_err("mixed workflow attempts must fail");
        assert_eq!(error.code(), ErrorCode::Digest);
        assert!(error.to_string().contains("run_attempt"));
    }

    #[test]
    fn rejects_malformed_or_partial_stream() {
        let catalog = keys(3);
        let rows: Vec<EvidenceRow> = (0..3)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("malformed");
        let good = scratch.file("good.jsonl");
        write_unsharded(&good, &catalog, &rows);
        let good_text = fs::read_to_string(&good).expect("read");

        type Mutate = fn(&str) -> String;
        let cases: &[(&str, Mutate)] = &[
            ("legacy-schema", |text| {
                text.replacen("bamti.evidence/v2", "bamti.evidence/v1", 1)
            }),
            ("blank", |text| text.replace('\n', "\n\n")),
            ("trailing-junk", |text| {
                let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
                lines[0].push_str(" true");
                let mut out = lines.join("\n");
                out.push('\n');
                out
            }),
            ("duplicate-row", |text| {
                let mut lines: Vec<&str> = text.lines().collect();
                lines.insert(2, lines[1]);
                let mut out = lines.join("\n");
                out.push('\n');
                out
            }),
            ("out-of-order", |text| {
                let mut lines: Vec<&str> = text.lines().collect();
                lines.swap(1, 3);
                let mut out = lines.join("\n");
                out.push('\n');
                out
            }),
            ("trailing-record", |text| {
                let mut out = text.to_owned();
                out.push_str("{\"record\":\"footer\",\"body\":{\"row_count\":0,\"obligation_set_digest\":\"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee\"}}\n");
                out
            }),
            ("missing-footer", |text| {
                let mut lines: Vec<&str> = text.lines().collect();
                lines.pop();
                let mut out = lines.join("\n");
                out.push('\n');
                out
            }),
            ("crlf", |text| text.replace('\n', "\r\n")),
            ("partial-line", |text| {
                text.trim_end_matches('\n').to_owned()
            }),
        ];
        for (name, mutate) in cases {
            let path = scratch.file(&format!("{name}.jsonl"));
            fs::write(&path, mutate(&good_text)).expect("write");
            assert!(consume(&path).is_err(), "{name} must fail closed");
        }
    }

    #[test]
    fn streaming_merge_matches_unsharded() {
        for catalog_len in 1..=12 {
            for count in 1..=catalog_len {
                let catalog = keys(catalog_len);
                let rows: Vec<EvidenceRow> = (0..catalog_len)
                    .map(|index| {
                        let state = if index % 3 == 0 {
                            TerminalState::BlockingFail
                        } else {
                            TerminalState::Pass
                        };
                        row(index, state)
                    })
                    .collect();
                let scratch = Scratch::new("merge");
                let unsharded = scratch.file("all.jsonl");
                write_unsharded(&unsharded, &catalog, &rows);
                let mut shards = Vec::new();
                for index in 0..count {
                    let path = scratch.file(&format!("s-{index}.jsonl"));
                    write_shard(&path, &catalog, index as u32, count as u32, &rows);
                    shards.push(path);
                }
                let merged = scratch.file("merged.jsonl");
                merge_shards(&shards, &catalog, &merged, PublishMode::Replace).expect("merge");
                let expected = fs::read(&unsharded).expect("unsharded");
                let actual = fs::read(&merged).expect("merged");
                assert_eq!(actual, expected, "catalog {catalog_len} shards {count}");
            }
        }
    }

    #[test]
    fn publication_is_atomic() {
        let catalog = keys(4);
        let rows: Vec<EvidenceRow> = (0..4)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("atomic");
        let dest = scratch.file("evidence.jsonl");
        write_unsharded(&dest, &catalog, &rows);
        let before = fs::read(&dest).expect("before");

        let shard = ShardIdentity::plan(ShardSpec::unsharded(), &catalog).expect("plan");
        let header = EvidenceHeader::new(shard, binding(), ExecutionBinding::local_for_tests())
            .expect("header");
        let err = publish_streaming_with_fault(
            &dest,
            header.clone(),
            rows.clone(),
            PublishMode::Replace,
            Some(32),
        )
        .expect_err("fault");
        assert_eq!(err.code(), ErrorCode::Io);
        assert_eq!(fs::read(&dest).expect("after fault"), before);

        let other = scratch.file("other.jsonl");
        fs::write(&other, b"not-evidence\n").expect("bait");
        let check = publish_evidence(&other, header, &rows, PublishMode::Check).expect_err("check");
        assert_eq!(check.code(), ErrorCode::Digest);
        assert_eq!(fs::read(&other).expect("check dest"), b"not-evidence\n");
    }

    #[test]
    fn two_writes_of_same_binding_produce_byte_identical_headers() {
        let catalog = keys(4);
        let rows: Vec<EvidenceRow> = (0..4)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("deterministic-binding");
        let first = scratch.file("first.jsonl");
        let second = scratch.file("second.jsonl");
        write_unsharded(&first, &catalog, &rows);
        write_unsharded(&second, &catalog, &rows);
        let first_bytes = fs::read(&first).expect("read first");
        let second_bytes = fs::read(&second).expect("read second");
        assert_eq!(first_bytes, second_bytes);
    }
    #[test]
    fn reader_rejects_receipt_with_invalid_candidate_tree_digest() {
        let catalog = keys(2);
        let rows: Vec<EvidenceRow> = (0..2)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("invalid-tree");
        let dest = scratch.file("evidence.jsonl");

        // Write a valid receipt, then tamper with the candidate_tree_digest
        // to make it an invalid (non-SHA-256-hex) value.
        write_unsharded(&dest, &catalog, &rows);
        let bytes = fs::read_to_string(&dest).expect("read");
        let tampered = bytes.replace(
            "\"candidate_tree_digest\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
            "\"candidate_tree_digest\":\"not-a-sha256-digest\"",
        );
        assert_ne!(bytes, tampered, "tamper must change bytes");
        fs::write(&dest, &tampered).expect("write tampered");

        let error = EvidenceReader::open(&dest).expect_err("must reject");
        assert_eq!(
            error.code(),
            ErrorCode::Digest,
            "invalid candidate_tree_digest must be rejected: {error}"
        );
    }

    #[test]
    fn reader_rejects_receipt_missing_toolchain_pin() {
        let catalog = keys(2);
        let rows: Vec<EvidenceRow> = (0..2)
            .map(|index| row(index, TerminalState::Pass))
            .collect();
        let scratch = Scratch::new("missing-toolchain");
        let dest = scratch.file("evidence.jsonl");

        // Write a valid receipt, then remove the toolchain field from the header.
        write_unsharded(&dest, &catalog, &rows);
        let bytes = fs::read_to_string(&dest).expect("read");
        // Remove the toolchain object from the binding.
        let tampered = bytes.replace(
            ",\"toolchain\":{\"rustc_version\":\"rustc-1.97.1\",\"rust_toolchain_toml_digest\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}",
            "",
        );
        assert_ne!(bytes, tampered, "tamper must change bytes");
        fs::write(&dest, &tampered).expect("write tampered");

        let error = EvidenceReader::open(&dest).expect_err("must reject");
        assert_eq!(
            error.code(),
            ErrorCode::Json,
            "missing toolchain pin must be rejected as a JSON error: {error}"
        );
    }
}
