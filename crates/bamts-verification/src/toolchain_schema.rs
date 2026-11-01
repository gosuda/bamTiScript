//! Target-cell evidence schema and `verification/toolchains/<triple>.json` generator.
//!
//! The `target-cells` catalog is the cross-product of four triples and seven
//! obligations.  Each record on disk is one triple.  Every obligation is named,
//! classified, and either observed or explicitly missing: a cell cannot skip an
//! obligation it never looked for, and `PASS` cannot be written over a gap.
//!
//! Committed E4 records are stricter than intermediate generator values: every
//! obligation must be `PASS`, content-addressed, and backed by an explicit
//! replay command. `BLOCKING_FAIL` and `EXTERNAL_BLOCKED` remain available only
//! while collecting observations and are rejected by the committed-record loader.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

use serde::{Deserialize, Serialize};

use crate::{
    ErrorCode, Result, VerificationError,
    evidence::TerminalState,
    schema::{is_lower_hex, parse_json, read_bytes, require_nonempty, schema_error, set_mismatch},
};
use bamts_bytecode::{
    Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
    ModuleId, Program, ProgramModule, Register,
};
use bamts_codegen::{TargetDescriptor, emit_for_target};

/// Directory holding one record per target cell.
pub const TOOLCHAIN_DIR: &str = "verification/toolchains";

/// Schema tag bound into every target-cell record.
pub const TARGET_CELL_SCHEMA: &str = "bamti.target-cell/v1";

/// Target cells closed by the E4 leaves, in catalog target order.
pub const TARGET_TRIPLES: [&str; 4] = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "s390x-unknown-linux-gnu",
    "riscv64gc-unknown-linux-gnu",
];

/// Catalog obligations for every target cell, in extractor order.
pub const CELL_OBLIGATIONS: [&str; 7] = [
    "toolchain-manifest",
    "elf-object",
    "hardened-link",
    "qemu-functional",
    "native-runtime",
    "execmem-guard",
    "reproducible-build",
];

const ENVIRONMENT_ARTIFACTS: [&str; 2] = ["cross-linker", "qemu-user"];

/// Schema tag bound into every target-cell record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TargetCellSchema {
    #[serde(rename = "bamti.target-cell/v1")]
    V1,
}

impl TargetCellSchema {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        TARGET_CELL_SCHEMA
    }
}

/// How the cell reaches its target: directly on this host, or through emulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CellClass {
    NativeHost,
    CrossQemu,
}

/// The compiler identity a cell was evaluated against.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RustcPin {
    commit: String,
    commit_date: String,
    host: String,
    llvm_version: String,
    version: String,
}

impl RustcPin {
    /// # Errors
    ///
    /// Returns [`ErrorCode::Schema`] when any field is empty or `commit` is not
    /// a 40-character lowercase hex SHA-1.
    pub fn new(
        commit: impl Into<String>,
        commit_date: impl Into<String>,
        host: impl Into<String>,
        llvm_version: impl Into<String>,
        version: impl Into<String>,
    ) -> Result<Self> {
        let pin = Self {
            commit: commit.into(),
            commit_date: commit_date.into(),
            host: host.into(),
            llvm_version: llvm_version.into(),
            version: version.into(),
        };
        pin.validate(Path::new("rustc"))?;
        Ok(pin)
    }

    fn validate(&self, path: &Path) -> Result<()> {
        for (field, value) in [
            ("rustc commit_date", self.commit_date.as_str()),
            ("rustc host", self.host.as_str()),
            ("rustc llvm_version", self.llvm_version.as_str()),
            ("rustc version", self.version.as_str()),
        ] {
            require_nonempty(path, field, value)?;
        }
        if !is_lower_hex(&self.commit, 40) {
            return Err(schema_error(
                path,
                format!(
                    "rustc commit must be 40 lower-hex characters, found `{}`",
                    self.commit
                ),
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn host(&self) -> &str {
        &self.host
    }

    #[must_use]
    pub fn version(&self) -> &str {
        &self.version
    }

    #[must_use]
    pub fn identity(&self) -> String {
        format!(
            "rustc {} ({} {}) host {} LLVM {}",
            self.version, self.commit, self.commit_date, self.host, self.llvm_version
        )
    }
}

/// One catalog obligation inside a target cell.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObligationEvidence {
    evidence: String,
    missing_artifact: String,
    reason: String,
    status: TerminalState,
    unblock_condition: String,
}

impl ObligationEvidence {
    fn validate(&self, path: &Path, triple: &str, obligation: &str) -> Result<()> {
        require_nonempty(
            path,
            &format!("{triple}::{obligation} reason"),
            &self.reason,
        )?;
        match self.status {
            TerminalState::Pass => {
                require_nonempty(
                    path,
                    &format!("{triple}::{obligation} evidence"),
                    &self.evidence,
                )?;
                require_empty(
                    path,
                    &format!("{triple}::{obligation} missing_artifact"),
                    &self.missing_artifact,
                )?;
                require_empty(
                    path,
                    &format!("{triple}::{obligation} unblock_condition"),
                    &self.unblock_condition,
                )?;
            }
            TerminalState::BlockingFail | TerminalState::ExternalBlocked => {
                require_nonempty(
                    path,
                    &format!("{triple}::{obligation} missing_artifact"),
                    &self.missing_artifact,
                )?;
                require_nonempty(
                    path,
                    &format!("{triple}::{obligation} unblock_condition"),
                    &self.unblock_condition,
                )?;
                validate_ownership(
                    path,
                    triple,
                    obligation,
                    self.status,
                    &self.missing_artifact,
                )?;
            }
            TerminalState::InapplicableOutOfScopeHostFeature => {
                return Err(schema_error(
                    path,
                    format!(
                        "{triple}::{obligation} cannot be inapplicable; every target obligation requires observed evidence"
                    ),
                ));
            }
            other => {
                return Err(VerificationError::new(
                    ErrorCode::Transition,
                    format!(
                        "{}: {triple}::{obligation} has state `{}`",
                        path.display(),
                        other.as_str()
                    ),
                ));
            }
        }
        Ok(())
    }

    #[must_use]
    pub const fn status(&self) -> TerminalState {
        self.status
    }

    #[must_use]
    pub fn missing_artifact(&self) -> &str {
        &self.missing_artifact
    }

    #[must_use]
    pub fn reason(&self) -> &str {
        &self.reason
    }

    #[must_use]
    pub fn evidence(&self) -> &str {
        &self.evidence
    }
}

/// One target cell: seven catalog obligations for a single triple.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TargetCellRecord {
    cell_class: CellClass,
    obligations: BTreeMap<String, ObligationEvidence>,
    rustc: RustcPin,
    schema: TargetCellSchema,
    triple: String,
}

impl TargetCellRecord {
    /// Every rule a record must satisfy.  Rejects, never repairs.
    pub fn validate(&self, path: &Path) -> Result<()> {
        require_nonempty(path, "triple", &self.triple)?;
        if !TARGET_TRIPLES.contains(&self.triple.as_str()) {
            return Err(schema_error(
                path,
                format!("`{}` is not a declared target cell", self.triple),
            ));
        }
        self.rustc.validate(path)?;
        match self.cell_class {
            CellClass::NativeHost if self.rustc.host != self.triple => {
                return Err(schema_error(
                    path,
                    format!(
                        "native-host cell `{}` was evaluated by a rustc hosted on `{}`",
                        self.triple, self.rustc.host
                    ),
                ));
            }
            CellClass::CrossQemu if self.rustc.host == self.triple => {
                return Err(schema_error(
                    path,
                    format!(
                        "cross-qemu cell `{}` is the rustc host and must be native_host",
                        self.triple
                    ),
                ));
            }
            _ => {}
        }

        let expected = obligation_set();
        let actual: BTreeSet<String> = self.obligations.keys().cloned().collect();
        if actual != expected {
            return Err(set_mismatch(
                &format!("{} obligations", self.triple),
                &expected,
                &actual,
            ));
        }
        for (obligation, evidence) in &self.obligations {
            evidence.validate(path, &self.triple, obligation)?;
        }
        Ok(())
    }

    #[must_use]
    pub fn triple(&self) -> &str {
        &self.triple
    }

    #[must_use]
    pub const fn cell_class(&self) -> CellClass {
        self.cell_class
    }

    #[must_use]
    pub const fn rustc(&self) -> &RustcPin {
        &self.rustc
    }

    #[must_use]
    pub const fn obligations(&self) -> &BTreeMap<String, ObligationEvidence> {
        &self.obligations
    }

    /// True only when all seven target obligations carry observed passes.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.obligations
            .values()
            .all(|obligation| obligation.status == TerminalState::Pass)
    }

    fn validate_committed_evidence(&self, path: &Path) -> Result<()> {
        if !self.is_closed() {
            return Err(schema_error(
                path,
                format!(
                    "{} must record PASS for all seven target obligations",
                    self.triple
                ),
            ));
        }
        for (obligation, record) in &self.obligations {
            let triple = self.triple.as_str();
            let evidence = record.evidence.as_str();
            let rules = self.evidence_rules(obligation);
            require_evidence_fields(path, triple, obligation, evidence, &["command"])?;
            require_evidence_fields(path, triple, obligation, evidence, &rules.fields)?;
            for (field, expected) in rules.values {
                require_evidence_value(path, triple, obligation, evidence, field, expected)?;
            }
            if obligation == "reproducible-build" {
                require_equal_hashes(path, triple, obligation, evidence)?;
            }
            validate_evidence_hashes(path, triple, obligation, evidence)?;
        }
        Ok(())
    }

    /// What one obligation's evidence must state for this cell.
    fn evidence_rules(&self, obligation: &str) -> EvidenceRules {
        let machine = match self.triple.as_str() {
            "x86_64-unknown-linux-gnu" => "Advanced Micro Devices X86-64",
            "aarch64-unknown-linux-gnu" => "AArch64",
            "s390x-unknown-linux-gnu" => "IBM S/390",
            "riscv64gc-unknown-linux-gnu" => "RISC-V",
            _ => unreachable!("target set was validated"),
        };
        match obligation {
            "toolchain-manifest" => EvidenceRules::fields(&["rustc_version", "rustc_sha256"]),
            "elf-object" => EvidenceRules {
                fields: vec![
                    "object_sha256",
                    "elf_type",
                    "elf_machine",
                    "entry",
                    "helpers",
                ],
                values: vec![("elf_type", "REL"), ("elf_machine", machine)],
            },
            "hardened-link" => EvidenceRules {
                fields: vec![
                    "executable_sha256",
                    "elf_type",
                    "elf_machine",
                    "linker_version",
                    "linker_sha256",
                ],
                values: vec![("elf_type", "EXEC"), ("elf_machine", machine)],
            },
            "qemu-functional" | "native-runtime" => self.execution_rules(),
            "execmem-guard" => EvidenceRules {
                fields: vec!["executable_sha256", "readelf_sha256"],
                values: vec![
                    ("writable_executable_load_segments", "0"),
                    ("gnu_stack", "RW"),
                    ("dynamic_section", "absent"),
                ],
            },
            "reproducible-build" => EvidenceRules {
                fields: vec!["first_object_sha256", "second_object_sha256"],
                values: vec![("byte_identical", "true")],
            },
            _ => unreachable!("obligation set was validated"),
        }
    }

    /// Rules shared by the two obligations that run a linked image.
    fn execution_rules(&self) -> EvidenceRules {
        let mut rules = EvidenceRules {
            fields: vec!["executable_sha256", "execution", "fuel"],
            values: vec![("exit", "0"), ("result", "int32:42")],
        };
        match self.cell_class {
            CellClass::NativeHost => rules.values.push(("execution", "native")),
            CellClass::CrossQemu => {
                rules.fields.extend(["emulator_version", "emulator_sha256"]);
                let execution = match self.triple.as_str() {
                    "aarch64-unknown-linux-gnu" => "qemu-aarch64",
                    "s390x-unknown-linux-gnu" => "qemu-s390x",
                    "riscv64gc-unknown-linux-gnu" => "qemu-riscv64",
                    _ => unreachable!("cross target set was validated"),
                };
                rules.values.push(("execution", execution));
            }
        }
        rules
    }
}

/// The fields one obligation's evidence must carry, and the values some must hold.
struct EvidenceRules {
    fields: Vec<&'static str>,
    values: Vec<(&'static str, &'static str)>,
}

impl EvidenceRules {
    fn fields(fields: &[&'static str]) -> Self {
        Self {
            fields: fields.to_vec(),
            values: Vec::new(),
        }
    }
}

fn evidence_value<'a>(evidence: &'a str, name: &str) -> Option<&'a str> {
    evidence.split("; ").find_map(|field| {
        let (key, value) = field.split_once('=')?;
        (key == name).then_some(value)
    })
}

fn require_evidence_fields(
    path: &Path,
    triple: &str,
    obligation: &str,
    evidence: &str,
    fields: &[&str],
) -> Result<()> {
    for field in fields {
        match evidence_value(evidence, field) {
            Some(value) if !value.is_empty() => {}
            _ => {
                return Err(schema_error(
                    path,
                    format!("{triple}::{obligation} evidence is missing `{field}`"),
                ));
            }
        }
    }
    Ok(())
}

fn require_evidence_value(
    path: &Path,
    triple: &str,
    obligation: &str,
    evidence: &str,
    field: &str,
    expected: &str,
) -> Result<()> {
    let actual = evidence_value(evidence, field).unwrap_or("<missing>");
    if actual == expected {
        Ok(())
    } else {
        Err(schema_error(
            path,
            format!(
                "{triple}::{obligation} evidence `{field}` expected `{expected}`, found `{actual}`"
            ),
        ))
    }
}

fn require_equal_hashes(path: &Path, triple: &str, obligation: &str, evidence: &str) -> Result<()> {
    let first = evidence_value(evidence, "first_object_sha256").expect("required");
    let second = evidence_value(evidence, "second_object_sha256").expect("required");
    if first == second {
        Ok(())
    } else {
        Err(schema_error(
            path,
            format!("{triple}::{obligation} claims byte identity for unequal object hashes"),
        ))
    }
}

fn validate_evidence_hashes(
    path: &Path,
    triple: &str,
    obligation: &str,
    evidence: &str,
) -> Result<()> {
    let mut count = 0usize;
    for field in evidence.split("; ") {
        let Some((name, value)) = field.split_once('=') else {
            return Err(schema_error(
                path,
                format!("{triple}::{obligation} evidence field `{field}` is not key=value"),
            ));
        };
        if name.ends_with("_sha256") {
            count += 1;
            if !is_lower_hex(value, 64) {
                return Err(schema_error(
                    path,
                    format!("{triple}::{obligation} `{name}` is not lowercase SHA-256"),
                ));
            }
        }
    }
    if count == 0 {
        Err(schema_error(
            path,
            format!("{triple}::{obligation} evidence has no content hash"),
        ))
    } else {
        Ok(())
    }
}

/// Host/toolchain observations the generator is allowed to consume.  Absent
/// maps mean the artifact was looked for and not found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostObservation {
    rustc: RustcPin,
    elf_objects: BTreeMap<String, String>,
    execmem_guards: BTreeMap<String, String>,
    hardened_links: BTreeMap<String, String>,
    linkers: BTreeMap<String, String>,
    native_executions: BTreeMap<String, String>,
    qemu_user: BTreeMap<String, String>,
    reproducible_builds: BTreeMap<String, String>,
}

impl HostObservation {
    #[must_use]
    pub fn new(rustc: RustcPin) -> Self {
        Self {
            rustc,
            elf_objects: BTreeMap::new(),
            execmem_guards: BTreeMap::new(),
            hardened_links: BTreeMap::new(),
            linkers: BTreeMap::new(),
            native_executions: BTreeMap::new(),
            qemu_user: BTreeMap::new(),
            reproducible_builds: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn with_linker(mut self, triple: impl Into<String>, identity: impl Into<String>) -> Self {
        self.linkers.insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub fn with_qemu_user(
        mut self,
        triple: impl Into<String>,
        identity: impl Into<String>,
    ) -> Self {
        self.qemu_user.insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub fn with_elf_object(
        mut self,
        triple: impl Into<String>,
        identity: impl Into<String>,
    ) -> Self {
        self.elf_objects.insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub fn with_hardened_link(
        mut self,
        triple: impl Into<String>,
        identity: impl Into<String>,
    ) -> Self {
        self.hardened_links.insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub fn with_native_execution(
        mut self,
        triple: impl Into<String>,
        identity: impl Into<String>,
    ) -> Self {
        self.native_executions
            .insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub fn with_execmem_guard(
        mut self,
        triple: impl Into<String>,
        identity: impl Into<String>,
    ) -> Self {
        self.execmem_guards.insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub fn with_reproducible_build(
        mut self,
        triple: impl Into<String>,
        identity: impl Into<String>,
    ) -> Self {
        self.reproducible_builds
            .insert(triple.into(), identity.into());
        self
    }

    #[must_use]
    pub const fn rustc(&self) -> &RustcPin {
        &self.rustc
    }
}

/// Catalog identifier `{triple}::{obligation}`.
#[must_use]
pub fn catalog_identifier(triple: &str, obligation: &str) -> String {
    format!("{triple}::{obligation}")
}

/// The 28 catalog identifiers in sorted order.
#[must_use]
pub fn catalog_identifiers() -> Vec<String> {
    let mut identifiers = Vec::with_capacity(TARGET_TRIPLES.len() * CELL_OBLIGATIONS.len());
    for triple in TARGET_TRIPLES {
        for obligation in CELL_OBLIGATIONS {
            identifiers.push(catalog_identifier(triple, obligation));
        }
    }
    identifiers.sort();
    identifiers
}

/// Class for `triple` given the rustc that evaluated it.
///
/// # Errors
///
/// Returns [`ErrorCode::Schema`] when `triple` is not a declared target cell.
pub fn cell_class_for(triple: &str, rustc_host: &str) -> Result<CellClass> {
    if !TARGET_TRIPLES.contains(&triple) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("`{triple}` is not a declared target cell"),
        ));
    }
    if triple == rustc_host {
        Ok(CellClass::NativeHost)
    } else {
        Ok(CellClass::CrossQemu)
    }
}

/// Build one validated cell from observed artifacts.  Missing maps stay missing.
///
/// # Errors
///
/// Returns a schema or transition error when the generated record would be
/// illegal (unknown triple, native/cross mismatch, or an invalid obligation).
pub fn generate_cell(triple: &str, observation: &HostObservation) -> Result<TargetCellRecord> {
    let class = cell_class_for(triple, observation.rustc.host())?;
    let mut obligations = BTreeMap::new();
    for obligation in CELL_OBLIGATIONS {
        obligations.insert(
            obligation.to_owned(),
            generate_obligation(triple, obligation, class, observation),
        );
    }
    let record = TargetCellRecord {
        cell_class: class,
        obligations,
        rustc: observation.rustc.clone(),
        schema: TargetCellSchema::V1,
        triple: triple.to_owned(),
    };
    record.validate(Path::new("<generated>"))?;
    Ok(record)
}

/// Build every declared target cell from one observation.
///
/// # Errors
///
/// Returns the first [`generate_cell`] failure.
pub fn generate_cells(observation: &HostObservation) -> Result<BTreeMap<String, TargetCellRecord>> {
    let mut cells = BTreeMap::new();
    for triple in TARGET_TRIPLES {
        cells.insert(triple.to_owned(), generate_cell(triple, observation)?);
    }
    Ok(cells)
}

/// Encode one record as pretty JSON with a trailing newline.
///
/// # Errors
///
/// Returns [`ErrorCode::Json`] when serialization fails.
pub fn encode_record(record: &TargetCellRecord) -> Result<Vec<u8>> {
    let mut bytes = serde_json::to_vec_pretty(record).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("cannot encode target cell: {error}"),
        )
    })?;
    if !bytes.ends_with(b"\n") {
        bytes.push(b'\n');
    }
    Ok(bytes)
}

/// Parse and validate one record.  Duplicate JSON keys are rejected by the
/// shared JSON reader so a shadowed status cannot survive into the record.
pub fn parse_record(path: &Path, bytes: &[u8]) -> Result<TargetCellRecord> {
    let record: TargetCellRecord = parse_json(path, bytes)?;
    record.validate(path)?;
    Ok(record)
}
/// Metadata for the deterministic executable probe emitted by [`emit_probe_object`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProbeObject {
    pub target: String,
    pub sha256: String,
    pub entry_symbol: String,
    pub required_helpers: Vec<&'static str>,
    pub byte_len: usize,
}

/// Emit the target-evidence probe through the production BamTS AOT codegen path.
///
/// The probe loads the integer constant 42 through the native helper ABI and
/// returns it through the generated entry function. The freestanding support
/// linked by the evidence commands supplies the helpers and checks the returned
/// completion value.
///
/// # Errors
///
/// Returns a schema error if the canonical probe cannot be verified or emitted,
/// and an I/O error if `output` cannot be written.
pub fn emit_probe_object(target: &str, output: &Path) -> Result<ProbeObject> {
    let function = Function::new(
        None,
        0,
        0,
        1,
        FunctionFlags::default(),
        vec![
            Instruction::LoadConst {
                dst: Register::new(0),
                constant: ConstantId::new(1),
            },
            Instruction::Return {
                value: Register::new(0),
            },
        ],
        Vec::new(),
    );
    let module = Module::new(
        vec![
            Constant::String(EcmaString::encode("target-evidence")),
            Constant::Int32(42),
        ],
        vec![function],
        FunctionId::new(0),
    )
    .verify()
    .map_err(|error| {
        schema_error(
            Path::new("<target-evidence-probe>"),
            format!("probe bytecode verification failed: {error}"),
        )
    })?;
    let program = Program::link(
        vec![ProgramModule {
            name: ConstantId::new(0),
            code: module,
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        }],
        ModuleId::new(0),
    )
    .map_err(|error| {
        schema_error(
            Path::new("<target-evidence-probe>"),
            format!("probe program verification failed: {error}"),
        )
    })?;
    let descriptor = TargetDescriptor::lookup(target).map_err(|error| {
        schema_error(
            Path::new("<target-evidence-probe>"),
            format!("target `{target}` is not an executable codegen target: {error}"),
        )
    })?;
    let emitted = emit_for_target(&program, &descriptor).map_err(|error| {
        schema_error(
            Path::new("<target-evidence-probe>"),
            format!("probe AOT emission failed for `{target}`: {error}"),
        )
    })?;
    std::fs::write(output, emitted.bytes()).map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("cannot write {}: {error}", output.display()),
        )
    })?;

    Ok(ProbeObject {
        target: emitted.target().triple().to_owned(),
        sha256: emitted.content_digest_hex(),
        entry_symbol: emitted.object().entry_symbol.clone(),
        required_helpers: emitted.object().required_helpers.clone(),
        byte_len: emitted.bytes().len(),
    })
}

/// Load every target cell.  A missing file is an error, never an empty cell.
pub fn load_target_cells(root: &Path) -> Result<BTreeMap<String, TargetCellRecord>> {
    let directory = root.join(TOOLCHAIN_DIR);
    let mut cells = BTreeMap::new();
    for triple in TARGET_TRIPLES {
        let path = directory.join(format!("{triple}.json"));
        let bytes = read_bytes(&path)?;
        let record = parse_record(&path, &bytes)?;
        record.validate_committed_evidence(&path)?;
        if record.triple != triple {
            return Err(schema_error(
                &path,
                format!("record declares triple `{}`", record.triple),
            ));
        }
        cells.insert(triple.to_owned(), record);
    }

    let native: Vec<&str> = cells
        .values()
        .filter(|record| matches!(record.cell_class, CellClass::NativeHost))
        .map(TargetCellRecord::triple)
        .collect();
    if native.len() != 1 {
        return Err(schema_error(
            &directory,
            format!(
                "expected exactly one native-host cell, found {}",
                native.len()
            ),
        ));
    }
    Ok(cells)
}

/// Obligations that are not `PASS`, in catalog-identifier order.
pub fn blocking_obligations(
    cells: &BTreeMap<String, TargetCellRecord>,
) -> Vec<(String, &ObligationEvidence)> {
    let mut blocked = Vec::new();
    for identifier in catalog_identifiers() {
        let (triple, obligation) = identifier
            .split_once("::")
            .expect("catalog identifiers are `{triple}::{obligation}`");
        if let Some(cell) = cells.get(triple)
            && let Some(evidence) = cell.obligations.get(obligation)
            && evidence.status != TerminalState::Pass
        {
            blocked.push((identifier, evidence));
        }
    }
    blocked
}

fn generate_obligation(
    triple: &str,
    obligation: &str,
    class: CellClass,
    observation: &HostObservation,
) -> ObligationEvidence {
    match obligation {
        "toolchain-manifest" => pass(
            observation.rustc.identity(),
            "Recorded from rustc -vV on this host.",
        ),
        "elf-object" => match observation.elf_objects.get(triple) {
            Some(identity) => pass(
                identity.clone(),
                "Stored relocatable AOT object for this triple.",
            ),
            None => blocking(
                "elf-object",
                "",
                "No relocatable AOT object is stored for this triple.",
                "Emit a BamTS AOT object for this triple and record its content hash.",
            ),
        },
        "hardened-link" => {
            if let Some(identity) = observation.hardened_links.get(triple) {
                pass(
                    identity.clone(),
                    "Stored hardened link artifact for this triple.",
                )
            } else if matches!(class, CellClass::CrossQemu)
                && !observation.linkers.contains_key(triple)
            {
                blocked_external(
                    "cross-linker",
                    "",
                    "No cross GNU linker for this triple is installed.",
                    "Install the matching *-linux-gnu-gcc linker, perform a hardened link, and record the binary identity.",
                )
            } else {
                let evidence = observation.linkers.get(triple).cloned().unwrap_or_default();
                blocking(
                    "hardened-link",
                    evidence,
                    "No hardened BamTS link artifact is stored for this triple.",
                    "Link the emitted object with the hardened recipe and record the binary identity.",
                )
            }
        }
        "qemu-functional" => match class {
            CellClass::NativeHost => match observation.native_executions.get(triple) {
                Some(identity) => pass(
                    identity.clone(),
                    "Native-host functional execution completed without emulation.",
                ),
                None => blocking(
                    "qemu-functional",
                    "",
                    "No native functional execution is stored for this host triple.",
                    "Execute the linked BamTS image natively and record the functional result.",
                ),
            },
            CellClass::CrossQemu => match observation.qemu_user.get(triple) {
                Some(identity) => pass(
                    identity.clone(),
                    "qemu-user executed a linked image for this triple.",
                ),
                None => blocked_external(
                    "qemu-user",
                    "",
                    "qemu-user for this triple is not installed.",
                    "Install qemu-user for this triple, execute the linked image, and record qemu version and the run identity.",
                ),
            },
        },
        "native-runtime" => match class {
            CellClass::NativeHost => match observation.native_executions.get(triple) {
                Some(identity) => pass(
                    identity.clone(),
                    "This process runs natively on the cell triple.",
                ),
                None => blocking(
                    "native-runtime",
                    "",
                    "No native-runtime observation is stored for this triple.",
                    "Execute a linked BamTS image natively on this host and record the run identity.",
                ),
            },
            CellClass::CrossQemu => match observation.qemu_user.get(triple) {
                Some(identity) => pass(
                    identity.clone(),
                    "qemu-user executed the target runtime image for this triple.",
                ),
                None => blocked_external(
                    "qemu-user",
                    "",
                    "qemu-user for this triple is not installed.",
                    "Install qemu-user for this triple, execute the target runtime image, and record the run identity.",
                ),
            },
        },
        "execmem-guard" => match observation.execmem_guards.get(triple) {
            Some(identity) => pass(
                identity.clone(),
                "Stored execmem-guard observation for this triple.",
            ),
            None => blocking(
                "execmem-guard",
                "",
                "No execmem-guard observation is stored for this triple.",
                "Link and run an AOT image for this triple under an execmem-guard and record the observation.",
            ),
        },
        "reproducible-build" => match observation.reproducible_builds.get(triple) {
            Some(identity) => pass(
                identity.clone(),
                "Stored reproducible-build identity for this triple.",
            ),
            None => blocking(
                "reproducible-build",
                "",
                "No reproducible-build artifact pair is stored for this triple.",
                "Emit twice for this triple, require byte identity, and record the hash.",
            ),
        },
        _ => blocking(
            obligation,
            "",
            "Unknown obligation.",
            "Remove the unknown obligation or add it to CELL_OBLIGATIONS.",
        ),
    }
}

fn pass(evidence: String, reason: &str) -> ObligationEvidence {
    ObligationEvidence {
        evidence,
        missing_artifact: String::new(),
        reason: reason.to_owned(),
        status: TerminalState::Pass,
        unblock_condition: String::new(),
    }
}

fn blocking(
    missing: &str,
    evidence: impl Into<String>,
    reason: &str,
    unblock: &str,
) -> ObligationEvidence {
    ObligationEvidence {
        evidence: evidence.into(),
        missing_artifact: missing.to_owned(),
        reason: reason.to_owned(),
        status: TerminalState::BlockingFail,
        unblock_condition: unblock.to_owned(),
    }
}

fn blocked_external(
    missing: &str,
    evidence: impl Into<String>,
    reason: &str,
    unblock: &str,
) -> ObligationEvidence {
    ObligationEvidence {
        evidence: evidence.into(),
        missing_artifact: missing.to_owned(),
        reason: reason.to_owned(),
        status: TerminalState::ExternalBlocked,
        unblock_condition: unblock.to_owned(),
    }
}

fn validate_ownership(
    path: &Path,
    triple: &str,
    obligation: &str,
    status: TerminalState,
    missing: &str,
) -> Result<()> {
    let environment = ENVIRONMENT_ARTIFACTS.contains(&missing);
    match status {
        TerminalState::ExternalBlocked if !environment => Err(schema_error(
            path,
            format!(
                "{triple}::{obligation} claims EXTERNAL_BLOCKED for `{missing}`, which is not an environment artifact"
            ),
        )),
        TerminalState::BlockingFail if environment => Err(schema_error(
            path,
            format!(
                "{triple}::{obligation} is missing environment artifact `{missing}` and must be EXTERNAL_BLOCKED"
            ),
        )),
        _ => Ok(()),
    }
}

fn obligation_set() -> BTreeSet<String> {
    CELL_OBLIGATIONS
        .iter()
        .map(|obligation| (*obligation).to_owned())
        .collect()
}

fn require_empty(path: &Path, field: &str, value: &str) -> Result<()> {
    if value.is_empty() {
        Ok(())
    } else {
        Err(schema_error(
            path,
            format!("{field} must be empty, found `{value}`"),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rustc() -> RustcPin {
        RustcPin::new(
            "8bab26f4f68e0e26f0bb7960be334d5b520ea452",
            "2026-07-14",
            "x86_64-unknown-linux-gnu",
            "22.1.6",
            "1.97.1",
        )
        .expect("test rustc pin")
    }

    fn hosted() -> HostObservation {
        HostObservation::new(rustc())
            .with_linker(
                "x86_64-unknown-linux-gnu",
                "cc (Ubuntu 16-20260322-1ubuntu1) 16.0.1 20260322 (experimental) [trunk r16-8246-g569ace1fa50]; dumpmachine x86_64-linux-gnu",
            )
            .with_native_execution("x86_64-unknown-linux-gnu", "Linux x86_64")
    }

    #[test]
    fn catalog_identifiers_match_the_target_cells_cross_product() {
        let identifiers = catalog_identifiers();
        assert_eq!(identifiers.len(), 28);
        assert_eq!(identifiers[0], "aarch64-unknown-linux-gnu::elf-object");
        assert_eq!(
            identifiers[27],
            "x86_64-unknown-linux-gnu::toolchain-manifest"
        );
        let expected: BTreeSet<String> = TARGET_TRIPLES
            .iter()
            .flat_map(|triple| {
                CELL_OBLIGATIONS
                    .iter()
                    .map(move |obligation| catalog_identifier(triple, obligation))
            })
            .collect();
        assert_eq!(identifiers.into_iter().collect::<BTreeSet<_>>(), expected);
    }

    #[test]
    fn generator_fail_closes_missing_hosted_and_cross_artifacts() {
        let cells = generate_cells(&hosted()).expect("cells generate");
        let native = cells.get("x86_64-unknown-linux-gnu").expect("native cell");
        assert_eq!(native.cell_class(), CellClass::NativeHost);
        assert!(!native.is_closed());
        assert_eq!(
            native.obligations()["toolchain-manifest"].status(),
            TerminalState::Pass
        );
        assert_eq!(
            native.obligations()["native-runtime"].status(),
            TerminalState::Pass
        );
        assert_eq!(
            native.obligations()["qemu-functional"].status(),
            TerminalState::Pass
        );
        assert_eq!(
            native.obligations()["elf-object"].status(),
            TerminalState::BlockingFail
        );
        assert_eq!(
            native.obligations()["hardened-link"].status(),
            TerminalState::BlockingFail
        );

        let aarch64 = cells.get("aarch64-unknown-linux-gnu").expect("cross cell");
        assert_eq!(aarch64.cell_class(), CellClass::CrossQemu);
        assert_eq!(
            aarch64.obligations()["qemu-functional"].status(),
            TerminalState::ExternalBlocked
        );
        assert_eq!(
            aarch64.obligations()["qemu-functional"].missing_artifact(),
            "qemu-user"
        );
        assert_eq!(
            aarch64.obligations()["hardened-link"].status(),
            TerminalState::ExternalBlocked
        );
        assert_eq!(
            aarch64.obligations()["native-runtime"].status(),
            TerminalState::ExternalBlocked
        );
        assert_eq!(
            aarch64.obligations()["elf-object"].status(),
            TerminalState::BlockingFail
        );
    }

    #[test]
    fn pass_cannot_be_claimed_for_a_missing_elf_object() {
        let cell = generate_cell("x86_64-unknown-linux-gnu", &hosted()).expect("native generates");
        let mut json = serde_json::to_value(&cell).expect("serialize");
        json["obligations"]["elf-object"]["status"] = serde_json::json!("PASS");
        json["obligations"]["elf-object"]["missing_artifact"] = serde_json::json!("");
        json["obligations"]["elf-object"]["unblock_condition"] = serde_json::json!("");
        json["obligations"]["elf-object"]["evidence"] = serde_json::json!("");
        let bytes = serde_json::to_vec(&json).expect("bytes");
        let error = parse_record(Path::new("cell.json"), &bytes)
            .expect_err("PASS requires evidence and forbids a gap");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn in_repository_gap_cannot_be_external_blocked() {
        let cell = generate_cell("x86_64-unknown-linux-gnu", &hosted()).expect("native generates");
        let mut json = serde_json::to_value(&cell).expect("serialize");
        json["obligations"]["elf-object"]["status"] = serde_json::json!("EXTERNAL_BLOCKED");
        let bytes = serde_json::to_vec(&json).expect("bytes");
        let error = parse_record(Path::new("cell.json"), &bytes)
            .expect_err("elf-object is not an environment artifact");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn missing_qemu_on_a_cross_cell_must_be_external_blocked() {
        let cell = generate_cell("s390x-unknown-linux-gnu", &hosted()).expect("cross generates");
        let mut json = serde_json::to_value(&cell).expect("serialize");
        json["obligations"]["qemu-functional"]["status"] = serde_json::json!("BLOCKING_FAIL");
        let bytes = serde_json::to_vec(&json).expect("bytes");
        let error = parse_record(Path::new("cell.json"), &bytes)
            .expect_err("missing qemu-user is external");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn native_cell_host_must_match_triple() {
        let cell = generate_cell("x86_64-unknown-linux-gnu", &hosted()).expect("native generates");
        let mut json = serde_json::to_value(&cell).expect("serialize");
        json["triple"] = serde_json::json!("aarch64-unknown-linux-gnu");
        json["cell_class"] = serde_json::json!("native_host");
        let bytes = serde_json::to_vec(&json).expect("bytes");
        let error = parse_record(Path::new("cell.json"), &bytes)
            .expect_err("native-host cell must match rustc host");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn complete_native_cell_closes_only_with_every_hosted_artifact() {
        let observation = hosted()
            .with_elf_object("x86_64-unknown-linux-gnu", "elf:1")
            .with_hardened_link("x86_64-unknown-linux-gnu", "link:1")
            .with_execmem_guard("x86_64-unknown-linux-gnu", "guard:1")
            .with_reproducible_build("x86_64-unknown-linux-gnu", "repro:1");
        let cell =
            generate_cell("x86_64-unknown-linux-gnu", &observation).expect("complete native");
        assert!(cell.is_closed());
        assert_eq!(
            cell.obligations()["qemu-functional"].status(),
            TerminalState::Pass
        );
    }

    #[test]
    fn duplicate_status_key_is_rejected() {
        let cell = generate_cell("x86_64-unknown-linux-gnu", &hosted()).expect("native generates");
        let mut text = String::from_utf8(encode_record(&cell).expect("encode")).expect("utf8");
        text = text.replace(
            "\"status\": \"BLOCKING_FAIL\"",
            "\"status\": \"BLOCKING_FAIL\",\n      \"status\": \"PASS\"",
        );
        parse_record(Path::new("cell.json"), text.as_bytes())
            .expect_err("duplicate keys are rejected");
    }

    #[test]
    fn load_target_cells_fails_closed_on_a_missing_record() {
        let error = load_target_cells(Path::new("/tmp/bamts-missing-toolchains"))
            .expect_err("missing directory is an error");
        assert_eq!(error.code(), ErrorCode::Io);
    }

    #[test]
    fn round_trip_preserves_a_generated_cell() {
        let cell = generate_cell("riscv64gc-unknown-linux-gnu", &hosted()).expect("generate");
        let bytes = encode_record(&cell).expect("encode");
        let parsed =
            parse_record(Path::new("riscv64gc-unknown-linux-gnu.json"), &bytes).expect("parse");
        assert_eq!(parsed, cell);
        assert!(!parsed.is_closed());
    }

    #[test]
    fn committed_records_are_content_addressed_and_closed() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let cells = load_target_cells(&root).expect("committed cells load");
        assert_eq!(cells.len(), TARGET_TRIPLES.len());
        assert!(cells.values().all(TargetCellRecord::is_closed));
        assert!(blocking_obligations(&cells).is_empty());
    }
}
