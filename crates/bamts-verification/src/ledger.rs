use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    fs::File,
    io::BufReader,
    path::Path,
};

use serde::{
    Deserialize,
    de::{self, DeserializeSeed, IgnoredAny, MapAccess, SeqAccess, Visitor},
};

use crate::schema::{
    MANIFEST_PATH, SourcePin, VerificationManifest, io_error, is_lower_hex, is_nonempty,
    json_error, load_sources, parse_json, parse_toml, read_bytes, require_nonempty, schema_error,
    set_difference_detail, set_mismatch, sha256_hex, source_by_name, string_set, validate_digest,
    validate_manifest, validate_sha256,
};
use crate::{ErrorCode, Gate, GateReport, Result, VerificationError, rebuild::LEDGER_SCHEMA};

const TOOLCHAINS_PATH: &str = "formal/toolchains.toml";
const LEDGER_PATH: &str = "proof/completeness-ledger.json";
const BLOCKER_PATH: &str = "verification/blockers/webassembly.json";

const P0_STATES: [&str; 7] = [
    "PASS",
    "BLOCKING_FAIL",
    "INAPPLICABLE_LANGUAGE_SERVICE",
    "INAPPLICABLE_OUT_OF_SCOPE_HOST_FEATURE",
    "INAPPLICABLE_V8_INTERNAL",
    "INAPPLICABLE_CATALOG_ERROR",
    "EXTERNAL_BLOCKED",
];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FormalToolchains {
    schema: String,
    quint: QuintToolchain,
    racket: RacketToolchain,
    lean: ToolchainPin,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct QuintToolchain {
    version: String,
    node_minimum: String,
    url: String,
    digest_algorithm: String,
    digest: String,
    commit: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RacketToolchain {
    version: String,
    url: String,
    digest_algorithm: String,
    digest: String,
    commit: String,
    redex_url: String,
    redex_digest_algorithm: String,
    redex_digest: String,
    redex_commit: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ToolchainPin {
    version: String,
    url: String,
    digest_algorithm: String,
    digest: String,
    commit: String,
}

struct ToolSource<'a> {
    version: &'a str,
    url: &'a str,
    digest_algorithm: &'a str,
    digest: &'a str,
    commit: &'a str,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WebassemblyBlocker {
    blocked_catalog_rows: Vec<String>,
    decision: String,
    evidence: Vec<String>,
    id: String,
    owner: String,
    reason: String,
    schema: String,
    status: String,
    unblock_condition: String,
    zero_match_catalogs: BTreeMap<String, ZeroMatchCatalog>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZeroMatchCatalog {
    runnable_rows: usize,
    webassembly_or_wasi_rows: usize,
}

struct LedgerMetadata {
    schema: String,
    manifest_sha256: String,
    states: Vec<String>,
}

struct LedgerRow {
    catalog: String,
    citation: String,
    id: String,
    matcher: String,
    owner: String,
    reason: String,
    state: String,
}

struct LedgerState {
    expected_ids: BTreeSet<String>,
    seen_ids: BTreeSet<String>,
    blocked_ids: BTreeSet<String>,
    error: Option<VerificationError>,
}

impl LedgerState {
    fn new(expected_ids: BTreeSet<String>) -> Self {
        Self {
            expected_ids,
            seen_ids: BTreeSet::new(),
            blocked_ids: BTreeSet::new(),
            error: None,
        }
    }

    fn has_error(&self) -> bool {
        self.error.is_some()
    }

    fn record_error(&mut self, error: VerificationError) {
        if self.error.is_none() {
            self.error = Some(error);
        }
    }

    fn take_error(&mut self) -> Option<VerificationError> {
        self.error.take()
    }

    fn process_row(&mut self, row: LedgerRow) {
        if self.has_error() {
            return;
        }

        for (field, value) in [
            ("catalog", row.catalog.as_str()),
            ("id", row.id.as_str()),
            ("state", row.state.as_str()),
        ] {
            if !is_nonempty(value) {
                self.record_error(VerificationError::new(
                    ErrorCode::Schema,
                    format!("{LEDGER_PATH}: row has empty `{field}`"),
                ));
                return;
            }
        }

        let case = row.id.strip_prefix(&format!("{}:", row.catalog));
        if !case.is_some_and(is_nonempty) {
            self.record_error(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "{LEDGER_PATH}: row id `{}` names no case in catalog `{}`",
                    row.id, row.catalog
                ),
            ));
            return;
        }

        if !is_allowed_state(&row.state) {
            self.record_error(VerificationError::new(
                ErrorCode::Transition,
                format!(
                    "{LEDGER_PATH}: row `{}` has unknown state `{}`",
                    row.id, row.state
                ),
            ));
            return;
        }

        if row.state != "PASS" {
            for (field, value) in [
                ("reason", row.reason.as_str()),
                ("owner", row.owner.as_str()),
                ("citation", row.citation.as_str()),
                ("matcher", row.matcher.as_str()),
            ] {
                if !is_nonempty(value) {
                    self.record_error(VerificationError::new(
                        ErrorCode::Transition,
                        format!(
                            "{LEDGER_PATH}: non-PASS row `{}` has empty `{field}`",
                            row.id
                        ),
                    ));
                    return;
                }
            }
        }

        if self.expected_ids.remove(&row.id) {
            self.seen_ids.insert(row.id.clone());
            if row.state == "EXTERNAL_BLOCKED" {
                self.blocked_ids.insert(row.id);
            }
            return;
        }

        if self.seen_ids.contains(&row.id) {
            self.record_error(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate ledger row `{}`", row.id),
            ));
            return;
        }

        let extra = BTreeSet::from([row.id]);
        self.record_error(set_mismatch("ledger rows", &BTreeSet::new(), &extra));
    }
}

pub fn verify_ledger_g0(root: &Path) -> Result<GateReport> {
    let (sources, source_ledger_sha256) = load_sources(root)?;
    validate_formal_toolchains(root, &sources)?;

    let manifest_path = root.join(MANIFEST_PATH);
    let manifest_bytes = read_bytes(&manifest_path)?;
    let manifest_sha256 = sha256_hex(&manifest_bytes);
    let manifest: VerificationManifest = parse_json(&manifest_path, &manifest_bytes)?;
    let expected_ids =
        validate_manifest(&manifest, &manifest_path, &source_ledger_sha256, &sources)?;
    let checks = expected_ids.len();

    let blocker_ids = load_blocker(root)?;
    let (ledger, state) = stream_ledger(root, expected_ids)?;
    validate_ledger_metadata(&ledger, &manifest_sha256)?;

    if !state.expected_ids.is_empty() {
        return Err(set_mismatch(
            "ledger rows",
            &state.expected_ids,
            &BTreeSet::new(),
        ));
    }

    if blocker_ids != state.blocked_ids {
        return Err(set_mismatch(
            "EXTERNAL_BLOCKED rows",
            &blocker_ids,
            &state.blocked_ids,
        ));
    }

    Ok(GateReport {
        gate: Gate::G0,
        checks,
    })
}

fn validate_formal_toolchains(root: &Path, sources: &BTreeMap<String, SourcePin>) -> Result<()> {
    let path = root.join(TOOLCHAINS_PATH);
    let bytes = read_bytes(&path)?;
    let toolchains: FormalToolchains = parse_toml(&path, &bytes)?;

    if toolchains.schema != "bamti.formal-toolchains/v1" {
        return Err(schema_error(
            &path,
            format!(
                "expected schema `bamti.formal-toolchains/v1`, found `{}`",
                toolchains.schema
            ),
        ));
    }

    if toolchains.quint.node_minimum.is_empty()
        || !toolchains
            .quint
            .node_minimum
            .bytes()
            .all(|byte| byte.is_ascii_digit())
    {
        return Err(schema_error(
            &path,
            "quint `node_minimum` must be a decimal string",
        ));
    }

    validate_tool_source(
        &path,
        "quint",
        ToolSource {
            version: &toolchains.quint.version,
            url: &toolchains.quint.url,
            digest_algorithm: &toolchains.quint.digest_algorithm,
            digest: &toolchains.quint.digest,
            commit: &toolchains.quint.commit,
        },
        source_by_name(sources, "quint", &path)?,
    )?;
    validate_tool_source(
        &path,
        "racket",
        ToolSource {
            version: &toolchains.racket.version,
            url: &toolchains.racket.url,
            digest_algorithm: &toolchains.racket.digest_algorithm,
            digest: &toolchains.racket.digest,
            commit: &toolchains.racket.commit,
        },
        source_by_name(sources, "racket", &path)?,
    )?;
    validate_tool_source(
        &path,
        "redex",
        ToolSource {
            version: &toolchains.racket.version,
            url: &toolchains.racket.redex_url,
            digest_algorithm: &toolchains.racket.redex_digest_algorithm,
            digest: &toolchains.racket.redex_digest,
            commit: &toolchains.racket.redex_commit,
        },
        source_by_name(sources, "redex", &path)?,
    )?;
    validate_tool_source(
        &path,
        "lean",
        ToolSource {
            version: &toolchains.lean.version,
            url: &toolchains.lean.url,
            digest_algorithm: &toolchains.lean.digest_algorithm,
            digest: &toolchains.lean.digest,
            commit: &toolchains.lean.commit,
        },
        source_by_name(sources, "lean", &path)?,
    )?;

    Ok(())
}

fn validate_tool_source(
    path: &Path,
    name: &str,
    tool: ToolSource<'_>,
    source: &SourcePin,
) -> Result<()> {
    for (field, value) in [
        ("version", tool.version),
        ("url", tool.url),
        ("commit", tool.commit),
    ] {
        require_nonempty(path, &format!("{name} {field}"), value)?;
    }
    if !is_lower_hex(tool.commit, 40) {
        return Err(schema_error(path, format!("{name} has malformed commit")));
    }
    validate_digest(path, name, tool.digest_algorithm, tool.digest)?;

    if tool.version != source.pin || tool.url != source.url {
        return Err(schema_error(
            path,
            format!("{name} pin does not match vendor source"),
        ));
    }
    if tool.digest_algorithm != source.digest_algorithm || tool.digest != source.digest {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{path_display}: {name} digest does not match vendor source",
                path_display = path.display()
            ),
        ));
    }
    if source.commit.as_deref() != Some(tool.commit) {
        return Err(schema_error(
            path,
            format!("{name} commit does not match vendor source"),
        ));
    }

    Ok(())
}

fn load_blocker(root: &Path) -> Result<BTreeSet<String>> {
    let path = root.join(BLOCKER_PATH);
    let bytes = read_bytes(&path)?;
    let blocker: WebassemblyBlocker = parse_json(&path, &bytes)?;

    if blocker.schema != "bamti.external-blocker/v1" {
        return Err(schema_error(
            &path,
            format!(
                "expected schema `bamti.external-blocker/v1`, found `{}`",
                blocker.schema
            ),
        ));
    }
    if blocker.status != "EXTERNAL_BLOCKED" {
        return Err(VerificationError::new(
            ErrorCode::Transition,
            format!(
                "{}: blocker status must be `EXTERNAL_BLOCKED`",
                path.display()
            ),
        ));
    }
    for (field, value) in [
        ("id", blocker.id.as_str()),
        ("owner", blocker.owner.as_str()),
        ("reason", blocker.reason.as_str()),
        ("unblock_condition", blocker.unblock_condition.as_str()),
        ("decision", blocker.decision.as_str()),
    ] {
        require_nonempty(&path, &format!("blocker {field}"), value)?;
    }
    if blocker.evidence.is_empty() {
        return Err(schema_error(&path, "blocker must include evidence"));
    }
    for evidence in &blocker.evidence {
        require_nonempty(&path, "blocker evidence", evidence)?;
    }
    for (catalog, counts) in &blocker.zero_match_catalogs {
        require_nonempty(&path, "zero-match catalog", catalog)?;
        if counts.webassembly_or_wasi_rows > counts.runnable_rows {
            return Err(schema_error(
                &path,
                format!("zero-match catalog `{catalog}` has inconsistent counts"),
            ));
        }
    }
    if blocker.blocked_catalog_rows.is_empty() {
        return Err(schema_error(&path, "blocker has no blocked catalog rows"));
    }

    let mut ids = BTreeSet::new();
    for id in blocker.blocked_catalog_rows {
        require_nonempty(&path, "blocked catalog row", &id)?;
        if !ids.insert(id.clone()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate blocked catalog row `{id}`"),
            ));
        }
    }
    Ok(ids)
}

fn stream_ledger(
    root: &Path,
    expected_ids: BTreeSet<String>,
) -> Result<(LedgerMetadata, LedgerState)> {
    let path = root.join(LEDGER_PATH);
    let file = File::open(&path).map_err(|error| io_error(&path, error))?;
    let mut deserializer = serde_json::Deserializer::from_reader(BufReader::new(file));
    let mut state = LedgerState::new(expected_ids);
    let ledger = LedgerSeed { state: &mut state }
        .deserialize(&mut deserializer)
        .map_err(|error| json_error(&path, error))?;
    deserializer
        .end()
        .map_err(|error| json_error(&path, error))?;

    if let Some(error) = state.take_error() {
        return Err(error);
    }

    Ok((ledger, state))
}

fn validate_ledger_metadata(ledger: &LedgerMetadata, manifest_sha256: &str) -> Result<()> {
    if ledger.schema != LEDGER_SCHEMA {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{LEDGER_PATH}: expected schema `{LEDGER_SCHEMA}`, found `{}`",
                ledger.schema
            ),
        ));
    }
    let path = Path::new(LEDGER_PATH);
    validate_sha256(path, "manifest_sha256", &ledger.manifest_sha256)?;
    if ledger.manifest_sha256 != manifest_sha256 {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!("{LEDGER_PATH}: manifest SHA-256 does not match raw {MANIFEST_PATH}"),
        ));
    }
    validate_state_vocabulary(&ledger.states)
}

fn validate_state_vocabulary(states: &[String]) -> Result<()> {
    let expected = string_set(&P0_STATES);
    let mut actual = BTreeSet::new();
    for state in states {
        if !is_allowed_state(state) {
            return Err(VerificationError::new(
                ErrorCode::Transition,
                format!("{LEDGER_PATH}: unknown declared state `{state}`"),
            ));
        }
        if !actual.insert(state.clone()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate declared state `{state}`"),
            ));
        }
    }
    if actual != expected {
        return Err(VerificationError::new(
            ErrorCode::Transition,
            format!(
                "{LEDGER_PATH}: state vocabulary {}",
                set_difference_detail(&expected, &actual)
            ),
        ));
    }
    Ok(())
}

struct LedgerSeed<'a> {
    state: &'a mut LedgerState,
}

impl<'de, 'a> DeserializeSeed<'de> for LedgerSeed<'a> {
    type Value = LedgerMetadata;

    fn deserialize<D>(self, deserializer: D) -> std::result::Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_map(LedgerVisitor { state: self.state })
    }
}

struct LedgerVisitor<'a> {
    state: &'a mut LedgerState,
}

impl<'de, 'a> Visitor<'de> for LedgerVisitor<'a> {
    type Value = LedgerMetadata;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a completeness-ledger object")
    }

    fn visit_map<A>(self, mut map: A) -> std::result::Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut schema = None;
        let mut manifest_sha256 = None;
        let mut states = None;
        let mut saw_rows = false;

        while let Some(key) = map.next_key::<String>()? {
            if self.state.has_error() {
                map.next_value::<IgnoredAny>()?;
                continue;
            }

            match key.as_str() {
                "schema" => {
                    read_ledger_string(&mut map, &mut schema, "root", "schema", self.state)?
                }
                "manifest_sha256" => read_ledger_string(
                    &mut map,
                    &mut manifest_sha256,
                    "root",
                    "manifest_sha256",
                    self.state,
                )?,
                "states" => read_ledger_states(&mut map, &mut states, self.state)?,
                "rows" => {
                    if saw_rows {
                        self.state.record_error(VerificationError::new(
                            ErrorCode::Schema,
                            format!("{LEDGER_PATH}: duplicate root field `rows`"),
                        ));
                        map.next_value::<IgnoredAny>()?;
                    } else {
                        saw_rows = true;
                        map.next_value_seed(RowsSeed {
                            state: &mut *self.state,
                        })?;
                    }
                }
                _ => {
                    self.state.record_error(VerificationError::new(
                        ErrorCode::Schema,
                        format!("{LEDGER_PATH}: unknown root field `{key}`"),
                    ));
                    map.next_value::<IgnoredAny>()?;
                }
            }
        }

        let schema = match schema {
            Some(value) => value,
            None => {
                self.state.record_error(VerificationError::new(
                    ErrorCode::Schema,
                    format!("{LEDGER_PATH}: missing root field `schema`"),
                ));
                String::new()
            }
        };
        let manifest_sha256 = match manifest_sha256 {
            Some(value) => value,
            None => {
                self.state.record_error(VerificationError::new(
                    ErrorCode::Schema,
                    format!("{LEDGER_PATH}: missing root field `manifest_sha256`"),
                ));
                String::new()
            }
        };
        let states = match states {
            Some(value) => value,
            None => {
                self.state.record_error(VerificationError::new(
                    ErrorCode::Schema,
                    format!("{LEDGER_PATH}: missing root field `states`"),
                ));
                Vec::new()
            }
        };
        if !saw_rows {
            self.state.record_error(VerificationError::new(
                ErrorCode::Schema,
                format!("{LEDGER_PATH}: missing root field `rows`"),
            ));
        }

        Ok(LedgerMetadata {
            schema,
            manifest_sha256,
            states,
        })
    }
}

struct RowsSeed<'a> {
    state: &'a mut LedgerState,
}

impl<'de, 'a> DeserializeSeed<'de> for RowsSeed<'a> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> std::result::Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_seq(RowsVisitor { state: self.state })
    }
}

struct RowsVisitor<'a> {
    state: &'a mut LedgerState,
}

impl<'de, 'a> Visitor<'de> for RowsVisitor<'a> {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a completeness-ledger rows array")
    }

    fn visit_seq<A>(self, mut sequence: A) -> std::result::Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        loop {
            if self.state.has_error() {
                while sequence.next_element::<IgnoredAny>()?.is_some() {}
                return Ok(());
            }
            if sequence
                .next_element_seed(RowSeed {
                    state: &mut *self.state,
                })?
                .is_none()
            {
                return Ok(());
            }
        }
    }
}

struct RowSeed<'a> {
    state: &'a mut LedgerState,
}

impl<'de, 'a> DeserializeSeed<'de> for RowSeed<'a> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> std::result::Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_map(RowVisitor { state: self.state })
    }
}

struct RowVisitor<'a> {
    state: &'a mut LedgerState,
}

impl<'de, 'a> Visitor<'de> for RowVisitor<'a> {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a completeness-ledger row object")
    }

    fn visit_map<A>(self, mut map: A) -> std::result::Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut catalog = None;
        let mut citation = None;
        let mut id = None;
        let mut matcher = None;
        let mut owner = None;
        let mut reason = None;
        let mut state = None;

        while let Some(key) = map.next_key::<String>()? {
            if self.state.has_error() {
                map.next_value::<IgnoredAny>()?;
                continue;
            }

            match key.as_str() {
                "catalog" => {
                    read_ledger_string(&mut map, &mut catalog, "row", "catalog", self.state)?
                }
                "citation" => {
                    read_ledger_string(&mut map, &mut citation, "row", "citation", self.state)?
                }
                "id" => read_ledger_string(&mut map, &mut id, "row", "id", self.state)?,
                "matcher" => {
                    read_ledger_string(&mut map, &mut matcher, "row", "matcher", self.state)?
                }
                "owner" => read_ledger_string(&mut map, &mut owner, "row", "owner", self.state)?,
                "reason" => read_ledger_string(&mut map, &mut reason, "row", "reason", self.state)?,
                "state" => read_ledger_string(&mut map, &mut state, "row", "state", self.state)?,
                _ => {
                    self.state.record_error(VerificationError::new(
                        ErrorCode::Schema,
                        format!("{LEDGER_PATH}: row has unknown field `{key}`"),
                    ));
                    map.next_value::<IgnoredAny>()?;
                }
            }
        }

        let missing = [
            ("catalog", catalog.is_none()),
            ("id", id.is_none()),
            ("state", state.is_none()),
        ]
        .into_iter()
        .find_map(|(field, is_missing)| is_missing.then_some(field));
        if let Some(field) = missing {
            self.state.record_error(VerificationError::new(
                ErrorCode::Schema,
                format!("{LEDGER_PATH}: row is missing field `{field}`"),
            ));
            return Ok(());
        }

        let (Some(catalog), Some(id), Some(state)) = (catalog, id, state) else {
            return Ok(());
        };

        self.state.process_row(LedgerRow {
            catalog,
            citation: citation.unwrap_or_default(),
            id,
            matcher: matcher.unwrap_or_default(),
            owner: owner.unwrap_or_default(),
            reason: reason.unwrap_or_default(),
            state,
        });
        Ok(())
    }
}

fn read_ledger_string<'de, A>(
    map: &mut A,
    slot: &mut Option<String>,
    scope: &str,
    field: &str,
    state: &mut LedgerState,
) -> std::result::Result<(), A::Error>
where
    A: MapAccess<'de>,
{
    if slot.is_some() {
        state.record_error(VerificationError::new(
            ErrorCode::Schema,
            format!("{LEDGER_PATH}: duplicate {scope} field `{field}`"),
        ));
        map.next_value::<IgnoredAny>()?;
    } else {
        *slot = Some(map.next_value()?);
    }
    Ok(())
}

fn read_ledger_states<'de, A>(
    map: &mut A,
    slot: &mut Option<Vec<String>>,
    state: &mut LedgerState,
) -> std::result::Result<(), A::Error>
where
    A: MapAccess<'de>,
{
    if slot.is_some() {
        state.record_error(VerificationError::new(
            ErrorCode::Schema,
            format!("{LEDGER_PATH}: duplicate root field `states`"),
        ));
        map.next_value::<IgnoredAny>()?;
    } else {
        *slot = Some(map.next_value()?);
    }
    Ok(())
}

fn is_allowed_state(value: &str) -> bool {
    P0_STATES.contains(&value)
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        process,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use serde_json::{Value, json};

    use super::*;
    use crate::schema::{CATALOG_NAMES, SOURCE_NAMES, SOURCES_PATH, upstream_source_name};

    const TEST_SHA512: &str =
        "9Yoji7DU6moRm1ofDaN+ftdxNcEGciiGbm7eN4MjlcCbfv7/Y/zchadcXXRmMZmN9oTPXUk9GmhjQOhADJsiSQ==";
    const TEST_COMMIT: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    static NEXT_ROOT: AtomicUsize = AtomicUsize::new(0);

    struct Fixture {
        root: PathBuf,
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    fn fixture() -> Fixture {
        let root = std::env::temp_dir().join(format!(
            "bamts-ledger-test-{}-{}",
            process::id(),
            NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("vendor/libuv-1.52.1")).unwrap();
        fs::create_dir_all(root.join("formal")).unwrap();
        fs::create_dir_all(root.join("verification/blockers")).unwrap();
        fs::create_dir_all(root.join("proof")).unwrap();

        let sources = fixture_sources();
        fs::write(root.join(SOURCES_PATH), &sources).unwrap();
        fs::write(root.join(TOOLCHAINS_PATH), fixture_toolchains()).unwrap();

        let manifest = fixture_manifest(sha256_hex(sources.as_bytes()));
        let manifest_bytes = serde_json::to_vec(&manifest).unwrap();
        fs::write(root.join(MANIFEST_PATH), &manifest_bytes).unwrap();

        fs::write(
            root.join(LEDGER_PATH),
            serde_json::to_vec(&fixture_ledger(sha256_hex(&manifest_bytes))).unwrap(),
        )
        .unwrap();
        fs::write(
            root.join(BLOCKER_PATH),
            serde_json::to_vec(&fixture_blocker()).unwrap(),
        )
        .unwrap();

        Fixture { root }
    }

    fn fixture_sources() -> String {
        let mut output = String::from("schema = \"bamti.sources/v1\"\n");
        for source in SOURCE_NAMES {
            output.push_str("\n[[source]]\n");
            output.push_str(&format!("name = \"{source}\"\n"));
            output.push_str(&format!("pin = \"{}\"\n", fixture_pin(source)));
            output.push_str(&format!("url = \"{}\"\n", fixture_url(source)));
            output.push_str(&format!(
                "digest_algorithm = \"{}\"\n",
                fixture_digest_algorithm(source)
            ));
            output.push_str(&format!("digest = \"{}\"\n", fixture_digest(source)));
            if fixture_commit(source).is_some() {
                output.push_str(&format!("commit = \"{TEST_COMMIT}\"\n"));
            }
            if source == "libuv" {
                output.push_str("vendored_path = \"vendor/libuv-1.52.1\"\n");
            }
        }
        output
    }

    fn fixture_toolchains() -> String {
        format!(
            "schema = \"bamti.formal-toolchains/v1\"\n\n[quint]\nversion = \"{}\"\nnode_minimum = \"18\"\nurl = \"{}\"\ndigest_algorithm = \"{}\"\ndigest = \"{}\"\ncommit = \"{TEST_COMMIT}\"\n\n[racket]\nversion = \"{}\"\nurl = \"{}\"\ndigest_algorithm = \"{}\"\ndigest = \"{}\"\ncommit = \"{TEST_COMMIT}\"\nredex_url = \"{}\"\nredex_digest_algorithm = \"{}\"\nredex_digest = \"{}\"\nredex_commit = \"{TEST_COMMIT}\"\n\n[lean]\nversion = \"{}\"\nurl = \"{}\"\ndigest_algorithm = \"{}\"\ndigest = \"{}\"\ncommit = \"{TEST_COMMIT}\"\n",
            fixture_pin("quint"),
            fixture_url("quint"),
            fixture_digest_algorithm("quint"),
            fixture_digest("quint"),
            fixture_pin("racket"),
            fixture_url("racket"),
            fixture_digest_algorithm("racket"),
            fixture_digest("racket"),
            fixture_url("redex"),
            fixture_digest_algorithm("redex"),
            fixture_digest("redex"),
            fixture_pin("lean"),
            fixture_url("lean"),
            fixture_digest_algorithm("lean"),
            fixture_digest("lean"),
        )
    }

    fn fixture_manifest(source_ledger_sha256: String) -> Value {
        let catalogs = CATALOG_NAMES
            .iter()
            .map(|catalog| {
                let case = fixture_case(catalog);
                json!({
                    "extractor": { "kind": "fixture" },
                    "id": catalog,
                    "identifier_count": 1,
                    "identifiers": [case],
                    "identifiers_sha256": sha256_hex(format!("{case}\n").as_bytes()),
                    "source": fixture_catalog_source(catalog),
                })
            })
            .collect::<Vec<_>>();
        json!({
            "schema": "bamti.verification-manifest/v1",
            "source_ledger_sha256": source_ledger_sha256,
            "catalogs": catalogs,
        })
    }

    fn fixture_catalog_source(catalog: &str) -> Value {
        if let Some(source) = upstream_source_name(catalog) {
            return json!({
                "pin": fixture_pin(source),
                "url": fixture_url(source),
                "digest_algorithm": fixture_digest_algorithm(source),
                "digest": fixture_digest(source),
            });
        }
        json!({
            "pin": "approved-fixture",
            "url": format!("local://{catalog}"),
            "digest_algorithm": "sha256",
            "digest": sha256_hex(catalog.as_bytes()),
        })
    }

    fn fixture_ledger(manifest_sha256: String) -> Value {
        let rows = CATALOG_NAMES
            .iter()
            .map(|catalog| {
                let case = fixture_case(catalog);
                let id = format!("{catalog}:{case}");
                let state = if catalog == &"test262" {
                    "EXTERNAL_BLOCKED"
                } else {
                    "BLOCKING_FAIL"
                };
                json!({
                    "catalog": catalog,
                    "citation": format!("https://example.invalid/{id}"),
                    "id": id,
                    "matcher": "\\Afixture\\Z",
                    "owner": "P0",
                    "reason": "fixture classification",
                    "state": state,
                })
            })
            .collect::<Vec<_>>();
        json!({
            "manifest_sha256": manifest_sha256,
            "rows": rows,
            "schema": LEDGER_SCHEMA,
            "states": P0_STATES,
        })
    }

    fn fixture_blocker() -> Value {
        json!({
            "blocked_catalog_rows": [fixture_blocked_id()],
            "decision": "fixture decision",
            "evidence": ["https://example.invalid/evidence"],
            "id": "fixture-wasm-blocker",
            "owner": "external:fixture",
            "reason": "fixture reason",
            "schema": "bamti.external-blocker/v1",
            "status": "EXTERNAL_BLOCKED",
            "unblock_condition": "fixture condition",
            "zero_match_catalogs": {
                "test262": { "runnable_rows": 0, "webassembly_or_wasi_rows": 0 }
            }
        })
    }

    fn fixture_pin(source: &str) -> String {
        match source {
            "quint" => "0.32.0".to_owned(),
            "racket" | "redex" => "9.2".to_owned(),
            "lean" => "4.32.1".to_owned(),
            _ => format!("pin-{source}"),
        }
    }

    fn fixture_url(source: &str) -> String {
        format!("https://example.invalid/{source}.tar.gz")
    }

    fn fixture_digest_algorithm(source: &str) -> &'static str {
        if source == "quint" {
            "sha512"
        } else {
            "sha256"
        }
    }

    fn fixture_digest(source: &str) -> String {
        if source == "quint" {
            TEST_SHA512.to_owned()
        } else {
            sha256_hex(source.as_bytes())
        }
    }

    fn fixture_commit(source: &str) -> Option<&'static str> {
        match source {
            "quint" | "racket" | "redex" | "lean" => Some(TEST_COMMIT),
            _ => None,
        }
    }

    fn fixture_case(catalog: &str) -> String {
        format!("case-{catalog}")
    }

    fn fixture_blocked_id() -> String {
        let catalog = "test262";
        format!("{catalog}:{}", fixture_case(catalog))
    }

    fn mutate_ledger(fixture: &Fixture, mutate: impl FnOnce(&mut Value)) {
        let path = fixture.root.join(LEDGER_PATH);
        let mut ledger = read_json(&path);
        mutate(&mut ledger);
        write_json(&path, &ledger);
    }

    fn mutate_blocker(fixture: &Fixture, mutate: impl FnOnce(&mut Value)) {
        let path = fixture.root.join(BLOCKER_PATH);
        let mut blocker = read_json(&path);
        mutate(&mut blocker);
        write_json(&path, &blocker);
    }

    fn read_json(path: &Path) -> Value {
        serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
    }

    fn write_json(path: &Path, value: &Value) {
        fs::write(path, serde_json::to_vec(value).unwrap()).unwrap();
    }

    #[test]
    fn accepts_a_tiny_streaming_ledger() {
        let fixture = fixture();
        let report = verify_ledger_g0(&fixture.root).unwrap();
        assert_eq!(report.gate, Gate::G0);
        assert_eq!(report.checks, CATALOG_NAMES.len());
    }

    #[test]
    fn rejects_duplicate_ledger_rows() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            let rows = ledger["rows"].as_array_mut().unwrap();
            let duplicate = rows[0].clone();
            rows.push(duplicate);
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::Duplicate
        );
    }

    #[test]
    fn rejects_missing_ledger_rows() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            ledger["rows"].as_array_mut().unwrap().pop();
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::SetMismatch
        );
    }

    #[test]
    fn a_pass_row_needs_no_prose_and_a_non_pass_row_does() {
        let bare = |ledger: &mut Value| {
            let row = &mut ledger["rows"].as_array_mut().unwrap()[0];
            for field in ["citation", "matcher", "owner", "reason"] {
                row.as_object_mut().unwrap().remove(field);
            }
        };
        let fixture_a = fixture();
        mutate_ledger(&fixture_a, |ledger| {
            bare(ledger);
            ledger["rows"][0]["state"] = json!("PASS");
        });
        verify_ledger_g0(&fixture_a.root).expect("a PASS row is three fields");

        let fixture_b = fixture();
        mutate_ledger(&fixture_b, bare);
        assert_eq!(
            verify_ledger_g0(&fixture_b.root).unwrap_err().code(),
            ErrorCode::Transition
        );
    }

    #[test]
    fn a_v1_ledger_is_not_read_as_v2() {
        let schema = fixture();
        mutate_ledger(&schema, |ledger| {
            ledger["schema"] = json!("bamti.completeness-ledger/v1");
        });
        assert_eq!(
            verify_ledger_g0(&schema.root).unwrap_err().code(),
            ErrorCode::Schema
        );

        let row = fixture();
        mutate_ledger(&row, |ledger| {
            ledger["rows"][0]["case"] = json!("fixture");
        });
        assert_eq!(
            verify_ledger_g0(&row.root).unwrap_err().code(),
            ErrorCode::Schema
        );
    }

    #[test]
    fn a_row_id_must_name_a_case_in_its_catalog() {
        for id in ["typescript-6.0.2:elsewhere", "typescript-7.0.2:"] {
            let fixture = fixture();
            mutate_ledger(&fixture, |ledger| {
                let row = &mut ledger["rows"].as_array_mut().unwrap()[0];
                row["catalog"] = json!("typescript-7.0.2");
                row["id"] = json!(id);
            });
            assert_eq!(
                verify_ledger_g0(&fixture.root).unwrap_err().code(),
                ErrorCode::Schema,
                "{id}"
            );
        }
    }

    #[test]
    fn rejects_extra_ledger_rows() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            let rows = ledger["rows"].as_array_mut().unwrap();
            let mut extra = rows[0].clone();
            extra["id"] = json!("typescript-7.0.2:case-extra");
            rows.push(extra);
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::SetMismatch
        );
    }

    #[test]
    fn rejects_manifest_hash_mismatch() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            ledger["manifest_sha256"] =
                json!("0000000000000000000000000000000000000000000000000000000000000000");
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::Digest
        );
    }

    #[test]
    fn rejects_unknown_ledger_state() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            ledger["rows"].as_array_mut().unwrap()[0]["state"] = json!("UNCLASSIFIED");
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::Transition
        );
    }

    #[test]
    fn rejects_unknown_ledger_field() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            ledger["rows"].as_array_mut().unwrap()[0]["unexpected"] = json!(true);
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::Schema
        );
    }

    #[test]
    fn rejects_missing_non_pass_owner() {
        let fixture = fixture();
        mutate_ledger(&fixture, |ledger| {
            ledger["rows"].as_array_mut().unwrap()[0]["owner"] = json!("");
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::Transition
        );
    }

    #[test]
    fn rejects_blocker_drift() {
        let fixture = fixture();
        mutate_blocker(&fixture, |blocker| {
            blocker["blocked_catalog_rows"]
                .as_array_mut()
                .unwrap()
                .push(json!("node-24.18.0:case-extra"));
        });
        assert_eq!(
            verify_ledger_g0(&fixture.root).unwrap_err().code(),
            ErrorCode::SetMismatch
        );
    }
}
