use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

use serde::{Deserialize, Serialize, de::DeserializeOwned};
use sha2::{Digest, Sha256};

use crate::{ErrorCode, Result, VerificationError};

pub const SOURCES_PATH: &str = "vendor/sources.toml";
pub const MANIFEST_PATH: &str = "verification/manifest.lock.json";
pub const LOCKFILE_PATH: &str = "package-lock.json";
pub const CLASSIFICATION_DIR: &str = "verification/classification";
pub const SET_PREVIEW_LIMIT: usize = 16;

pub const TYPESCRIPT_RELEASE: &str = "typescript-7.0.2";
pub const TYPESCRIPT_VERSION: &str = "7.0.2";
pub const TYPESCRIPT_NPM_SOURCE: &str = "typescript-primary";
pub const TYPESCRIPT_COMPILER_SOURCE: &str = "typescript-7-compiler";
pub const TYPESCRIPT_SUITE_SOURCE: &str = "typescript-primary-tests";
pub const TYPESCRIPT_NPM_INTEGRITY: &str =
    "8FYau96o3NKOhbjKi/qNvG/W5jhzxkbdm5sj9AbZ/5T5sWqn3hJgLfGx27sRKZWTvyzCP8dLRBTf5tBTSRVUNA==";
pub const COMPAT_SOURCE: &str = "typescript-compat";
pub const COMPAT_TESTS_SOURCE: &str = "typescript-compat-tests";
pub const LEGACY_SOURCE: &str = "typescript-6.0";
pub const LEGACY_TESTS_SOURCE: &str = "typescript-6.0-tests";

pub const SOURCE_NAMES: [&str; 27] = [
    "rust",
    "typescript-primary",
    "typescript-7-compiler",
    "typescript-6.0",
    "typescript-compat",
    "node-source",
    "node-headers",
    "libuv",
    "cranelift-codegen",
    "cranelift-frontend",
    "cranelift-module",
    "cranelift-jit",
    "cranelift-object",
    "wasmtime-reference",
    "test262",
    "quint",
    "lean",
    "racket",
    "redex",
    "quint-connect",
    "typescript-primary-tests",
    "typescript-6.0-tests",
    "typescript-compat-tests",
    "unicode-emoji-sequences",
    "unicode-emoji-zwj-sequences",
    "icu-properties",
    "icu-properties-data",
];

pub const CATALOG_NAMES: [&str; 8] = [
    "typescript-7.0.2",
    "typescript-6.0.2",
    "typescript-5.9.3",
    "test262",
    "formal-quint",
    "formal-lean",
    "formal-redex",
    "benchmarks",
];

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourcesDocument {
    pub schema: String,
    pub source: Vec<SourcePin>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourcePin {
    pub name: String,
    pub pin: String,
    pub url: String,
    pub digest_algorithm: String,
    pub digest: String,
    #[serde(default)]
    pub commit: Option<String>,
    #[serde(default)]
    pub vendored_path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerificationManifest {
    pub schema: String,
    pub source_ledger_sha256: String,
    pub catalogs: Vec<Catalog>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Catalog {
    pub extractor: serde_json::Value,
    pub id: String,
    pub identifier_count: usize,
    pub identifiers: Vec<String>,
    pub identifiers_sha256: String,
    pub source: CatalogSource,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CatalogSource {
    pub pin: String,
    pub url: String,
    pub digest_algorithm: String,
    pub digest: String,
}

pub fn load_sources(root: &Path) -> Result<(BTreeMap<String, SourcePin>, String)> {
    let path = root.join(SOURCES_PATH);
    let bytes = read_bytes(&path)?;
    let source_ledger_sha256 = sha256_hex(&bytes);
    let document: SourcesDocument = parse_toml(&path, &bytes)?;

    if document.schema != "bamti.sources/v1" {
        return Err(schema_error(
            &path,
            format!(
                "expected schema `bamti.sources/v1`, found `{}`",
                document.schema
            ),
        ));
    }

    let mut sources = BTreeMap::new();
    for source in document.source {
        validate_source(root, &path, &source)?;
        let source_name = source.name.clone();
        if sources.insert(source_name.clone(), source).is_some() {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate source `{source_name}`"),
            ));
        }
    }

    let expected_names = string_set(&SOURCE_NAMES);
    let actual_names = sources.keys().cloned().collect();
    if actual_names != expected_names {
        return Err(set_mismatch("source names", &expected_names, &actual_names));
    }

    let libuv = match sources.get("libuv") {
        Some(source) => source,
        None => return Err(schema_error(&path, "missing required `libuv` source")),
    };
    if libuv.vendored_path.is_none() {
        return Err(schema_error(
            &path,
            "source `libuv` must declare `vendored_path`",
        ));
    }

    Ok((sources, source_ledger_sha256))
}

pub fn validate_source(root: &Path, path: &Path, source: &SourcePin) -> Result<()> {
    for (field, value) in [
        ("name", source.name.as_str()),
        ("pin", source.pin.as_str()),
        ("url", source.url.as_str()),
    ] {
        require_nonempty(path, &format!("source `{}` {field}", source.name), value)?;
    }

    validate_digest(
        path,
        &format!("source `{}`", source.name),
        &source.digest_algorithm,
        &source.digest,
    )?;

    if let Some(commit) = &source.commit
        && !is_lower_hex(commit, 40)
    {
        return Err(schema_error(
            path,
            format!("source `{}` has malformed commit", source.name),
        ));
    }

    if let Some(vendored_path) = &source.vendored_path {
        validate_vendored_path(root, path, &source.name, vendored_path)?;
    }

    Ok(())
}

pub fn validate_vendored_path(
    root: &Path,
    path: &Path,
    source_name: &str,
    value: &str,
) -> Result<()> {
    if !is_nonempty(value) {
        return Err(schema_error(
            path,
            format!("source `{source_name}` has an empty `vendored_path`"),
        ));
    }

    let relative_path = Path::new(value);
    if relative_path.is_absolute()
        || relative_path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(schema_error(
            path,
            format!("source `{source_name}` has a non-local `vendored_path`"),
        ));
    }

    if !root.join(relative_path).is_dir() {
        return Err(schema_error(
            path,
            format!("source `{source_name}` vendored path `{value}` does not exist"),
        ));
    }

    Ok(())
}

pub fn validate_manifest(
    manifest: &VerificationManifest,
    path: &Path,
    source_ledger_sha256: &str,
    sources: &BTreeMap<String, SourcePin>,
) -> Result<BTreeSet<String>> {
    if manifest.schema != "bamti.verification-manifest/v1" {
        return Err(schema_error(
            path,
            format!(
                "expected schema `bamti.verification-manifest/v1`, found `{}`",
                manifest.schema
            ),
        ));
    }

    validate_sha256(path, "source_ledger_sha256", &manifest.source_ledger_sha256)?;
    if manifest.source_ledger_sha256 != source_ledger_sha256 {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{}: source ledger SHA-256 does not match raw {SOURCES_PATH}",
                path.display()
            ),
        ));
    }

    let mut catalog_names = BTreeSet::new();
    let mut expected_ids = BTreeSet::new();
    for catalog in &manifest.catalogs {
        require_nonempty(path, "catalog id", &catalog.id)?;
        if !catalog_names.insert(catalog.id.clone()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate catalog `{}`", catalog.id),
            ));
        }
        if !catalog.extractor.is_object() {
            return Err(schema_error(
                path,
                format!("catalog `{}` extractor must be an object", catalog.id),
            ));
        }

        validate_catalog_source(path, catalog)?;
        if let Some(source_name) = upstream_source_name(&catalog.id) {
            validate_catalog_cross_pin(path, catalog, source_by_name(sources, source_name, path)?)?;
        }
        validate_catalog_identifiers(path, catalog)?;

        for identifier in &catalog.identifiers {
            let row_id = format!("{}:{identifier}", catalog.id);
            if !expected_ids.insert(row_id.clone()) {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!("duplicate catalog row `{row_id}`"),
                ));
            }
        }
    }

    let expected_catalog_names = string_set(&CATALOG_NAMES);
    if catalog_names != expected_catalog_names {
        return Err(set_mismatch(
            "catalog names",
            &expected_catalog_names,
            &catalog_names,
        ));
    }

    Ok(expected_ids)
}

pub fn validate_catalog_source(path: &Path, catalog: &Catalog) -> Result<()> {
    for (field, value) in [
        ("pin", catalog.source.pin.as_str()),
        ("url", catalog.source.url.as_str()),
    ] {
        require_nonempty(
            path,
            &format!("catalog `{}` source {field}", catalog.id),
            value,
        )?;
    }
    validate_digest(
        path,
        &format!("catalog `{}` source", catalog.id),
        &catalog.source.digest_algorithm,
        &catalog.source.digest,
    )
}

pub fn validate_catalog_cross_pin(
    path: &Path,
    catalog: &Catalog,
    source: &SourcePin,
) -> Result<()> {
    if catalog.source.pin != source.pin || catalog.source.url != source.url {
        return Err(schema_error(
            path,
            format!(
                "catalog `{}` source pin does not match vendor source",
                catalog.id
            ),
        ));
    }
    if catalog.source.digest_algorithm != source.digest_algorithm
        || catalog.source.digest != source.digest
    {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{}: catalog `{}` source digest does not match vendor source",
                path.display(),
                catalog.id
            ),
        ));
    }
    Ok(())
}

pub fn validate_catalog_identifiers(path: &Path, catalog: &Catalog) -> Result<()> {
    if catalog.identifiers.is_empty() {
        return Err(schema_error(
            path,
            format!("catalog `{}` has no identifiers", catalog.id),
        ));
    }
    if catalog.identifier_count != catalog.identifiers.len() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "{}: catalog `{}` declares {} identifiers but contains {}",
                path.display(),
                catalog.id,
                catalog.identifier_count,
                catalog.identifiers.len()
            ),
        ));
    }

    let mut previous: Option<&str> = None;
    let mut hasher = Sha256::new();
    for identifier in &catalog.identifiers {
        if !is_nonempty(identifier) {
            return Err(schema_error(
                path,
                format!("catalog `{}` has an empty identifier", catalog.id),
            ));
        }
        if let Some(previous_identifier) = previous {
            if identifier == previous_identifier {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!(
                        "duplicate identifier `{identifier}` in catalog `{}`",
                        catalog.id
                    ),
                ));
            }
            if identifier.as_str() < previous_identifier {
                return Err(schema_error(
                    path,
                    format!(
                        "catalog `{}` identifiers are not strictly ordered",
                        catalog.id
                    ),
                ));
            }
        }
        hasher.update(identifier.as_bytes());
        hasher.update(b"\n");
        previous = Some(identifier);
    }

    validate_sha256(
        path,
        &format!("catalog `{}` identifiers_sha256", catalog.id),
        &catalog.identifiers_sha256,
    )?;
    let actual = format!("{:x}", hasher.finalize());
    if actual != catalog.identifiers_sha256 {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{}: catalog `{}` identifiers SHA-256 mismatch",
                path.display(),
                catalog.id
            ),
        ));
    }

    Ok(())
}

pub fn source_by_name<'a>(
    sources: &'a BTreeMap<String, SourcePin>,
    name: &str,
    path: &Path,
) -> Result<&'a SourcePin> {
    sources
        .get(name)
        .ok_or_else(|| schema_error(path, format!("missing source `{name}`")))
}

pub fn required_source<'a>(
    sources: &'a BTreeMap<String, SourcePin>,
    name: &str,
) -> Result<&'a SourcePin> {
    sources.get(name).ok_or_else(|| {
        VerificationError::new(ErrorCode::Schema, format!("missing source `{name}`"))
    })
}

pub fn upstream_source_name(catalog_id: &str) -> Option<&'static str> {
    match catalog_id {
        "typescript-7.0.2" => Some(TYPESCRIPT_SUITE_SOURCE),
        "typescript-6.0.2" => Some("typescript-6.0-tests"),
        "typescript-5.9.3" => Some("typescript-compat-tests"),
        "test262" => Some("test262"),
        _ => None,
    }
}

pub fn catalog_source_from_pin(source: &SourcePin) -> CatalogSource {
    CatalogSource {
        pin: source.pin.clone(),
        url: source.url.clone(),
        digest_algorithm: source.digest_algorithm.clone(),
        digest: source.digest.clone(),
    }
}

pub fn identifiers_sha256(identifiers: &[String]) -> String {
    let mut hasher = Sha256::new();
    for identifier in identifiers {
        hasher.update(identifier.as_bytes());
        hasher.update(b"\n");
    }
    format!("{:x}", hasher.finalize())
}

pub fn encode_manifest(manifest: &VerificationManifest) -> Result<Vec<u8>> {
    let mut bytes = serde_json::to_vec_pretty(manifest).map_err(|error| {
        VerificationError::new(ErrorCode::Json, format!("cannot encode manifest: {error}"))
    })?;
    if !bytes.ends_with(b"\n") {
        bytes.push(b'\n');
    }
    Ok(bytes)
}

pub fn parse_toml<T: DeserializeOwned>(path: &Path, bytes: &[u8]) -> Result<T> {
    let input = std::str::from_utf8(bytes).map_err(|_| {
        VerificationError::new(
            ErrorCode::Toml,
            format!("{}: TOML must be UTF-8", path.display()),
        )
    })?;
    toml::from_str(input).map_err(|error| {
        VerificationError::new(ErrorCode::Toml, format!("{}: {error}", path.display()))
    })
}

pub fn parse_json<T: DeserializeOwned>(path: &Path, bytes: &[u8]) -> Result<T> {
    reject_duplicate_json_keys(path, bytes)?;
    serde_json::from_slice(bytes).map_err(|error| json_error(path, error))
}

pub fn reject_duplicate_json_keys(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    NoDuplicateJson::deserialize(&mut deserializer).map_err(|error| json_error(path, error))?;
    deserializer.end().map_err(|error| json_error(path, error))
}

struct NoDuplicateJson;

impl<'de> Deserialize<'de> for NoDuplicateJson {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(NoDuplicateJsonVisitor)
    }
}

struct NoDuplicateJsonVisitor;

impl<'de> serde::de::Visitor<'de> for NoDuplicateJsonVisitor {
    type Value = NoDuplicateJson;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON value")
    }

    fn visit_bool<E>(self, _: bool) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_i64<E>(self, _: i64) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_u64<E>(self, _: u64) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_f64<E>(self, _: f64) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_str<E>(self, _: &str) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_string<E>(self, _: String) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_none<E>(self) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_unit<E>(self) -> std::result::Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(NoDuplicateJson)
    }

    fn visit_some<D>(self, deserializer: D) -> std::result::Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        NoDuplicateJson::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> std::result::Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        while sequence.next_element::<NoDuplicateJson>()?.is_some() {}
        Ok(NoDuplicateJson)
    }

    fn visit_map<A>(self, mut map: A) -> std::result::Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON key `{key}`"
                )));
            }
            map.next_value::<NoDuplicateJson>()?;
        }
        Ok(NoDuplicateJson)
    }
}

pub fn read_bytes(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| io_error(path, error))
}

pub fn io_error(path: &Path, error: std::io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

pub fn json_error(path: &Path, error: serde_json::Error) -> VerificationError {
    let code = match error.classify() {
        serde_json::error::Category::Io => ErrorCode::Io,
        serde_json::error::Category::Syntax | serde_json::error::Category::Eof => ErrorCode::Json,
        serde_json::error::Category::Data => ErrorCode::Schema,
    };
    VerificationError::new(code, format!("{}: {error}", path.display()))
}

pub fn schema_error(path: &Path, detail: impl Into<String>) -> VerificationError {
    VerificationError::new(
        ErrorCode::Schema,
        format!("{}: {}", path.display(), detail.into()),
    )
}

pub fn require_nonempty(path: &Path, field: &str, value: &str) -> Result<()> {
    if is_nonempty(value) {
        Ok(())
    } else {
        Err(schema_error(path, format!("{field} must be nonempty")))
    }
}

pub fn validate_digest(path: &Path, field: &str, algorithm: &str, digest: &str) -> Result<()> {
    let valid = match algorithm {
        "sha256" => is_lower_hex(digest, 64),
        "sha512" => is_sha512_base64(digest),
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{}: {field} has malformed `{algorithm}` digest",
                path.display()
            ),
        ))
    }
}

pub fn validate_sha256(path: &Path, field: &str, digest: &str) -> Result<()> {
    if is_lower_hex(digest, 64) {
        Ok(())
    } else {
        Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{}: {field} is not a lowercase SHA-256 digest",
                path.display()
            ),
        ))
    }
}

pub fn is_lower_hex(value: &str, length: usize) -> bool {
    value.len() == length
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

pub fn is_sha512_base64(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.len() != 88 || bytes[86] != b'=' || bytes[87] != b'=' {
        return false;
    }
    let Some(last_value) = base64_value(bytes[85]) else {
        return false;
    };
    last_value & 0b0000_1111 == 0 && bytes[..86].iter().all(|byte| base64_value(*byte).is_some())
}

pub(crate) fn base64_value(byte: u8) -> Option<u8> {
    match byte {
        b'A'..=b'Z' => Some(byte - b'A'),
        b'a'..=b'z' => Some(byte - b'a' + 26),
        b'0'..=b'9' => Some(byte - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

pub fn is_nonempty(value: &str) -> bool {
    !value.trim().is_empty()
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

pub fn string_set(values: &[&str]) -> BTreeSet<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

pub fn set_mismatch(
    kind: &str,
    expected: &BTreeSet<String>,
    actual: &BTreeSet<String>,
) -> VerificationError {
    VerificationError::new(
        ErrorCode::SetMismatch,
        format!("{kind}: {}", set_difference_detail(expected, actual)),
    )
}

pub fn set_difference_detail(expected: &BTreeSet<String>, actual: &BTreeSet<String>) -> String {
    format!(
        "missing {}; extra {}",
        summarize_ids(expected.difference(actual)),
        summarize_ids(actual.difference(expected))
    )
}

pub fn summarize_ids<'a>(ids: impl Iterator<Item = &'a String>) -> String {
    let mut count = 0;
    let mut preview = Vec::new();
    for id in ids {
        count += 1;
        if preview.len() < SET_PREVIEW_LIMIT {
            preview.push(id.as_str());
        }
    }
    let suffix = if count > preview.len() { ", ..." } else { "" };
    format!("{count} [{}{suffix}]", preview.join(", "))
}
