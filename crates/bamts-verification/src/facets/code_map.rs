use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use serde::{Deserialize, Serialize};

use crate::{ErrorCode, Result, VerificationError};
/// Repository-relative path to the BAMTS↔TS diagnostic correspondence table.
pub const DIAGNOSTIC_CODE_MAP_PATH: &str = "verification/diagnostic-code-map.json";

/// Schema version accepted by the diagnostic code map loader.
pub const DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION: u32 = 1;

/// Every current BAMTS diagnostic code the map must cover exactly once.
pub const REQUIRED_BAMTS_DIAGNOSTIC_CODES: [&str; 135] = [
    "BAMTS-L001",
    "BAMTS-L002",
    "BAMTS-L003",
    "BAMTS-L004",
    "BAMTS-L005",
    "BAMTS-L006",
    "BAMTS-L007",
    "BAMTS-L008",
    "BAMTS-L009",
    "BAMTS-L010",
    "BAMTS-L011",
    "BAMTS-L012",
    "BAMTS-L013",
    "BAMTS-L014",
    "BAMTS-L015",
    "BAMTS-L016",
    "BAMTS-P001",
    "BAMTS-P002",
    "BAMTS-P003",
    "BAMTS-P004",
    "BAMTS-P005",
    "BAMTS-P006",
    "BAMTS-P007",
    "BAMTS-P009",
    "BAMTS-P010",
    "BAMTS-P011",
    "BAMTS-P012",
    "BAMTS-P017",
    "BAMTS-P018",
    "BAMTS-P019",
    "BAMTS-P020",
    "BAMTS-P021",
    "BAMTS-C001",
    "BAMTS-C002",
    "BAMTS-C003",
    "BAMTS-C004",
    "BAMTS-C005",
    "BAMTS-C006",
    "BAMTS-C007",
    "BAMTS-C008",
    "BAMTS-C009",
    "BAMTS-C010",
    "BAMTS-C011",
    "BAMTS-C012",
    "BAMTS-C013",
    "BAMTS-C014",
    "BAMTS-C015",
    "BAMTS-C016",
    "BAMTS-C017",
    "BAMTS-C018",
    "BAMTS-C019",
    "BAMTS-C020",
    "BAMTS-C021",
    "BAMTS-C022",
    "BAMTS-C023",
    "BAMTS-C024",
    "BAMTS-C025",
    "BAMTS-C026",
    "BAMTS-C027",
    "BAMTS-C028",
    "BAMTS-C029",
    "BAMTS-C030",
    "BAMTS-C031",
    "BAMTS-C032",
    "BAMTS-C033",
    "BAMTS-C034",
    "BAMTS-C035",
    "BAMTS-C036",
    "BAMTS-C037",
    "BAMTS-C038",
    "BAMTS-C039",
    "BAMTS-C040",
    "BAMTS-C041",
    "BAMTS-C042",
    "BAMTS-C043",
    "BAMTS-C044",
    "BAMTS-C045",
    "BAMTS-C046",
    "BAMTS-C047",
    "BAMTS-C048",
    "BAMTS-C049",
    "BAMTS-C050",
    "BAMTS-C051",
    "BAMTS-C052",
    "BAMTS-C053",
    "BAMTS-C054",
    "BAMTS-C055",
    "BAMTS-C057",
    "BAMTS-C058",
    "BAMTS-C059",
    "BAMTS-C060",
    "BAMTS-C061",
    "BAMTS-C062",
    "BAMTS-C063",
    "BAMTS-C064",
    "BAMTS-C065",
    "BAMTS-C066",
    "BAMTS-C067",
    "BAMTS-C068",
    "BAMTS-C069",
    "BAMTS-C070",
    "BAMTS-C071",
    "BAMTS-C072",
    "BAMTS-C073",
    "BAMTS-C074",
    "BAMTS-C075",
    "BAMTS-C076",
    "BAMTS-C077",
    "BAMTS-C078",
    "BAMTS-C079",
    "BAMTS-C080",
    "BAMTS-C081",
    "BAMTS-C082",
    "BAMTS-C086",
    "BAMTS-C087",
    "BAMTS-C088",
    "BAMTS-C089",
    "BAMTS-C090",
    "BAMTS-C091",
    "BAMTS-C092",
    "BAMTS-C093",
    "BAMTS-C094",
    "BAMTS-C095",
    "BAMTS-C096",
    "BAMTS-C097",
    "BAMTS-C098",
    "BAMTS-C099",
    "BAMTS-C100",
    "BAMTS-C101",
    "BAMTS-C102",
    "BAMTS-C103",
    "BAMTS-C104",
    "BAMTS-C105",
    "BAMTS-C106",
    "BAMTS-C107",
];

/// Mapping status for one BAMTS diagnostic code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiagnosticMappingStatus {
    Mapped,
    Unmapped,
}

/// One BAMTS↔TS correspondence row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct DiagnosticCodeMapping {
    pub bamts_code: String,
    pub ts_code: Option<u32>,
    pub status: DiagnosticMappingStatus,
    pub evidence: String,
}

/// Validated BAMTS↔TS diagnostic correspondence table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticCodeMap {
    entries: BTreeMap<String, DiagnosticCodeMapping>,
}

impl DiagnosticCodeMap {
    /// Returns every validated mapping in BAMTS-code order.
    pub fn entries(&self) -> impl Iterator<Item = &DiagnosticCodeMapping> {
        self.entries.values()
    }

    /// Looks up a BAMTS diagnostic code.
    #[must_use]
    pub fn get(&self, bamts_code: &str) -> Option<&DiagnosticCodeMapping> {
        self.entries.get(bamts_code)
    }

    /// Returns the mapped TypeScript numeric code, if the BAMTS code is mapped.
    #[must_use]
    pub fn typescript_code(&self, bamts_code: &str) -> Option<u32> {
        self.entries
            .get(bamts_code)
            .and_then(|entry| match entry.status {
                DiagnosticMappingStatus::Mapped => entry.ts_code,
                DiagnosticMappingStatus::Unmapped => None,
            })
    }

    /// Counts entries explicitly marked unmapped.
    #[must_use]
    pub fn unmapped_count(&self) -> usize {
        self.entries
            .values()
            .filter(|entry| entry.status == DiagnosticMappingStatus::Unmapped)
            .count()
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct RawDiagnosticCodeMap {
    schema_version: u32,
    entries: Vec<DiagnosticCodeMapping>,
}

/// Loads and fully validates `verification/diagnostic-code-map.json` under `root`.
pub fn load_diagnostic_code_map(root: &Path) -> Result<DiagnosticCodeMap> {
    let path = root.join(DIAGNOSTIC_CODE_MAP_PATH);
    let text = fs::read_to_string(&path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })?;
    parse_diagnostic_code_map(&text)
}

/// Parses and fully validates a diagnostic code map document.
pub fn parse_diagnostic_code_map(text: &str) -> Result<DiagnosticCodeMap> {
    let raw: RawDiagnosticCodeMap = serde_json::from_str(text)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("{error}")))?;
    validate_diagnostic_code_map(raw)
}

fn validate_diagnostic_code_map(raw: RawDiagnosticCodeMap) -> Result<DiagnosticCodeMap> {
    if raw.schema_version != DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION {
        return Err(schema_error(format!(
            "schemaVersion must be {DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION}, found {}",
            raw.schema_version
        )));
    }

    let required: BTreeSet<&str> = REQUIRED_BAMTS_DIAGNOSTIC_CODES.iter().copied().collect();
    let mut entries = BTreeMap::new();

    for entry in raw.entries {
        validate_mapping_row(&entry)?;

        if entries.contains_key(&entry.bamts_code) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate BAMTS diagnostic code `{}`", entry.bamts_code),
            ));
        }

        if !required.contains(entry.bamts_code.as_str()) {
            return Err(schema_error(format!(
                "unknown BAMTS diagnostic code `{}`",
                entry.bamts_code
            )));
        }

        entries.insert(entry.bamts_code.clone(), entry);
    }

    let present: BTreeSet<&str> = entries.keys().map(String::as_str).collect();
    let missing: Vec<&str> = required.difference(&present).copied().collect();
    if !missing.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "diagnostic code map missing required BAMTS codes: {}",
                missing.join(", ")
            ),
        ));
    }

    Ok(DiagnosticCodeMap { entries })
}

fn validate_mapping_row(entry: &DiagnosticCodeMapping) -> Result<()> {
    if !is_well_formed_bamts_code(&entry.bamts_code) {
        return Err(schema_error(format!(
            "malformed BAMTS diagnostic code `{}`",
            entry.bamts_code
        )));
    }

    if entry.evidence.trim().is_empty() {
        return Err(schema_error(format!(
            "mapping for `{}` must include non-empty evidence",
            entry.bamts_code
        )));
    }

    match entry.status {
        DiagnosticMappingStatus::Unmapped => {
            if entry.ts_code.is_some() {
                return Err(schema_error(format!(
                    "unmapped entry `{}` must not invent a TypeScript code",
                    entry.bamts_code
                )));
            }
        }
        DiagnosticMappingStatus::Mapped => {
            let Some(ts_code) = entry.ts_code else {
                return Err(schema_error(format!(
                    "mapped entry `{}` requires a TypeScript code",
                    entry.bamts_code
                )));
            };
            if ts_code == 0 {
                return Err(schema_error(format!(
                    "mapped entry `{}` has malformed TypeScript code 0",
                    entry.bamts_code
                )));
            }
        }
    }

    Ok(())
}

fn is_well_formed_bamts_code(code: &str) -> bool {
    let Some((prefix, number)) = code.split_once('-') else {
        return false;
    };
    if prefix != "BAMTS" {
        return false;
    }
    let mut chars = number.chars();
    let Some(family) = chars.next() else {
        return false;
    };
    if !matches!(family, 'L' | 'P' | 'C') {
        return false;
    }
    let digits: String = chars.collect();
    digits.len() == 3 && digits.chars().all(|ch| ch.is_ascii_digit())
}

fn schema_error(detail: impl Into<String>) -> VerificationError {
    VerificationError::new(ErrorCode::Schema, detail)
}
