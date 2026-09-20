pub mod build_mode;
pub mod effective;
pub mod output;
pub mod references;
pub mod resolution;
pub mod resolution_trace;
pub mod tsconfig;

use crate::{
    lint::{LintConfig, LintLevel, LintSetting},
    source::JsxEmit,
};

use std::{
    fmt,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

const MAX_JSON_DEPTH: usize = 128;

/// A path operation that would make a project depend on the ambient working directory
/// or access a path outside its declared root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PathError {
    RootIsNotAbsolute { path: PathBuf },
    PathEscapesRoot { root: PathBuf, path: PathBuf },
    PathHasNoParent { path: PathBuf },
}

impl fmt::Display for PathError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RootIsNotAbsolute { path } => {
                write!(
                    formatter,
                    "project root must be absolute: {}",
                    path.display()
                )
            }
            Self::PathEscapesRoot { root, path } => write!(
                formatter,
                "path {} escapes project root {}",
                path.display(),
                root.display()
            ),
            Self::PathHasNoParent { path } => {
                write!(formatter, "module path has no parent: {}", path.display())
            }
        }
    }
}

impl std::error::Error for PathError {}

/// A normalized immutable project boundary.
///
/// Construction and resolution are lexical: neither operation requires the path to
/// exist. Every path returned by this type is absolute, normalized, and confined.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ProjectRoot {
    path: PathBuf,
}

impl ProjectRoot {
    /// Creates a project boundary from an absolute path without touching the file system.
    pub fn new(path: impl AsRef<Path>) -> Result<Self, PathError> {
        let path = path.as_ref();
        if !path.is_absolute() {
            return Err(PathError::RootIsNotAbsolute {
                path: path.to_path_buf(),
            });
        }
        Ok(Self {
            path: normalize_absolute(path),
        })
    }

    /// Returns the normalized absolute root.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Resolves a root-relative or already-absolute path and rejects root escapes.
    pub fn resolve(&self, path: impl AsRef<Path>) -> Result<PathBuf, PathError> {
        self.resolve_from(&self.path, path)
    }

    /// Resolves a path relative to a confined absolute directory.
    pub fn resolve_from(
        &self,
        directory: impl AsRef<Path>,
        path: impl AsRef<Path>,
    ) -> Result<PathBuf, PathError> {
        let directory = self.confine(directory)?;
        let path = path.as_ref();
        let joined = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        self.confine(joined)
    }

    /// Resolves an output-target path relative to a confined directory.
    ///
    /// Output targets (`tsBuildInfoFile`, `outFile`) may point anywhere —
    /// tsc accepts absolute and `..`-escaping values for them
    /// (incrementalTsBuildInfoFile runs clean with `/a.tsbuildinfo`;
    /// references tests use `../cache/info.json`), unlike source paths,
    /// which `resolve_from` confines.
    #[must_use]
    pub fn resolve_output_from(
        &self,
        directory: impl AsRef<Path>,
        path: impl AsRef<Path>,
    ) -> PathBuf {
        let directory = directory.as_ref();
        let path = path.as_ref();
        let joined = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        if joined.is_absolute() {
            normalize_absolute(&joined)
        } else {
            normalize_absolute(&self.path.join(joined))
        }
    }

    /// Normalizes an absolute path and verifies that it belongs to this project.
    pub fn confine(&self, path: impl AsRef<Path>) -> Result<PathBuf, PathError> {
        let original = path.as_ref();
        let absolute = if original.is_absolute() {
            normalize_absolute(original)
        } else {
            normalize_absolute(&self.path.join(original))
        };
        if absolute.starts_with(&self.path) {
            Ok(absolute)
        } else {
            Err(PathError::PathEscapesRoot {
                root: self.path.clone(),
                path: absolute,
            })
        }
    }
}

fn normalize_absolute(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            Component::Normal(part) => normalized.push(part),
        }
    }
    normalized
}

/// The reason a JSON-with-comments document was rejected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsoncErrorKind {
    UnexpectedEnd,
    UnexpectedToken,
    UnterminatedBlockComment,
    UnterminatedString,
    InvalidEscape,
    InvalidUnicodeEscape,
    LoneSurrogate,
    UnescapedControlCharacter,
    InvalidNumber,
    TrailingCharacters,
    NestingTooDeep,
}

/// An offset-bearing JSONC parse error. `offset` is a UTF-8 byte offset into the
/// original document, which makes it safe to use directly with file I/O diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsoncError {
    offset: usize,
    kind: JsoncErrorKind,
}

impl JsoncError {
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    #[must_use]
    pub const fn kind(&self) -> &JsoncErrorKind {
        &self.kind
    }
}

impl fmt::Display for JsoncError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "JSONC error at byte {}: ", self.offset)?;
        match &self.kind {
            JsoncErrorKind::UnexpectedEnd => formatter.write_str("unexpected end of input"),
            JsoncErrorKind::UnexpectedToken => formatter.write_str("unexpected token"),
            JsoncErrorKind::UnterminatedBlockComment => {
                formatter.write_str("unterminated block comment")
            }
            JsoncErrorKind::UnterminatedString => formatter.write_str("unterminated string"),
            JsoncErrorKind::InvalidEscape => formatter.write_str("invalid string escape"),
            JsoncErrorKind::InvalidUnicodeEscape => formatter.write_str("invalid Unicode escape"),
            JsoncErrorKind::LoneSurrogate => formatter.write_str("lone UTF-16 surrogate"),
            JsoncErrorKind::UnescapedControlCharacter => {
                formatter.write_str("unescaped control character in string")
            }
            JsoncErrorKind::InvalidNumber => formatter.write_str("invalid number"),
            JsoncErrorKind::TrailingCharacters => {
                formatter.write_str("characters follow the root value")
            }
            JsoncErrorKind::NestingTooDeep => formatter.write_str("nesting limit exceeded"),
        }
    }
}

impl std::error::Error for JsoncError {}

/// An immutable JSON object that preserves declaration order for package condition maps.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsonObject {
    entries: Arc<[(Arc<str>, JsonValue)]>,
}

impl JsonObject {
    #[must_use]
    pub fn from_entries(entries: Vec<(Arc<str>, JsonValue)>) -> Self {
        Self {
            entries: Arc::from(entries),
        }
    }

    #[must_use]
    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        self.entries
            .iter()
            .find_map(|(candidate, value)| (candidate.as_ref() == key).then_some(value))
    }

    #[must_use]
    pub fn entries(&self) -> &[(Arc<str>, JsonValue)] {
        &self.entries
    }
}

/// A dependency-free immutable JSON value used for tsconfig and package metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(Arc<str>),
    String(Arc<str>),
    Array(Arc<[JsonValue]>),
    Object(JsonObject),
}

impl JsonValue {
    #[must_use]
    pub const fn as_object(&self) -> Option<&JsonObject> {
        if let Self::Object(value) = self {
            Some(value)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(value) = self {
            Some(value)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(value) = self {
            Some(*value)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_array(&self) -> Option<&[JsonValue]> {
        if let Self::Array(value) = self {
            Some(value)
        } else {
            None
        }
    }
}

/// Parses strict JSON plus line comments, block comments, and trailing commas.
/// Comments inside strings remain ordinary string content.
pub fn parse_jsonc(source: &str) -> Result<JsonValue, JsoncError> {
    JsoncParser::new(source).parse()
}

struct JsoncParser<'a> {
    source: &'a str,
    bytes: &'a [u8],
    position: usize,
}

impl<'a> JsoncParser<'a> {
    const fn new(source: &'a str) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            position: 0,
        }
    }

    fn parse(mut self) -> Result<JsonValue, JsoncError> {
        self.skip_trivia()?;
        let value = self.parse_value(0)?;
        self.skip_trivia()?;
        if self.position != self.bytes.len() {
            return self.error(JsoncErrorKind::TrailingCharacters);
        }
        Ok(value)
    }

    fn parse_value(&mut self, depth: usize) -> Result<JsonValue, JsoncError> {
        if depth > MAX_JSON_DEPTH {
            return self.error(JsoncErrorKind::NestingTooDeep);
        }
        self.skip_trivia()?;
        match self.peek() {
            Some(b'{') => self.parse_object(depth + 1),
            Some(b'[') => self.parse_array(depth + 1),
            Some(b'"') => self.parse_string().map(JsonValue::String),
            Some(b't') => {
                self.expect_literal(b"true")?;
                Ok(JsonValue::Bool(true))
            }
            Some(b'f') => {
                self.expect_literal(b"false")?;
                Ok(JsonValue::Bool(false))
            }
            Some(b'n') => {
                self.expect_literal(b"null")?;
                Ok(JsonValue::Null)
            }
            Some(b'-' | b'0'..=b'9') => self.parse_number().map(JsonValue::Number),
            Some(_) => self.error(JsoncErrorKind::UnexpectedToken),
            None => self.error(JsoncErrorKind::UnexpectedEnd),
        }
    }

    fn parse_object(&mut self, depth: usize) -> Result<JsonValue, JsoncError> {
        self.position += 1;
        self.skip_trivia()?;
        let mut entries: Vec<(Arc<str>, JsonValue)> = Vec::new();
        if self.consume(b'}') {
            return Ok(JsonValue::Object(JsonObject {
                entries: Arc::from(entries),
            }));
        }
        loop {
            self.skip_trivia()?;
            if self.peek() != Some(b'"') {
                return self.error(JsoncErrorKind::UnexpectedToken);
            }
            let key = self.parse_string()?;
            self.skip_trivia()?;
            if !self.consume(b':') {
                return self.error(JsoncErrorKind::UnexpectedToken);
            }
            let value = self.parse_value(depth)?;
            // TypeScript's tsconfig parser uses last-wins for duplicate keys.
            // Replace any existing entry with the same key so `get` and
            // `entries` expose only the surviving value.
            if let Some(slot) = entries
                .iter_mut()
                .find(|(existing, _)| existing.as_ref() == key.as_ref())
            {
                slot.1 = value;
            } else {
                entries.push((key, value));
            }
            self.skip_trivia()?;
            if self.consume(b'}') {
                break;
            }
            if !self.consume(b',') {
                return self.error(JsoncErrorKind::UnexpectedToken);
            }
            self.skip_trivia()?;
            if self.consume(b'}') {
                break;
            }
        }
        Ok(JsonValue::Object(JsonObject {
            entries: Arc::from(entries),
        }))
    }

    fn parse_array(&mut self, depth: usize) -> Result<JsonValue, JsoncError> {
        self.position += 1;
        self.skip_trivia()?;
        let mut values = Vec::new();
        if self.consume(b']') {
            return Ok(JsonValue::Array(Arc::from(values)));
        }
        loop {
            values.push(self.parse_value(depth)?);
            self.skip_trivia()?;
            if self.consume(b']') {
                break;
            }
            if !self.consume(b',') {
                return self.error(JsoncErrorKind::UnexpectedToken);
            }
            self.skip_trivia()?;
            if self.consume(b']') {
                break;
            }
        }
        Ok(JsonValue::Array(Arc::from(values)))
    }

    fn parse_string(&mut self) -> Result<Arc<str>, JsoncError> {
        let opening = self.position;
        self.position += 1;
        let content_start = self.position;
        let mut decoded: Option<String> = None;
        let mut segment_start = content_start;
        while let Some(byte) = self.peek() {
            match byte {
                b'"' => {
                    let end = self.position;
                    self.position += 1;
                    if let Some(mut text) = decoded {
                        text.push_str(&self.source[segment_start..end]);
                        return Ok(Arc::from(text));
                    }
                    return Ok(Arc::from(&self.source[content_start..end]));
                }
                b'\\' => {
                    let escape_start = self.position;
                    let text = decoded.get_or_insert_with(String::new);
                    text.push_str(&self.source[segment_start..escape_start]);
                    self.position += 1;
                    let escape = self.peek().ok_or(JsoncError {
                        offset: opening,
                        kind: JsoncErrorKind::UnterminatedString,
                    })?;
                    self.position += 1;
                    match escape {
                        b'"' => text.push('"'),
                        b'\\' => text.push('\\'),
                        b'/' => text.push('/'),
                        b'b' => text.push('\u{0008}'),
                        b'f' => text.push('\u{000c}'),
                        b'n' => text.push('\n'),
                        b'r' => text.push('\r'),
                        b't' => text.push('\t'),
                        b'u' => {
                            let first_offset = self.position;
                            let first = self.parse_hex_quad()?;
                            let scalar = if (0xd800..=0xdbff).contains(&first) {
                                if self.bytes.get(self.position..self.position + 2) != Some(b"\\u")
                                {
                                    return Err(JsoncError {
                                        offset: first_offset,
                                        kind: JsoncErrorKind::LoneSurrogate,
                                    });
                                }
                                self.position += 2;
                                let second_offset = self.position;
                                let second = self.parse_hex_quad()?;
                                if !(0xdc00..=0xdfff).contains(&second) {
                                    return Err(JsoncError {
                                        offset: second_offset,
                                        kind: JsoncErrorKind::LoneSurrogate,
                                    });
                                }
                                0x1_0000
                                    + ((u32::from(first) - 0xd800) << 10)
                                    + (u32::from(second) - 0xdc00)
                            } else if (0xdc00..=0xdfff).contains(&first) {
                                return Err(JsoncError {
                                    offset: first_offset,
                                    kind: JsoncErrorKind::LoneSurrogate,
                                });
                            } else {
                                u32::from(first)
                            };
                            let character = char::from_u32(scalar).ok_or(JsoncError {
                                offset: first_offset,
                                kind: JsoncErrorKind::InvalidUnicodeEscape,
                            })?;
                            text.push(character);
                        }
                        _ => {
                            return Err(JsoncError {
                                offset: escape_start,
                                kind: JsoncErrorKind::InvalidEscape,
                            });
                        }
                    }
                    segment_start = self.position;
                }
                0x00..=0x1f => {
                    return self.error(JsoncErrorKind::UnescapedControlCharacter);
                }
                _ => {
                    let character =
                        self.source[self.position..]
                            .chars()
                            .next()
                            .ok_or(JsoncError {
                                offset: opening,
                                kind: JsoncErrorKind::UnterminatedString,
                            })?;
                    self.position += character.len_utf8();
                }
            }
        }
        Err(JsoncError {
            offset: opening,
            kind: JsoncErrorKind::UnterminatedString,
        })
    }

    fn parse_hex_quad(&mut self) -> Result<u16, JsoncError> {
        let start = self.position;
        let end = start.saturating_add(4);
        let digits = self.bytes.get(start..end).ok_or(JsoncError {
            offset: start,
            kind: JsoncErrorKind::InvalidUnicodeEscape,
        })?;
        let mut value = 0_u16;
        for &digit in digits {
            value = value
                .checked_mul(16)
                .and_then(|prefix| hex_value(digit).map(|suffix| prefix + suffix))
                .ok_or(JsoncError {
                    offset: start,
                    kind: JsoncErrorKind::InvalidUnicodeEscape,
                })?;
        }
        self.position = end;
        Ok(value)
    }

    fn parse_number(&mut self) -> Result<Arc<str>, JsoncError> {
        let start = self.position;
        self.consume(b'-');
        match self.peek() {
            Some(b'0') => {
                self.position += 1;
                if matches!(self.peek(), Some(b'0'..=b'9')) {
                    return self.error(JsoncErrorKind::InvalidNumber);
                }
            }
            Some(b'1'..=b'9') => {
                self.position += 1;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.position += 1;
                }
            }
            _ => return self.error(JsoncErrorKind::InvalidNumber),
        }
        if self.consume(b'.') {
            if !matches!(self.peek(), Some(b'0'..=b'9')) {
                return self.error(JsoncErrorKind::InvalidNumber);
            }
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.position += 1;
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.position += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.position += 1;
            }
            if !matches!(self.peek(), Some(b'0'..=b'9')) {
                return self.error(JsoncErrorKind::InvalidNumber);
            }
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.position += 1;
            }
        }
        Ok(Arc::from(&self.source[start..self.position]))
    }

    fn expect_literal(&mut self, literal: &[u8]) -> Result<(), JsoncError> {
        if self.bytes.get(self.position..self.position + literal.len()) == Some(literal) {
            self.position += literal.len();
            Ok(())
        } else {
            self.error(JsoncErrorKind::UnexpectedToken)
        }
    }

    fn skip_trivia(&mut self) -> Result<(), JsoncError> {
        loop {
            while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n')) {
                self.position += 1;
            }
            match self.bytes.get(self.position..self.position + 2) {
                Some(b"//") => {
                    self.position += 2;
                    while !matches!(self.peek(), None | Some(b'\r' | b'\n')) {
                        self.position += 1;
                    }
                }
                Some(b"/*") => {
                    let start = self.position;
                    self.position += 2;
                    while self.bytes.get(self.position..self.position + 2) != Some(b"*/") {
                        if self.position == self.bytes.len() {
                            return Err(JsoncError {
                                offset: start,
                                kind: JsoncErrorKind::UnterminatedBlockComment,
                            });
                        }
                        self.position += 1;
                    }
                    self.position += 2;
                }
                _ => return Ok(()),
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.position).copied()
    }

    fn consume(&mut self, expected: u8) -> bool {
        if self.peek() == Some(expected) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn error<T>(&self, kind: JsoncErrorKind) -> Result<T, JsoncError> {
        Err(JsoncError {
            offset: self.position,
            kind,
        })
    }
}

const fn hex_value(byte: u8) -> Option<u16> {
    match byte {
        b'0'..=b'9' => Some((byte - b'0') as u16),
        b'a'..=b'f' => Some((byte - b'a' + 10) as u16),
        b'A'..=b'F' => Some((byte - b'A' + 10) as u16),
        _ => None,
    }
}

/// A syntax or value error in the lint-owned portion of `bamts.toml`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BamtsTomlError {
    line: usize,
    message: Arc<str>,
}

impl BamtsTomlError {
    #[must_use]
    pub const fn line(&self) -> usize {
        self.line
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for BamtsTomlError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "bamts.toml:{}: {}", self.line, self.message)
    }
}

impl std::error::Error for BamtsTomlError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LintTomlSection {
    Other,
    Groups,
    Rules,
}

/// Parses only `[lints.groups]` and `[lints.rules]` from an already-loaded
/// `bamts.toml`. Other native BamTS sections remain owned by their subsystems.
pub fn parse_bamts_toml(source: &str) -> Result<LintConfig, BamtsTomlError> {
    let mut section = LintTomlSection::Other;
    let mut groups = Vec::new();
    let mut rules = Vec::new();
    for (line_index, raw_line) in source.lines().enumerate() {
        let line_number = line_index + 1;
        let line = strip_toml_comment(raw_line).trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            let Some(name) = line
                .strip_prefix('[')
                .and_then(|line| line.strip_suffix(']'))
            else {
                return Err(bamts_toml_error(line_number, "malformed table header"));
            };
            section = match name.trim() {
                "lints.groups" => LintTomlSection::Groups,
                "lints.rules" => LintTomlSection::Rules,
                _ => LintTomlSection::Other,
            };
            continue;
        }
        if section == LintTomlSection::Other {
            continue;
        }
        let Some((raw_name, raw_level)) = line.split_once('=') else {
            return Err(bamts_toml_error(
                line_number,
                "lint setting must be `name = \"level\"`",
            ));
        };
        let name = parse_toml_atom(raw_name.trim()).ok_or_else(|| {
            bamts_toml_error(
                line_number,
                "lint name must be a non-empty bare or quoted key",
            )
        })?;
        let level_name = parse_toml_atom(raw_level.trim())
            .ok_or_else(|| bamts_toml_error(line_number, "lint level must be a quoted string"))?;
        if !raw_level.trim().starts_with('"') {
            return Err(bamts_toml_error(
                line_number,
                "lint level must be a quoted string",
            ));
        }
        let level = level_name.parse::<LintLevel>().map_err(|_| {
            bamts_toml_error(
                line_number,
                "lint level must be one of allow, warn, deny, or forbid",
            )
        })?;
        let setting = LintSetting::new(name, level, format!("bamts.toml:{line_number}"));
        match section {
            LintTomlSection::Groups => groups.push(setting),
            LintTomlSection::Rules => rules.push(setting),
            LintTomlSection::Other => unreachable!("other sections were skipped"),
        }
    }
    Ok(LintConfig::new(groups, rules))
}

fn strip_toml_comment(line: &str) -> &str {
    let mut quoted = false;
    let mut escaped = false;
    for (index, character) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        match character {
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            '#' if !quoted => return &line[..index],
            _ => {}
        }
    }
    line
}

fn parse_toml_atom(value: &str) -> Option<&str> {
    if let Some(quoted) = value
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
    {
        (!quoted.is_empty() && !quoted.contains(['"', '\\'])).then_some(quoted)
    } else {
        (!value.is_empty()
            && value
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')))
        .then_some(value)
    }
}

fn bamts_toml_error(line: usize, message: &'static str) -> BamtsTomlError {
    BamtsTomlError {
        line,
        message: Arc::from(message),
    }
}

/// A strict tsconfig schema or confinement failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigError {
    Json(JsoncError),
    Path(PathError),
    RootMustBeObject,
    InvalidField {
        field: Arc<str>,
        expected: &'static str,
    },
}

impl fmt::Display for ConfigError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Json(error) => error.fmt(formatter),
            Self::Path(error) => error.fmt(formatter),
            Self::RootMustBeObject => formatter.write_str("tsconfig root must be an object"),
            Self::InvalidField { field, expected } => {
                write!(formatter, "tsconfig field {field:?} must be {expected}")
            }
        }
    }
}

impl std::error::Error for ConfigError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Json(error) => Some(error),
            Self::Path(error) => Some(error),
            Self::RootMustBeObject | Self::InvalidField { .. } => None,
        }
    }
}

impl From<JsoncError> for ConfigError {
    fn from(error: JsoncError) -> Self {
        Self::Json(error)
    }
}

impl From<PathError> for ConfigError {
    fn from(error: PathError) -> Self {
        Self::Path(error)
    }
}

/// One immutable `compilerOptions.paths` entry. Targets are normalized absolute
/// patterns confined to the project root; `*` remains a literal substitution marker.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathMapping {
    pattern: Arc<str>,
    targets: Arc<[PathBuf]>,
}

impl PathMapping {
    #[must_use]
    pub fn pattern(&self) -> &str {
        &self.pattern
    }

    #[must_use]
    pub fn targets(&self) -> &[PathBuf] {
        &self.targets
    }
}
/// The deliberately narrow tsconfig view consumed by lint configuration.
///
/// No TypeScript strictness switch changes BamTS lint levels; those live only in
/// `bamts.toml` and the BamTS profile/CLI surface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LintTsConfig {
    target: Option<Arc<str>>,
    module: Option<Arc<str>>,
    module_resolution: Option<Arc<str>>,
    paths: Arc<[PathMapping]>,
}

impl LintTsConfig {
    /// Parses only `paths`, `target`, `module`, and `moduleResolution`.
    pub fn parse(
        root: &ProjectRoot,
        config_path: impl AsRef<Path>,
        source: &str,
    ) -> Result<Self, ConfigError> {
        let path = root.confine(config_path)?;
        let directory = path
            .parent()
            .ok_or_else(|| PathError::PathHasNoParent { path: path.clone() })?;
        let raw = parse_jsonc(source)?
            .as_object()
            .ok_or(ConfigError::RootMustBeObject)?
            .clone();
        let compiler = match raw.get("compilerOptions") {
            None => None,
            Some(value) => Some(value.as_object().ok_or_else(|| ConfigError::InvalidField {
                field: Arc::from("compilerOptions"),
                expected: "an object",
            })?),
        };
        Ok(Self {
            target: optional_nested_string(compiler, "target")?,
            module: optional_nested_string(compiler, "module")?,
            module_resolution: optional_nested_string(compiler, "moduleResolution")?,
            paths: parse_path_mappings(root, directory, compiler)?,
        })
    }

    #[must_use]
    pub fn target(&self) -> Option<&str> {
        self.target.as_deref()
    }

    #[must_use]
    pub fn module(&self) -> Option<&str> {
        self.module.as_deref()
    }

    #[must_use]
    pub fn module_resolution(&self) -> Option<&str> {
        self.module_resolution.as_deref()
    }

    #[must_use]
    pub fn paths(&self) -> &[PathMapping] {
        &self.paths
    }
}

/// The compiler options needed by deterministic project and module resolution.
/// Unknown compiler options remain available through [`ProjectConfig::raw`] so this
/// foundation does not silently reinterpret options owned by later compiler phases.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilerOptions {
    target: Option<Arc<str>>,
    lib: Arc<[Arc<str>]>,
    module: Option<Arc<str>>,
    module_resolution: Option<Arc<str>>,
    jsx: Option<JsxEmit>,
    jsx_factory: Option<Arc<str>>,
    jsx_fragment_factory: Option<Arc<str>>,
    jsx_import_source: Option<Arc<str>>,
    strict: bool,
    no_implicit_any: bool,
    strict_null_checks: bool,
    strict_property_initialization: bool,
    always_strict: bool,
    use_define_for_class_fields: Option<bool>,
    import_helpers: Option<bool>,
    allow_js: bool,
    check_js: bool,
    resolve_json_module: bool,
    declaration: bool,
    declaration_map: bool,
    declaration_dir: Option<PathBuf>,
    source_map: bool,
    inline_source_map: bool,
    inline_sources: bool,
    no_emit_helpers: bool,
    map_root: Option<Arc<str>>,
    source_root: Option<Arc<str>>,
    no_emit: bool,
    no_emit_on_error: bool,
    emit_declaration_only: bool,
    incremental: bool,
    composite: bool,
    ts_build_info_file: Option<PathBuf>,
    new_line: Option<Arc<str>>,
    out_file: Option<PathBuf>,
    base_url: PathBuf,
    root_dir: Option<PathBuf>,
    out_dir: Option<PathBuf>,
    paths: Arc<[PathMapping]>,
}

impl CompilerOptions {
    #[must_use]
    pub fn target(&self) -> Option<&str> {
        self.target.as_deref()
    }

    #[must_use]
    pub fn lib(&self) -> &[Arc<str>] {
        &self.lib
    }

    #[must_use]
    pub fn module(&self) -> Option<&str> {
        self.module.as_deref()
    }

    #[must_use]
    pub fn module_resolution(&self) -> Option<&str> {
        self.module_resolution.as_deref()
    }

    #[must_use]
    pub const fn jsx(&self) -> Option<JsxEmit> {
        self.jsx
    }

    #[must_use]
    pub fn jsx_factory(&self) -> Option<&str> {
        self.jsx_factory.as_deref()
    }

    #[must_use]
    pub fn jsx_fragment_factory(&self) -> Option<&str> {
        self.jsx_fragment_factory.as_deref()
    }

    #[must_use]
    pub fn jsx_import_source(&self) -> Option<&str> {
        self.jsx_import_source.as_deref()
    }

    #[must_use]
    pub const fn strict(&self) -> bool {
        self.strict
    }

    #[must_use]
    pub const fn no_implicit_any(&self) -> bool {
        self.no_implicit_any
    }

    #[must_use]
    pub const fn strict_null_checks(&self) -> bool {
        self.strict_null_checks
    }

    #[must_use]
    pub const fn strict_property_initialization(&self) -> bool {
        self.strict_property_initialization
    }

    #[must_use]
    pub const fn always_strict(&self) -> bool {
        self.always_strict
    }

    #[must_use]
    pub const fn no_emit_helpers(&self) -> bool {
        self.no_emit_helpers
    }
    #[must_use]
    pub const fn use_define_for_class_fields(&self) -> Option<bool> {
        self.use_define_for_class_fields
    }

    #[must_use]
    pub const fn import_helpers(&self) -> Option<bool> {
        self.import_helpers
    }

    #[must_use]
    pub const fn allow_js(&self) -> bool {
        self.allow_js
    }

    #[must_use]
    pub const fn check_js(&self) -> bool {
        self.check_js
    }

    #[must_use]
    pub const fn resolve_json_module(&self) -> bool {
        self.resolve_json_module
    }
    #[must_use]
    pub const fn declaration(&self) -> bool {
        self.declaration
    }

    #[must_use]
    pub const fn declaration_map(&self) -> bool {
        self.declaration_map
    }

    #[must_use]
    pub fn declaration_dir(&self) -> Option<&Path> {
        self.declaration_dir.as_deref()
    }

    #[must_use]
    pub const fn source_map(&self) -> bool {
        self.source_map
    }

    #[must_use]
    pub const fn inline_source_map(&self) -> bool {
        self.inline_source_map
    }

    #[must_use]
    pub const fn inline_sources(&self) -> bool {
        self.inline_sources
    }

    #[must_use]
    pub fn map_root(&self) -> Option<&str> {
        self.map_root.as_deref()
    }

    #[must_use]
    pub fn source_root(&self) -> Option<&str> {
        self.source_root.as_deref()
    }

    #[must_use]
    pub const fn no_emit(&self) -> bool {
        self.no_emit
    }

    #[must_use]
    pub const fn no_emit_on_error(&self) -> bool {
        self.no_emit_on_error
    }

    #[must_use]
    pub const fn emit_declaration_only(&self) -> bool {
        self.emit_declaration_only
    }

    #[must_use]
    pub const fn incremental(&self) -> bool {
        self.incremental
    }

    #[must_use]
    pub const fn composite(&self) -> bool {
        self.composite
    }

    #[must_use]
    pub fn ts_build_info_file(&self) -> Option<&Path> {
        self.ts_build_info_file.as_deref()
    }

    #[must_use]
    pub fn new_line(&self) -> Option<&str> {
        self.new_line.as_deref()
    }

    #[must_use]
    pub fn out_file(&self) -> Option<&Path> {
        self.out_file.as_deref()
    }

    #[must_use]
    pub fn base_url(&self) -> &Path {
        &self.base_url
    }

    #[must_use]
    pub fn root_dir(&self) -> Option<&Path> {
        self.root_dir.as_deref()
    }

    #[must_use]
    pub fn out_dir(&self) -> Option<&Path> {
        self.out_dir.as_deref()
    }

    #[must_use]
    pub fn paths(&self) -> &[PathMapping] {
        &self.paths
    }
}

/// Immutable, validated tsconfig metadata. Parsing performs no reads and does not
/// resolve `extends`; callers can load that named document under their own I/O policy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectConfig {
    path: PathBuf,
    extends: Option<Arc<str>>,
    files: Arc<[PathBuf]>,
    include: Arc<[Arc<str>]>,
    exclude: Arc<[Arc<str>]>,
    options: CompilerOptions,
    raw: JsonObject,
}

impl ProjectConfig {
    /// Parses one already-loaded tsconfig and confines every concrete path it names.
    pub fn parse(
        root: &ProjectRoot,
        config_path: impl AsRef<Path>,
        source: &str,
    ) -> Result<Self, ConfigError> {
        let value = parse_jsonc(source)?;
        let raw = value
            .as_object()
            .ok_or(ConfigError::RootMustBeObject)?
            .clone();
        Self::parse_value(root, config_path, raw)
    }

    /// Parses an already-decoded tsconfig object.
    pub fn parse_value(
        root: &ProjectRoot,
        config_path: impl AsRef<Path>,
        raw: JsonObject,
    ) -> Result<Self, ConfigError> {
        let path = root.confine(config_path)?;
        let directory = path
            .parent()
            .ok_or_else(|| PathError::PathHasNoParent { path: path.clone() })?;
        let extends = optional_string(&raw, "extends")?;
        let files = path_list(root, directory, &raw, "files")?;
        let include = string_list(&raw, "include")?;
        let exclude = string_list(&raw, "exclude")?;
        validate_patterns(root, directory, "include", &include)?;
        validate_patterns(root, directory, "exclude", &exclude)?;

        let compiler = match raw.get("compilerOptions") {
            None => None,
            Some(value) => Some(value.as_object().ok_or_else(|| ConfigError::InvalidField {
                field: Arc::from("compilerOptions"),
                expected: "an object",
            })?),
        };
        let base_url = optional_path(root, directory, compiler, "baseUrl")?
            .unwrap_or_else(|| directory.to_path_buf());
        let paths = parse_path_mappings(root, &base_url, compiler)?;
        let strict = optional_bool(compiler, "strict")?.unwrap_or(false);
        let options = CompilerOptions {
            target: optional_nested_string(compiler, "target")?,
            lib: optional_nested_string_array(compiler, "lib")?,
            module: optional_nested_string(compiler, "module")?,
            module_resolution: optional_nested_string(compiler, "moduleResolution")?,
            jsx: optional_jsx_emit(compiler)?,
            jsx_factory: optional_nested_string(compiler, "jsxFactory")?,
            jsx_fragment_factory: optional_nested_string(compiler, "jsxFragmentFactory")?,
            jsx_import_source: optional_nested_string(compiler, "jsxImportSource")?,
            ts_build_info_file: optional_output_path(root, directory, compiler, "tsBuildInfoFile")?,
            strict,
            no_implicit_any: optional_bool(compiler, "noImplicitAny")?.unwrap_or(strict),
            strict_null_checks: optional_bool(compiler, "strictNullChecks")?.unwrap_or(strict),
            strict_property_initialization: optional_bool(
                compiler,
                "strictPropertyInitialization",
            )?
            .unwrap_or(strict),
            always_strict: optional_bool(compiler, "alwaysStrict")?.unwrap_or(strict),
            use_define_for_class_fields: optional_bool(compiler, "useDefineForClassFields")?,
            import_helpers: optional_bool(compiler, "importHelpers")?,
            allow_js: optional_bool(compiler, "allowJs")?.unwrap_or(false),
            check_js: optional_bool(compiler, "checkJs")?.unwrap_or(false),
            resolve_json_module: optional_bool(compiler, "resolveJsonModule")?.unwrap_or(false),
            declaration: optional_bool(compiler, "declaration")?.unwrap_or(false),
            declaration_map: optional_bool(compiler, "declarationMap")?.unwrap_or(false),
            declaration_dir: optional_path(root, directory, compiler, "declarationDir")?,
            source_map: optional_bool(compiler, "sourceMap")?.unwrap_or(false),
            inline_source_map: optional_bool(compiler, "inlineSourceMap")?.unwrap_or(false),
            inline_sources: optional_bool(compiler, "inlineSources")?.unwrap_or(false),
            no_emit_helpers: optional_bool(compiler, "noEmitHelpers")?.unwrap_or(false),
            map_root: optional_nested_string(compiler, "mapRoot")?,
            source_root: optional_nested_string(compiler, "sourceRoot")?,
            no_emit: optional_bool(compiler, "noEmit")?.unwrap_or(false),
            no_emit_on_error: optional_bool(compiler, "noEmitOnError")?.unwrap_or(false),
            emit_declaration_only: optional_bool(compiler, "emitDeclarationOnly")?.unwrap_or(false),
            incremental: optional_bool(compiler, "incremental")?.unwrap_or(false),
            composite: optional_bool(compiler, "composite")?.unwrap_or(false),
            new_line: optional_nested_string(compiler, "newLine")?,
            out_file: optional_path(root, directory, compiler, "outFile")?,
            base_url,
            root_dir: optional_path(root, directory, compiler, "rootDir")?,
            out_dir: optional_path(root, directory, compiler, "outDir")?,
            paths,
        };
        Ok(Self {
            path,
            extends,
            files,
            include,
            exclude,
            options,
            raw,
        })
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub fn extends(&self) -> Option<&str> {
        self.extends.as_deref()
    }

    #[must_use]
    pub fn files(&self) -> &[PathBuf] {
        &self.files
    }

    #[must_use]
    pub fn include(&self) -> &[Arc<str>] {
        &self.include
    }

    #[must_use]
    pub fn exclude(&self) -> &[Arc<str>] {
        &self.exclude
    }

    #[must_use]
    pub const fn options(&self) -> &CompilerOptions {
        &self.options
    }

    #[must_use]
    pub const fn raw(&self) -> &JsonObject {
        &self.raw
    }
}

fn invalid_field(field: impl Into<Arc<str>>, expected: &'static str) -> ConfigError {
    ConfigError::InvalidField {
        field: field.into(),
        expected,
    }
}

fn optional_string(
    object: &JsonObject,
    key: &'static str,
) -> Result<Option<Arc<str>>, ConfigError> {
    object
        .get(key)
        .map(|value| {
            value
                .as_str()
                .map(Arc::from)
                .ok_or_else(|| invalid_field(key, "a string"))
        })
        .transpose()
}

fn optional_nested_string(
    object: Option<&JsonObject>,
    key: &'static str,
) -> Result<Option<Arc<str>>, ConfigError> {
    object.map_or(Ok(None), |object| optional_string(object, key))
}

fn optional_nested_string_array(
    object: Option<&JsonObject>,
    key: &'static str,
) -> Result<Arc<[Arc<str>]>, ConfigError> {
    let Some(object) = object else {
        return Ok(Arc::from([]));
    };
    let Some(value) = object.get(key) else {
        return Ok(Arc::from([]));
    };
    let values = value
        .as_array()
        .ok_or_else(|| invalid_field(key, "an array of strings"))?;
    let parsed: Result<Vec<Arc<str>>, ConfigError> = values
        .iter()
        .map(|value| {
            value
                .as_str()
                .map(Arc::from)
                .ok_or_else(|| invalid_field(key, "an array of strings"))
        })
        .collect();
    Ok(Arc::from(parsed?))
}

fn optional_jsx_emit(object: Option<&JsonObject>) -> Result<Option<JsxEmit>, ConfigError> {
    optional_nested_string(object, "jsx")?
        .map(|value| {
            value.trim().to_ascii_lowercase().parse().map_err(|()| {
                invalid_field(
                    "jsx",
                    r#"one of "preserve", "react", "react-native", "react-jsx", or "react-jsxdev""#,
                )
            })
        })
        .transpose()
}

fn optional_bool(
    object: Option<&JsonObject>,
    key: &'static str,
) -> Result<Option<bool>, ConfigError> {
    object
        .and_then(|object| object.get(key))
        .map(|value| match value {
            JsonValue::Bool(b) => Ok(*b),

            JsonValue::String(s) => match s.trim().to_ascii_lowercase().as_str() {
                "true" => Ok(true),
                "false" => Ok(false),
                _ => Err(invalid_field(key, "a boolean")),
            },
            _ => Err(invalid_field(key, "a boolean")),
        })
        .transpose()
}

fn optional_path(
    root: &ProjectRoot,
    directory: &Path,
    object: Option<&JsonObject>,
    key: &'static str,
) -> Result<Option<PathBuf>, ConfigError> {
    object
        .and_then(|object| object.get(key))
        .map(|value| {
            let value = value
                .as_str()
                .ok_or_else(|| invalid_field(key, "a path string"))?;
            root.resolve_from(directory, value)
                .map_err(ConfigError::from)
        })
        .transpose()
}

fn string_list(object: &JsonObject, key: &'static str) -> Result<Arc<[Arc<str>]>, ConfigError> {
    let Some(value) = object.get(key) else {
        return Ok(Arc::from([]));
    };
    let values = value
        .as_array()
        .ok_or_else(|| invalid_field(key, "an array of strings"))?;
    values
        .iter()
        .map(|value| {
            value
                .as_str()
                .map(Arc::from)
                .ok_or_else(|| invalid_field(key, "an array of strings"))
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Arc::from)
}

/// Reads an output-target path option, accepting absolute and
/// root-escaping values (see [`ProjectRoot::resolve_output_from`]).
fn optional_output_path(
    root: &ProjectRoot,
    directory: &Path,
    object: Option<&JsonObject>,
    key: &'static str,
) -> Result<Option<PathBuf>, ConfigError> {
    object
        .and_then(|object| object.get(key))
        .map(|value| {
            let value = value
                .as_str()
                .ok_or_else(|| invalid_field(key, "a path string"))?;
            Ok(root.resolve_output_from(directory, value))
        })
        .transpose()
}

fn path_list(
    root: &ProjectRoot,
    directory: &Path,
    object: &JsonObject,
    key: &'static str,
) -> Result<Arc<[PathBuf]>, ConfigError> {
    let values = string_list(object, key)?;
    values
        .iter()
        .map(|value| {
            root.resolve_from(directory, value.as_ref())
                .map_err(ConfigError::from)
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Arc::from)
}

fn validate_patterns(
    root: &ProjectRoot,
    directory: &Path,
    field: &'static str,
    patterns: &[Arc<str>],
) -> Result<(), ConfigError> {
    for pattern in patterns {
        if pattern.is_empty() {
            return Err(invalid_field(field, "non-empty confined path patterns"));
        }
        root.resolve_from(directory, pattern.as_ref())?;
    }
    Ok(())
}

fn parse_path_mappings(
    root: &ProjectRoot,
    base_url: &Path,
    compiler: Option<&JsonObject>,
) -> Result<Arc<[PathMapping]>, ConfigError> {
    let Some(value) = compiler.and_then(|object| object.get("paths")) else {
        return Ok(Arc::from([]));
    };
    let object = value
        .as_object()
        .ok_or_else(|| invalid_field("paths", "an object of string arrays"))?;
    let mut mappings = Vec::with_capacity(object.entries().len());
    for (pattern, value) in object.entries() {
        if pattern.is_empty() || pattern.matches('*').count() > 1 {
            return Err(invalid_field(
                format!("paths.{pattern}"),
                "a non-empty pattern with at most one '*'",
            ));
        }
        let targets = value
            .as_array()
            .ok_or_else(|| invalid_field(format!("paths.{pattern}"), "an array of strings"))?;
        if targets.is_empty() {
            return Err(invalid_field(
                format!("paths.{pattern}"),
                "a non-empty array of strings",
            ));
        }
        let resolved = targets
            .iter()
            .map(|target| {
                let target = target.as_str().ok_or_else(|| {
                    invalid_field(format!("paths.{pattern}"), "an array of strings")
                })?;
                if target.matches('*').count() > 1 {
                    return Err(invalid_field(
                        format!("paths.{pattern}"),
                        "targets with at most one '*'",
                    ));
                }
                root.resolve_from(base_url, target)
                    .map_err(ConfigError::from)
            })
            .collect::<Result<Vec<_>, _>>()?;
        mappings.push(PathMapping {
            pattern: Arc::clone(pattern),
            targets: Arc::from(resolved),
        });
    }
    Ok(Arc::from(mappings))
}

/// File families to prioritize in a relative module search plan.
///
/// Ordered `Runtime` before `Types` so flavor-keyed structures can derive `Ord`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ResolutionFlavor {
    Runtime,
    Types,
}

/// A relative module planning failure. Planning is pure and never reports a missing
/// file; callers decide existence by applying their own probe to the candidates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModuleResolutionError {
    Path(PathError),
    EmptySpecifier,
    BareSpecifier { specifier: Arc<str> },
    UrlLikeSpecifier { specifier: Arc<str> },
    UnsupportedExtension { specifier: Arc<str> },
}

impl fmt::Display for ModuleResolutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Path(error) => error.fmt(formatter),
            Self::EmptySpecifier => formatter.write_str("module specifier is empty"),
            Self::BareSpecifier { specifier } => {
                write!(
                    formatter,
                    "{specifier:?} is not a relative module specifier"
                )
            }
            Self::UrlLikeSpecifier { specifier } => write!(
                formatter,
                "URL-like module specifier {specifier:?} cannot be resolved as a file"
            ),
            Self::UnsupportedExtension { specifier } => write!(
                formatter,
                "relative module specifier {specifier:?} has an unsupported extension"
            ),
        }
    }
}

impl std::error::Error for ModuleResolutionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        if let Self::Path(error) = self {
            Some(error)
        } else {
            None
        }
    }
}

impl From<PathError> for ModuleResolutionError {
    fn from(error: PathError) -> Self {
        Self::Path(error)
    }
}

/// An ordered, immutable set of candidate files for one relative import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolutionPlan {
    specifier: Arc<str>,
    candidates: Arc<[PathBuf]>,
}

impl ResolutionPlan {
    #[must_use]
    pub fn specifier(&self) -> &str {
        &self.specifier
    }

    #[must_use]
    pub fn candidates(&self) -> &[PathBuf] {
        &self.candidates
    }

    /// Returns the first candidate accepted by an injected existence policy.
    /// Planning itself deliberately does not perform file-system I/O.
    #[must_use]
    pub fn select(&self, mut exists: impl FnMut(&Path) -> bool) -> Option<&Path> {
        self.candidates
            .iter()
            .find(|candidate| exists(candidate))
            .map(PathBuf::as_path)
    }
}

/// Plans TypeScript/JavaScript extension substitution and directory-index search for
/// a relative import. The importer and every candidate must remain under `root`.
pub fn plan_relative_module(
    root: &ProjectRoot,
    importer: impl AsRef<Path>,
    specifier: &str,
    flavor: ResolutionFlavor,
    resolve_json_module: bool,
) -> Result<ResolutionPlan, ModuleResolutionError> {
    if specifier.is_empty() {
        return Err(ModuleResolutionError::EmptySpecifier);
    }
    if specifier.contains('?') || specifier.contains('#') || specifier.contains("//") {
        return Err(ModuleResolutionError::UrlLikeSpecifier {
            specifier: Arc::from(specifier),
        });
    }
    if !(specifier.starts_with("./") || specifier.starts_with("../")) {
        return Err(ModuleResolutionError::BareSpecifier {
            specifier: Arc::from(specifier),
        });
    }
    let importer = root.confine(importer)?;
    let directory = importer
        .parent()
        .ok_or_else(|| PathError::PathHasNoParent {
            path: importer.clone(),
        })?;
    let requested = root.resolve_from(directory, specifier)?;
    let mut candidates = Vec::new();
    append_file_candidates(
        &mut candidates,
        &requested,
        flavor,
        resolve_json_module,
        specifier,
    )?;
    if requested.extension().is_none() {
        let index = requested.join("index");
        append_extensionless_candidates(&mut candidates, &index, flavor, resolve_json_module);
    }
    Ok(ResolutionPlan {
        specifier: Arc::from(specifier),
        candidates: Arc::from(candidates),
    })
}

fn append_file_candidates(
    output: &mut Vec<PathBuf>,
    requested: &Path,
    flavor: ResolutionFlavor,
    resolve_json_module: bool,
    specifier: &str,
) -> Result<(), ModuleResolutionError> {
    let Some(extension) = requested.extension().and_then(|value| value.to_str()) else {
        append_unique(output, requested.to_path_buf());
        append_extensionless_candidates(output, requested, flavor, resolve_json_module);
        return Ok(());
    };
    let substitutions: &[&str] = match extension {
        "js" => &["ts", "tsx", "d.ts", "js"],
        "jsx" => &["tsx", "d.ts", "jsx"],
        "mjs" => &["mts", "d.mts", "mjs"],
        "cjs" => &["cts", "d.cts", "cjs"],
        "ts" | "tsx" | "mts" | "cts" => &[extension],
        // A `.json` specifier names an exact JSON file: TypeScript probes it
        // as-is and never substitutes other extensions after it, even when
        // `resolveJsonModule` is disabled (upstream resolves relative exact
        // `.json` imports without the flag). Whether `.json` joins the
        // *searched* extension list (extensionless stems, paths mappings) is
        // decided by the callers that own that policy.
        "json" => &[extension],
        _ => {
            return Err(ModuleResolutionError::UnsupportedExtension {
                specifier: Arc::from(specifier),
            });
        }
    };
    if flavor == ResolutionFlavor::Types {
        for extension in substitutions.iter().filter(|value| value.contains("d.")) {
            append_with_extension(output, requested, extension);
        }
    }
    for extension in substitutions {
        append_with_extension(output, requested, extension);
    }
    Ok(())
}

fn append_extensionless_candidates(
    output: &mut Vec<PathBuf>,
    stem: &Path,
    flavor: ResolutionFlavor,
    resolve_json_module: bool,
) {
    let runtime = ["ts", "tsx", "mts", "cts", "js", "jsx", "mjs", "cjs"];
    if flavor == ResolutionFlavor::Types {
        append_with_extension(output, stem, "d.ts");
        append_with_extension(output, stem, "d.mts");
        append_with_extension(output, stem, "d.cts");
    }
    for extension in runtime {
        append_with_extension(output, stem, extension);
    }
    if flavor == ResolutionFlavor::Runtime {
        append_with_extension(output, stem, "d.ts");
        append_with_extension(output, stem, "d.mts");
        append_with_extension(output, stem, "d.cts");
    }
    if resolve_json_module {
        append_with_extension(output, stem, "json");
    }
}

fn append_with_extension(output: &mut Vec<PathBuf>, path: &Path, extension: &str) {
    let mut candidate = path.to_path_buf();
    candidate.set_extension(extension);
    append_unique(output, candidate);
}

fn append_unique(output: &mut Vec<PathBuf>, candidate: PathBuf) {
    if !output.contains(&candidate) {
        output.push(candidate);
    }
}

/// The interpretation used for legacy package entry fields when `exports` is absent.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PackageMode {
    Import,
    Require,
    Types,
}

/// A package `imports` result may point to a confined project file or to another bare
/// package specifier. This layer plans only; it never downloads or executes a package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageTarget {
    Path(PathBuf),
    External(Arc<str>),
}

/// Package metadata or map resolution failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageError {
    Json(JsoncError),
    Path(PathError),
    RootMustBeObject,
    InvalidField {
        field: Arc<str>,
        expected: &'static str,
    },
    InvalidSubpath {
        subpath: Arc<str>,
    },
    InvalidImportSpecifier {
        specifier: Arc<str>,
    },
    InvalidCondition {
        condition: Arc<str>,
    },
    MixedExportsKeys,
    InvalidPattern {
        pattern: Arc<str>,
    },
    InvalidTarget {
        target: Arc<str>,
    },
    TargetEscapesPackage {
        target: Arc<str>,
    },
    TargetUsesNodeModules {
        target: Arc<str>,
    },
    SubpathNotExported {
        subpath: Arc<str>,
    },
    ImportNotDefined {
        specifier: Arc<str>,
    },
    TargetBlocked,
    NoLegacyEntry,
}

impl fmt::Display for PackageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Json(error) => error.fmt(formatter),
            Self::Path(error) => error.fmt(formatter),
            Self::RootMustBeObject => formatter.write_str("package.json root must be an object"),
            Self::InvalidField { field, expected } => {
                write!(formatter, "package.json field {field:?} must be {expected}")
            }
            Self::InvalidSubpath { subpath } => {
                write!(formatter, "invalid package export subpath {subpath:?}")
            }
            Self::InvalidImportSpecifier { specifier } => {
                write!(formatter, "invalid package import specifier {specifier:?}")
            }
            Self::InvalidCondition { condition } => {
                write!(formatter, "invalid package condition {condition:?}")
            }
            Self::MixedExportsKeys => formatter
                .write_str("package exports object cannot mix subpath keys and condition keys"),
            Self::InvalidPattern { pattern } => {
                write!(formatter, "invalid package map pattern {pattern:?}")
            }
            Self::InvalidTarget { target } => {
                write!(formatter, "invalid package target {target:?}")
            }
            Self::TargetEscapesPackage { target } => {
                write!(formatter, "package target {target:?} escapes its package")
            }
            Self::TargetUsesNodeModules { target } => write!(
                formatter,
                "package target {target:?} contains a forbidden node_modules segment"
            ),
            Self::SubpathNotExported { subpath } => {
                write!(formatter, "package subpath {subpath:?} is not exported")
            }
            Self::ImportNotDefined { specifier } => {
                write!(formatter, "package import {specifier:?} is not defined")
            }
            Self::TargetBlocked => formatter.write_str("package target is explicitly blocked"),
            Self::NoLegacyEntry => formatter.write_str("package has no matching legacy entry"),
        }
    }
}

impl std::error::Error for PackageError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Json(error) => Some(error),
            Self::Path(error) => Some(error),
            _ => None,
        }
    }
}

impl From<JsoncError> for PackageError {
    fn from(error: JsoncError) -> Self {
        Self::Json(error)
    }
}

impl From<PathError> for PackageError {
    fn from(error: PathError) -> Self {
        Self::Path(error)
    }
}

/// An immutable set of active package conditions. `default` is always eligible and
/// therefore need not be supplied explicitly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolutionConditions {
    values: Arc<[Arc<str>]>,
}

impl ResolutionConditions {
    pub fn new<I, S>(conditions: I) -> Result<Self, PackageError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut values: Vec<Arc<str>> = Vec::new();
        for condition in conditions {
            let condition = condition.as_ref();
            if condition.is_empty() || condition.starts_with('.') || condition.contains('/') {
                return Err(PackageError::InvalidCondition {
                    condition: Arc::from(condition),
                });
            }
            if !values.iter().any(|existing| existing.as_ref() == condition) {
                values.push(Arc::from(condition));
            }
        }
        Ok(Self {
            values: Arc::from(values),
        })
    }

    #[must_use]
    pub fn for_mode(mode: PackageMode) -> Self {
        let values: &[&str] = match mode {
            PackageMode::Import => &["import", "node"],
            PackageMode::Require => &["require", "node"],
            PackageMode::Types => &["types", "import", "node"],
        };
        Self {
            values: Arc::from(
                values
                    .iter()
                    .map(|value| Arc::from(*value))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    #[must_use]
    pub fn contains(&self, condition: &str) -> bool {
        condition == "default"
            || self
                .values
                .iter()
                .any(|candidate| candidate.as_ref() == condition)
    }

    #[must_use]
    pub fn values(&self) -> &[Arc<str>] {
        &self.values
    }
}

/// Immutable package.json metadata and pure export/import resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageJson {
    path: PathBuf,
    directory: PathBuf,
    name: Option<Arc<str>>,
    package_type: Option<Arc<str>>,
    main: Option<Arc<str>>,
    module: Option<Arc<str>>,
    types: Option<Arc<str>>,
    exports: Option<JsonValue>,
    imports: Option<JsonObject>,
    raw: JsonObject,
}

impl PackageJson {
    /// Parses already-loaded package metadata without scripts, network access, or I/O.
    pub fn parse(
        root: &ProjectRoot,
        package_path: impl AsRef<Path>,
        source: &str,
    ) -> Result<Self, PackageError> {
        let path = root.confine(package_path)?;
        let directory = path
            .parent()
            .ok_or_else(|| PathError::PathHasNoParent { path: path.clone() })?
            .to_path_buf();
        let value = parse_jsonc(source)?;
        let raw = value
            .as_object()
            .ok_or(PackageError::RootMustBeObject)?
            .clone();
        let imports = match raw.get("imports") {
            None => None,
            Some(value) => Some(
                value
                    .as_object()
                    .ok_or_else(|| package_invalid_field("imports", "an object"))?
                    .clone(),
            ),
        };
        let package_type = package_optional_string(&raw, "type")?;
        if let Some(value) = package_type.as_deref()
            && value != "module"
            && value != "commonjs"
        {
            return Err(package_invalid_field("type", "\"module\" or \"commonjs\""));
        }
        Ok(Self {
            path,
            directory,
            name: package_optional_string(&raw, "name")?,
            package_type,
            main: package_optional_string(&raw, "main")?,
            module: package_optional_string(&raw, "module")?,
            types: package_optional_string(&raw, "types")?
                .or(package_optional_string(&raw, "typings")?),
            exports: raw.get("exports").cloned(),
            imports,
            raw,
        })
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub fn directory(&self) -> &Path {
        &self.directory
    }

    #[must_use]
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    #[must_use]
    pub fn package_type(&self) -> Option<&str> {
        self.package_type.as_deref()
    }

    #[must_use]
    pub const fn raw(&self) -> &JsonObject {
        &self.raw
    }

    /// Resolves an export map target or a legacy root entry. Targets are planned
    /// lexically and need not exist.
    pub fn resolve_export(
        &self,
        root: &ProjectRoot,
        subpath: &str,
        mode: PackageMode,
        conditions: &ResolutionConditions,
    ) -> Result<PathBuf, PackageError> {
        validate_export_subpath(subpath)?;
        let Some(exports) = &self.exports else {
            if subpath != "." {
                return Err(PackageError::SubpathNotExported {
                    subpath: Arc::from(subpath),
                });
            }
            return self.resolve_legacy(root, mode);
        };
        let capture: Option<Arc<str>> = if let JsonValue::Object(object) = exports {
            let has_subpaths = object.entries().iter().any(|(key, _)| key.starts_with('.'));
            let has_conditions = object
                .entries()
                .iter()
                .any(|(key, _)| !key.starts_with('.'));
            if has_subpaths && has_conditions {
                return Err(PackageError::MixedExportsKeys);
            }
            if has_subpaths {
                let entry = select_map_entry(object, subpath)?.ok_or_else(|| {
                    PackageError::SubpathNotExported {
                        subpath: Arc::from(subpath),
                    }
                })?;
                return self.finish_export_target(
                    root,
                    resolve_package_target(entry.target, conditions, entry.capture.as_deref())?,
                );
            }
            None
        } else {
            None
        };
        if subpath != "." {
            return Err(PackageError::SubpathNotExported {
                subpath: Arc::from(subpath),
            });
        }
        self.finish_export_target(
            root,
            resolve_package_target(exports, conditions, capture.as_deref())?,
        )
    }

    /// Resolves a package-local `#imports` map. Bare results remain explicit external
    /// targets for a higher package locator; relative results are confined paths.
    pub fn resolve_import(
        &self,
        root: &ProjectRoot,
        specifier: &str,
        conditions: &ResolutionConditions,
    ) -> Result<PackageTarget, PackageError> {
        if !specifier.starts_with('#') || specifier == "#" || specifier.starts_with("#/") {
            return Err(PackageError::InvalidImportSpecifier {
                specifier: Arc::from(specifier),
            });
        }
        let imports = self
            .imports
            .as_ref()
            .ok_or_else(|| PackageError::ImportNotDefined {
                specifier: Arc::from(specifier),
            })?;
        let entry = select_map_entry(imports, specifier)?.ok_or_else(|| {
            PackageError::ImportNotDefined {
                specifier: Arc::from(specifier),
            }
        })?;
        match resolve_package_target(entry.target, conditions, entry.capture.as_deref())? {
            TargetOutcome::Path(target) => self
                .resolve_package_path(root, &target)
                .map(PackageTarget::Path),
            TargetOutcome::External(target) => Ok(PackageTarget::External(target)),
            TargetOutcome::Blocked => Err(PackageError::TargetBlocked),
            TargetOutcome::NoMatch => Err(PackageError::ImportNotDefined {
                specifier: Arc::from(specifier),
            }),
        }
    }

    fn resolve_legacy(
        &self,
        root: &ProjectRoot,
        mode: PackageMode,
    ) -> Result<PathBuf, PackageError> {
        let target = match mode {
            PackageMode::Types => self.types.as_deref(),
            PackageMode::Import => self.module.as_deref().or(self.main.as_deref()),
            PackageMode::Require => self.main.as_deref(),
        }
        .ok_or(PackageError::NoLegacyEntry)?;
        self.resolve_package_path(root, target)
    }

    fn finish_export_target(
        &self,
        root: &ProjectRoot,
        outcome: TargetOutcome,
    ) -> Result<PathBuf, PackageError> {
        match outcome {
            TargetOutcome::Path(target) => self.resolve_package_path(root, &target),
            TargetOutcome::External(target) => Err(PackageError::InvalidTarget { target }),
            TargetOutcome::Blocked => Err(PackageError::TargetBlocked),
            TargetOutcome::NoMatch => Err(PackageError::SubpathNotExported {
                subpath: Arc::from("."),
            }),
        }
    }

    fn resolve_package_path(
        &self,
        root: &ProjectRoot,
        target: &str,
    ) -> Result<PathBuf, PackageError> {
        // Export/import targets are pre-validated to start with `./`; legacy
        // main/module/types entries may be bare (`index.js`) or `./`-prefixed.
        let relative = target.strip_prefix("./").unwrap_or(target);
        if Path::new(relative)
            .components()
            .any(|component| component.as_os_str() == "node_modules")
        {
            return Err(PackageError::TargetUsesNodeModules {
                target: Arc::from(target),
            });
        }
        let resolved = root.resolve_from(&self.directory, relative)?;
        if !resolved.starts_with(&self.directory) {
            return Err(PackageError::TargetEscapesPackage {
                target: Arc::from(target),
            });
        }
        Ok(resolved)
    }
}

fn package_invalid_field(field: impl Into<Arc<str>>, expected: &'static str) -> PackageError {
    PackageError::InvalidField {
        field: field.into(),
        expected,
    }
}

fn package_optional_string(
    object: &JsonObject,
    key: &'static str,
) -> Result<Option<Arc<str>>, PackageError> {
    object
        .get(key)
        .map(|value| {
            value
                .as_str()
                .map(Arc::from)
                .ok_or_else(|| package_invalid_field(key, "a string"))
        })
        .transpose()
}

fn validate_export_subpath(subpath: &str) -> Result<(), PackageError> {
    if subpath == "."
        || (subpath.starts_with("./")
            && subpath.len() > 2
            && !subpath.contains('\\')
            && !subpath
                .split('/')
                .any(|part| part == ".." || part.is_empty()))
    {
        Ok(())
    } else {
        Err(PackageError::InvalidSubpath {
            subpath: Arc::from(subpath),
        })
    }
}

struct MapEntry<'a> {
    target: &'a JsonValue,
    capture: Option<Arc<str>>,
}

fn select_map_entry<'a>(
    object: &'a JsonObject,
    request: &str,
) -> Result<Option<MapEntry<'a>>, PackageError> {
    if let Some(value) = object.get(request) {
        return Ok(Some(MapEntry {
            target: value,
            capture: None,
        }));
    }
    let mut selected: Option<(&JsonValue, Arc<str>, usize)> = None;
    for (pattern, value) in object.entries() {
        let stars = pattern.matches('*').count();
        if stars == 0 {
            continue;
        }
        if stars != 1 {
            return Err(PackageError::InvalidPattern {
                pattern: Arc::clone(pattern),
            });
        }
        let (prefix, suffix) =
            pattern
                .split_once('*')
                .ok_or_else(|| PackageError::InvalidPattern {
                    pattern: Arc::clone(pattern),
                })?;
        let Some(remainder) = request.strip_prefix(prefix) else {
            continue;
        };
        let Some(capture) = remainder.strip_suffix(suffix) else {
            continue;
        };
        let specificity = prefix.len() + suffix.len();
        if selected
            .as_ref()
            .is_none_or(|(_, _, current)| specificity > *current)
        {
            selected = Some((value, Arc::from(capture), specificity));
        }
    }
    Ok(selected.map(|(value, capture, _)| MapEntry {
        target: value,
        capture: Some(capture),
    }))
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TargetOutcome {
    Path(Arc<str>),
    External(Arc<str>),
    Blocked,
    NoMatch,
}

fn resolve_package_target(
    value: &JsonValue,
    conditions: &ResolutionConditions,
    capture: Option<&str>,
) -> Result<TargetOutcome, PackageError> {
    match value {
        JsonValue::Null => Ok(TargetOutcome::Blocked),
        JsonValue::String(target) => {
            let target: Arc<str> = if let Some(capture) = capture {
                Arc::from(target.replace('*', capture))
            } else {
                Arc::clone(target)
            };
            if target.starts_with("./") {
                Ok(TargetOutcome::Path(target))
            } else if target.starts_with('/') || target.starts_with("../") {
                Err(PackageError::InvalidTarget { target })
            } else {
                Ok(TargetOutcome::External(target))
            }
        }
        JsonValue::Array(values) => {
            let mut blocked = false;
            for value in values.iter() {
                match resolve_package_target(value, conditions, capture)? {
                    TargetOutcome::NoMatch => {}
                    TargetOutcome::Blocked => blocked = true,
                    outcome => return Ok(outcome),
                }
            }
            Ok(if blocked {
                TargetOutcome::Blocked
            } else {
                TargetOutcome::NoMatch
            })
        }
        JsonValue::Object(object) => {
            for (condition, target) in object.entries() {
                if conditions.contains(condition) {
                    let outcome = resolve_package_target(target, conditions, capture)?;
                    if outcome != TargetOutcome::NoMatch {
                        return Ok(outcome);
                    }
                }
            }
            Ok(TargetOutcome::NoMatch)
        }
        JsonValue::Bool(_) | JsonValue::Number(_) => Err(package_invalid_field(
            "exports/imports target",
            "a string, object, array, or null",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ConfigError, JsonValue, JsoncErrorKind, LintTsConfig, ModuleResolutionError, PackageError,
        PackageJson, PackageMode, PackageTarget, ProjectConfig, ProjectRoot, ResolutionConditions,
        ResolutionFlavor, parse_bamts_toml, parse_jsonc, plan_relative_module,
    };
    use crate::source::JsxEmit;
    use std::path::{Path, PathBuf};

    fn root() -> ProjectRoot {
        ProjectRoot::new("/workspace/corpus").expect("absolute test root")
    }

    #[test]
    fn bamts_toml_reads_only_lint_groups_and_rules() {
        let config = parse_bamts_toml(
            r#"
                title = "ignored"
                [lints.groups]
                escape-hatches = "deny"
                [unrelated]
                setting = "ignored"
                [lints.rules]
                BAMTS-W017 = "forbid" # exact rule
            "#,
        )
        .expect("valid bamts.toml lint tables");
        assert_eq!(config.groups().len(), 1);
        assert_eq!(config.groups()[0].name(), "escape-hatches");
        assert_eq!(config.rules().len(), 1);
        assert_eq!(config.rules()[0].name(), "BAMTS-W017");
        assert_eq!(config.rules()[0].source(), "bamts.toml:8");
    }

    #[test]
    fn lint_tsconfig_ignores_typescript_strictness_options() {
        let config = LintTsConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "target": "ES2022",
                    "module": "NodeNext",
                    "moduleResolution": "NodeNext",
                    "paths": {"@app/*": ["src/*"]},
                    "strict": true,
                    "useDefineForClassFields": false
                }
            }"#,
        )
        .expect("supported tsconfig view");
        assert_eq!(config.target(), Some("ES2022"));
        assert_eq!(config.module(), Some("NodeNext"));
        assert_eq!(config.module_resolution(), Some("NodeNext"));
        assert_eq!(config.paths()[0].pattern(), "@app/*");
    }

    #[test]
    fn jsonc_accepts_tsconfig_comments_trailing_commas_and_surrogate_pairs() {
        let parsed = parse_jsonc(
            r#"{
                // TypeScript permits line comments.
                "compilerOptions": {
                    "module": "NodeNext", /* and block comments */
                    "types": ["node",],
                    "icon": "\uD83D\uDE80",
                },
            }"#,
        )
        .expect("valid JSONC");
        let compiler = parsed
            .as_object()
            .and_then(|object| object.get("compilerOptions"))
            .and_then(JsonValue::as_object)
            .expect("compiler options object");
        assert_eq!(compiler.get("icon").and_then(JsonValue::as_str), Some("🚀"));
        assert_eq!(
            compiler
                .get("types")
                .and_then(JsonValue::as_array)
                .map(<[JsonValue]>::len),
            Some(1)
        );
    }

    #[test]
    fn jsonc_duplicate_keys_are_last_wins_and_comments_have_offsets() {
        // TypeScript's tsconfig parser treats duplicate keys as last-wins.
        let parsed = parse_jsonc(r#"{"x": "1", "x": "2"}"#).expect("duplicate keys are accepted");
        let obj = parsed.as_object().expect("root object");
        assert_eq!(obj.get("x").and_then(JsonValue::as_str), Some("2"));
        // The surviving entry list contains no duplicate keys.
        assert_eq!(obj.entries().len(), 1);

        let comment = parse_jsonc("{/* never closed").expect_err("comment must terminate");
        assert_eq!(comment.offset(), 1);
        assert_eq!(comment.kind(), &JsoncErrorKind::UnterminatedBlockComment);
    }

    #[test]
    fn tsconfig_duplicate_compileroptions_keys_yield_last_value() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"strict": true, "strict": false}}"#,
        )
        .expect("duplicate keys are accepted");
        assert!(
            !config.options().strict(),
            "last value wins for duplicate compilerOptions keys"
        );
    }

    #[test]
    fn f12_duplicate_strict_and_declaration_pragmas_parse_last_wins() {
        // Simulates the tsconfig that build_tsconfig generates for cases like
        // contextuallyTypedBooleanLiterals.ts, which carry duplicate @strict
        // and @declaration pragmas. The harness emits one key per pragma
        // occurrence, so the JSONC parser must accept duplicate keys.
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"target": "es2015", "strict": true, "declaration": true, "strict": true, "declaration": true}}"#,
        )
        .expect("duplicate keys from duplicate pragmas must be accepted");
        assert!(config.options().strict(), "strict=true (last wins)");
    }

    #[test]
    fn jsonc_rejects_non_json_numbers_and_lone_surrogates() {
        assert_eq!(
            parse_jsonc("01").expect_err("leading zero").kind(),
            &JsoncErrorKind::InvalidNumber
        );
        assert_eq!(
            parse_jsonc(r#""\uD800""#)
                .expect_err("lone surrogate")
                .kind(),
            &JsoncErrorKind::LoneSurrogate
        );
    }

    #[test]
    fn root_normalization_is_lexical_and_rejects_escape() {
        let project = root();
        assert_eq!(
            project
                .resolve("projects/ohash/src/../src/index.ts")
                .expect("confined path"),
            PathBuf::from("/workspace/corpus/projects/ohash/src/index.ts")
        );
        assert!(project.resolve("../secrets.ts").is_err());
        assert!(ProjectRoot::new("relative/root").is_err());
    }

    #[test]
    fn project_config_parses_corpus_shaped_jsonc_into_immutable_options() {
        let config = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/projects/hookable/tsconfig.json",
            r##"{
                "compilerOptions": {
                    "target": "ESNext",
                    "module": "NodeNext",
                    "moduleResolution": "NodeNext",
                    "strict": true,
                    "resolveJsonModule": true,
                    "jsx": "react-jsx",
                    "jsxFactory": "h",
                    "jsxFragmentFactory": "Fragment",
                    "jsxImportSource": "@scope/runtime",
                    "baseUrl": ".",
                    "paths": { "#src/*": ["src/*"] },
                },
                "include": ["src", "test",],
            }"##,
        )
        .expect("corpus-shaped config");
        assert_eq!(config.options().module(), Some("NodeNext"));
        assert!(config.options().strict());
        // Upstream optionsStrictPropertyInitializationStrict.ts (sha256
        // 4c5f28823ac849778d69aed835f56cfff163dfb871c3d31496a0d0b46531c749)
        // combines the strict master switch with its property-initialization member.
        assert!(config.options().no_implicit_any());
        assert!(config.options().strict_null_checks());
        assert!(config.options().strict_property_initialization());
        assert!(config.options().always_strict());
        assert!(config.options().resolve_json_module());
        assert_eq!(config.options().jsx(), Some(JsxEmit::ReactJsx));
        assert_eq!(config.options().jsx_factory(), Some("h"));
        assert_eq!(config.options().jsx_fragment_factory(), Some("Fragment"));
        assert_eq!(config.options().jsx_import_source(), Some("@scope/runtime"));
        assert_eq!(
            config.options().base_url(),
            Path::new("/workspace/corpus/projects/hookable")
        );
        assert_eq!(
            config.options().paths()[0].targets()[0],
            PathBuf::from("/workspace/corpus/projects/hookable/src/*")
        );
        assert_eq!(config.include()[1].as_ref(), "test");
    }

    #[test]
    fn individual_strict_options_override_the_master_switch() {
        // TypeScript 7.0.2 showConfig baselines pin these canonical option names:
        // noImplicitAny (sha256 35227919724febab0410cf17ed4ad430a8638100981ddf20643746fff0a8e32a),
        // strictNullChecks (sha256 385f6fd5f0d8f183a0f56b4ae3f14399d4c982109ca1557152398d8650e43c64),
        // and strictPropertyInitialization (sha256
        // b3dadd75912e490756bd1c0165909cbdbb175e7ee223a57351c9061e2f242e9a).
        let config = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"strict":true,"noImplicitAny":false,"strictNullChecks":false,"strictPropertyInitialization":false,"alwaysStrict":false}}"#,
        )
        .expect("individual strict options");

        assert!(config.options().strict());
        assert!(!config.options().no_implicit_any());
        assert!(!config.options().strict_null_checks());
        assert!(!config.options().strict_property_initialization());
        assert!(!config.options().always_strict());
    }

    #[test]
    fn project_config_parses_use_define_for_class_fields_as_tri_state() {
        let pinned_true = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"useDefineForClassFields":true}}"#,
        )
        .expect("pinned true");
        assert_eq!(
            pinned_true.options().use_define_for_class_fields(),
            Some(true)
        );
        let pinned_false = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"useDefineForClassFields":false}}"#,
        )
        .expect("pinned false");
        assert_eq!(
            pinned_false.options().use_define_for_class_fields(),
            Some(false)
        );
        let silent = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"strict":true}}"#,
        )
        .expect("silent key");
        assert_eq!(silent.options().use_define_for_class_fields(), None);
    }

    #[test]
    fn project_config_parses_import_helpers_as_tri_state() {
        let pinned_true = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"importHelpers":true}}"#,
        )
        .expect("pinned true");
        assert_eq!(pinned_true.options().import_helpers(), Some(true));
        let pinned_false = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"importHelpers":false}}"#,
        )
        .expect("pinned false");
        assert_eq!(pinned_false.options().import_helpers(), Some(false));
        let silent = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"strict":true}}"#,
        )
        .expect("silent key");
        assert_eq!(silent.options().import_helpers(), None);
    }

    #[test]
    fn project_config_rejects_wrong_types_and_every_root_escape() {
        let wrong = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"strict":"yes"}}"#,
        )
        .expect_err("wrong type");
        assert!(matches!(wrong, ConfigError::InvalidField { .. }));

        let jsx = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"jsx":"invalid-mode"}}"#,
        )
        .expect_err("jsx values use the canonical closed set");
        assert!(matches!(
            jsx,
            ConfigError::InvalidField { field, .. } if field.as_ref() == "jsx"
        ));

        let escape = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"compilerOptions":{"outDir":"../outside"}}"#,
        )
        .expect_err("outDir escape");
        assert!(matches!(escape, ConfigError::Path(_)));

        let include_escape = ProjectConfig::parse(
            &root(),
            "/workspace/corpus/tsconfig.json",
            r#"{"include":["../outside/**/*.ts"]}"#,
        )
        .expect_err("include escape");
        assert!(matches!(include_escape, ConfigError::Path(_)));
    }

    #[test]
    fn relative_module_plan_covers_extension_substitution_and_index_without_io() {
        let project = root();
        let explicit = plan_relative_module(
            &project,
            "/workspace/corpus/cases/dot-prop.ts",
            "../projects/dot-prop/index.js",
            ResolutionFlavor::Runtime,
            false,
        )
        .expect("relative JS plan");
        assert_eq!(
            &explicit.candidates()[..4],
            &[
                PathBuf::from("/workspace/corpus/projects/dot-prop/index.ts"),
                PathBuf::from("/workspace/corpus/projects/dot-prop/index.tsx"),
                PathBuf::from("/workspace/corpus/projects/dot-prop/index.d.ts"),
                PathBuf::from("/workspace/corpus/projects/dot-prop/index.js"),
            ]
        );

        let directory = plan_relative_module(
            &project,
            "/workspace/corpus/cases/ohash.ts",
            "../projects/ohash/src/crypto/node",
            ResolutionFlavor::Runtime,
            false,
        )
        .expect("extension and index plan");
        assert!(directory.candidates().contains(&PathBuf::from(
            "/workspace/corpus/projects/ohash/src/crypto/node/index.ts"
        )));
        assert_eq!(
            directory.select(|path| path.ends_with("index.ts")),
            Some(Path::new(
                "/workspace/corpus/projects/ohash/src/crypto/node/index.ts"
            ))
        );
    }

    #[test]
    fn relative_module_plan_rejects_bare_url_unsupported_and_escaping_specifiers() {
        let project = root();
        let importer = "/workspace/corpus/cases/main.ts";
        assert!(matches!(
            plan_relative_module(
                &project,
                importer,
                "node:fs",
                ResolutionFlavor::Runtime,
                false
            ),
            Err(ModuleResolutionError::BareSpecifier { .. })
        ));
        assert!(matches!(
            plan_relative_module(
                &project,
                importer,
                "./x.ts?raw",
                ResolutionFlavor::Runtime,
                false
            ),
            Err(ModuleResolutionError::UrlLikeSpecifier { .. })
        ));
        assert!(
            plan_relative_module(
                &project,
                importer,
                "../../outside",
                ResolutionFlavor::Runtime,
                false
            )
            .is_err()
        );
    }

    #[test]
    fn package_exports_cover_corpus_string_conditional_subpath_and_wildcard_shapes() {
        let project = root();
        let flat = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/escape-string-regexp/package.json",
            r#"{"name":"escape-string-regexp","type":"module","exports":"./index.js"}"#,
        )
        .expect("flat corpus package");
        assert_eq!(
            flat.resolve_export(
                &project,
                ".",
                PackageMode::Import,
                &ResolutionConditions::for_mode(PackageMode::Import)
            )
            .expect("root export"),
            PathBuf::from("/workspace/corpus/projects/escape-string-regexp/index.js")
        );

        let nested = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/ohash/package.json",
            r#"{
                "name":"ohash",
                "exports": {
                    ".":"./dist/index.mjs",
                    "./crypto":{"node":"./dist/crypto/node/index.mjs","default":"./dist/crypto/js/index.mjs"},
                    "./*":"./src/*.ts"
                }
            }"#,
        )
        .expect("nested corpus package");
        assert_eq!(
            nested
                .resolve_export(
                    &project,
                    "./crypto",
                    PackageMode::Import,
                    &ResolutionConditions::for_mode(PackageMode::Import)
                )
                .expect("node condition"),
            PathBuf::from("/workspace/corpus/projects/ohash/dist/crypto/node/index.mjs")
        );
        assert_eq!(
            nested
                .resolve_export(
                    &project,
                    "./serialize",
                    PackageMode::Import,
                    &ResolutionConditions::for_mode(PackageMode::Import)
                )
                .expect("wildcard"),
            PathBuf::from("/workspace/corpus/projects/ohash/src/serialize.ts")
        );
    }

    #[test]
    fn package_conditions_preserve_declaration_precedence_and_types_branch() {
        let project = root();
        let package = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/defu/package.json",
            r#"{
                "exports": {
                    ".": {
                        "types": "./dist/defu.d.mts",
                        "import": {"default":"./dist/defu.mjs"},
                        "require":"./lib/defu.cjs"
                    }
                }
            }"#,
        )
        .expect("defu-shaped package");
        assert_eq!(
            package
                .resolve_export(
                    &project,
                    ".",
                    PackageMode::Types,
                    &ResolutionConditions::for_mode(PackageMode::Types)
                )
                .expect("types condition"),
            PathBuf::from("/workspace/corpus/projects/defu/dist/defu.d.mts")
        );
    }

    #[test]
    fn package_imports_return_confined_or_explicit_external_targets() {
        let project = root();
        let package = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/demo/package.json",
            r##"{
                "imports": {
                    "#internal/*": "./src/*.ts",
                    "#dependency": "dep/subpath"
                }
            }"##,
        )
        .expect("imports map");
        assert_eq!(
            package
                .resolve_import(
                    &project,
                    "#internal/value",
                    &ResolutionConditions::for_mode(PackageMode::Import)
                )
                .expect("local import"),
            PackageTarget::Path(PathBuf::from(
                "/workspace/corpus/projects/demo/src/value.ts"
            ))
        );
        assert_eq!(
            package
                .resolve_import(
                    &project,
                    "#dependency",
                    &ResolutionConditions::for_mode(PackageMode::Import)
                )
                .expect("external import"),
            PackageTarget::External("dep/subpath".into())
        );
    }

    #[test]
    fn package_targets_cannot_escape_or_reenter_node_modules() {
        let project = root();
        let escape = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/demo/package.json",
            r#"{"exports":"./../outside.js"}"#,
        )
        .expect("metadata parses");
        assert!(matches!(
            escape.resolve_export(
                &project,
                ".",
                PackageMode::Import,
                &ResolutionConditions::for_mode(PackageMode::Import)
            ),
            Err(PackageError::TargetEscapesPackage { .. })
        ));

        let node_modules = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/demo/package.json",
            r#"{"exports":"./node_modules/dep/index.js"}"#,
        )
        .expect("metadata parses");
        assert!(matches!(
            node_modules.resolve_export(
                &project,
                ".",
                PackageMode::Import,
                &ResolutionConditions::for_mode(PackageMode::Import)
            ),
            Err(PackageError::TargetUsesNodeModules { .. })
        ));
    }

    #[test]
    fn legacy_package_entries_are_mode_specific_and_need_not_exist() {
        let project = root();
        let package = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/tslib/package.json",
            r#"{
                "main":"./tslib.js",
                "module":"./tslib.es6.js",
                "typings":"./tslib.d.ts"
            }"#,
        )
        .expect("legacy corpus package");
        let conditions = ResolutionConditions::for_mode(PackageMode::Import);
        assert_eq!(
            package
                .resolve_export(&project, ".", PackageMode::Import, &conditions)
                .expect("module entry"),
            PathBuf::from("/workspace/corpus/projects/tslib/tslib.es6.js")
        );
        assert_eq!(
            package
                .resolve_export(&project, ".", PackageMode::Types, &conditions)
                .expect("types entry"),
            PathBuf::from("/workspace/corpus/projects/tslib/tslib.d.ts")
        );

        // mitt ships bare (no leading `./`) legacy fields across all three modes.
        let bare = PackageJson::parse(
            &project,
            "/workspace/corpus/projects/mitt/package.json",
            r#"{
                "main":"dist/mitt.js",
                "module":"dist/mitt.mjs",
                "typings":"index.d.ts"
            }"#,
        )
        .expect("bare legacy package");
        assert_eq!(
            bare.resolve_export(&project, ".", PackageMode::Require, &conditions)
                .expect("bare main entry"),
            PathBuf::from("/workspace/corpus/projects/mitt/dist/mitt.js")
        );
        assert_eq!(
            bare.resolve_export(&project, ".", PackageMode::Import, &conditions)
                .expect("bare module entry"),
            PathBuf::from("/workspace/corpus/projects/mitt/dist/mitt.mjs")
        );
        assert_eq!(
            bare.resolve_export(&project, ".", PackageMode::Types, &conditions)
                .expect("bare typings entry"),
            PathBuf::from("/workspace/corpus/projects/mitt/index.d.ts")
        );
    }

    // ── F13: tsconfig field validation accepts TypeScript-coerced forms ──

    #[test]
    fn f13_string_true_parses_as_boolean_true() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"incremental": "true"}}"#,
        )
        .expect("string \"true\" must coerce to boolean");
        assert!(config.options().incremental());
    }

    #[test]
    fn f13_string_false_parses_as_boolean_false() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"incremental": "false"}}"#,
        )
        .expect("string \"false\" must coerce to boolean");
        assert!(!config.options().incremental());
    }

    #[test]
    fn f13_string_true_case_insensitive_parses_as_boolean_true() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"composite": "True"}}"#,
        )
        .expect("string \"True\" must coerce to boolean");
        assert!(config.options().composite());
    }

    #[test]
    fn f13_string_true_with_whitespace_parses_as_boolean_true() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"incremental": " true "}}"#,
        )
        .expect("string \" true \" must coerce to boolean");
        assert!(config.options().incremental());
    }

    #[test]
    fn f13_string_composite_true_parses_as_boolean_true() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"composite": "true"}}"#,
        )
        .expect("string \"true\" must coerce to boolean for composite");
        assert!(config.options().composite());
    }

    #[test]
    fn f13_invalid_string_still_rejected_for_boolean_field() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let error = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"incremental": "yes"}}"#,
        )
        .expect_err("non-boolean string must be rejected");
        assert!(matches!(
            error,
            ConfigError::InvalidField { ref field, .. } if field.as_ref() == "incremental"
        ));
    }

    #[test]
    fn f13_number_still_rejected_for_boolean_field() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let error = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"incremental": 1}}"#,
        )
        .expect_err("number must be rejected for boolean field");
        assert!(matches!(
            error,
            ConfigError::InvalidField { ref field, .. } if field.as_ref() == "incremental"
        ));
    }

    #[test]
    fn f13_jsx_preserve_capital_parses_case_insensitively() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "Preserve"}}"#,
        )
        .expect("capitalized jsx value must be accepted");
        assert_eq!(config.options().jsx(), Some(JsxEmit::Preserve));
    }

    #[test]
    fn f13_jsx_react_uppercase_parses_case_insensitively() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "REACT"}}"#,
        )
        .expect("uppercase jsx value must be accepted");
        assert_eq!(config.options().jsx(), Some(JsxEmit::React));
    }

    #[test]
    fn f13_jsx_react_native_mixed_case_parses_case_insensitively() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "React-Native"}}"#,
        )
        .expect("mixed-case jsx value must be accepted");
        assert_eq!(config.options().jsx(), Some(JsxEmit::ReactNative));
    }

    #[test]
    fn f13_jsx_react_jsx_mixed_case_parses_case_insensitively() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "React-JSX"}}"#,
        )
        .expect("mixed-case jsx value must be accepted");
        assert_eq!(config.options().jsx(), Some(JsxEmit::ReactJsx));
    }

    #[test]
    fn f13_jsx_react_jsxdev_mixed_case_parses_case_insensitively() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "React-JSXDev"}}"#,
        )
        .expect("mixed-case jsx value must be accepted");
        assert_eq!(config.options().jsx(), Some(JsxEmit::ReactJsxDev));
    }

    #[test]
    fn f13_jsx_with_whitespace_parses_case_insensitively() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let config = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "  Preserve  "}}"#,
        )
        .expect("whitespace-padded jsx value must be accepted");
        assert_eq!(config.options().jsx(), Some(JsxEmit::Preserve));
    }

    #[test]
    fn f13_jsx_invalid_string_still_rejected() {
        let root = ProjectRoot::new("/workspace").expect("valid root");
        let error = ProjectConfig::parse(
            &root,
            "/workspace/tsconfig.json",
            r#"{"compilerOptions": {"jsx": "react-jsx-foo"}}"#,
        )
        .expect_err("invalid jsx value must be rejected");
        assert!(matches!(
            error,
            ConfigError::InvalidField { ref field, .. } if field.as_ref() == "jsx"
        ));
    }
}
