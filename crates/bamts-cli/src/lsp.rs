//! Stdio LSP 3.17 adapter over [`bamts_compiler::service::ServiceState`].
//!
//! Checking stays in the compiler service. This module frames JSON-RPC,
//! maps document sync onto open/update/close, and forwards queries.

use std::{
    collections::{BTreeMap, BTreeSet},
    io::{self, BufRead, Read, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bamts_compiler::checker::SymbolKind;
use bamts_compiler::diagnostic::DiagnosticSeverity;
use bamts_compiler::service::{
    DiagnosticEntry, DocumentSnapshot, Location, ServiceError, ServiceState,
    filesystem::{FileSystemError, OsFileSystem},
};
use bamts_compiler::source::{SourceText, TextRange, Utf16Pos};
use serde_json::{Value, json};

const MAX_MESSAGE_BYTES: usize = 16 * 1024 * 1024;
const MAX_HEADER_BYTES: usize = 8 * 1024;
const REQUEST_CANCELLED: i32 = -32800;

/// How the stdio loop finished.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Exit {
    /// Client sent `shutdown` then `exit`.
    Shutdown,
    /// Client sent `exit` without `shutdown`, or the stream ended uncleanly.
    Unrequested,
}

/// Runs one LSP session on `input`/`output` confined to `root`.
pub fn run(input: impl BufRead, output: impl Write, root: impl AsRef<Path>) -> io::Result<Exit> {
    let mut session = Session::new(root.as_ref())?;
    session.serve(input, output)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Lifecycle {
    AwaitingInitialize,
    AwaitingInitialized,
    Running,
    ShutdownRequested,
    Exited(Exit),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum RequestId {
    Null,
    Signed(i64),
    Unsigned(u64),
    String(String),
}

impl RequestId {
    fn parse(value: &Value) -> Option<Self> {
        match value {
            Value::Null => Some(Self::Null),
            Value::String(value) => Some(Self::String(value.clone())),
            Value::Number(value) => value
                .as_i64()
                .map(Self::Signed)
                .or_else(|| value.as_u64().map(Self::Unsigned)),
            _ => None,
        }
    }

    fn value(&self) -> Value {
        match self {
            Self::Null => Value::Null,
            Self::Signed(value) => json!(value),
            Self::Unsigned(value) => json!(value),
            Self::String(value) => json!(value),
        }
    }
}

struct Incoming {
    id: Option<RequestId>,
    method: String,
    params: Value,
}

struct Session {
    state: ServiceState<OsFileSystem>,
    snapshots: BTreeMap<PathBuf, Arc<DocumentSnapshot>>,
    process_root: PathBuf,
    workspace_root: PathBuf,
    lifecycle: Lifecycle,
    cancelled: BTreeSet<RequestId>,
    current_request: Option<RequestId>,
}

impl Session {
    fn new(root: &Path) -> io::Result<Self> {
        let process_root = root.canonicalize()?;
        let filesystem = OsFileSystem::new(&process_root).map_err(fs_io)?;
        Ok(Self {
            state: ServiceState::new(filesystem),
            snapshots: BTreeMap::new(),
            workspace_root: process_root.clone(),
            process_root,
            lifecycle: Lifecycle::AwaitingInitialize,
            cancelled: BTreeSet::new(),
            current_request: None,
        })
    }

    fn serve(&mut self, mut input: impl BufRead, mut output: impl Write) -> io::Result<Exit> {
        loop {
            let Some(raw) = read_message(&mut input)? else {
                return Ok(match self.lifecycle {
                    Lifecycle::Exited(exit) => exit,
                    Lifecycle::ShutdownRequested => Exit::Shutdown,
                    Lifecycle::AwaitingInitialize
                    | Lifecycle::AwaitingInitialized
                    | Lifecycle::Running => Exit::Unrequested,
                });
            };
            let parsed: Value = match serde_json::from_slice(&raw) {
                Ok(value) => value,
                Err(_) => {
                    write_json(
                        &mut output,
                        &error_response(Value::Null, -32700, "Parse error"),
                    )?;
                    continue;
                }
            };
            let responses = match validate_message(&parsed) {
                Ok(message) => self.dispatch(message),
                Err(response) => Some(vec![response]),
            };
            if let Some(responses) = responses {
                for response in responses {
                    write_json(&mut output, &response)?;
                }
            }
            if let Lifecycle::Exited(exit) = self.lifecycle {
                return Ok(exit);
            }
        }
    }

    fn dispatch(&mut self, message: Incoming) -> Option<Vec<Value>> {
        if message.method == "exit" {
            return self.exit(message.id, &message.params);
        }
        if message.method == "$/cancelRequest" {
            return self.cancel(message.id, &message.params);
        }

        match message.id {
            Some(id) => Some(vec![self.dispatch_request(
                id,
                &message.method,
                &message.params,
            )]),
            None => self.dispatch_notification(&message.method, &message.params),
        }
    }

    fn dispatch_request(&mut self, id: RequestId, method: &str, params: &Value) -> Value {
        if self.cancelled.remove(&id) {
            return error_response(id.value(), REQUEST_CANCELLED, "Request cancelled");
        }
        if matches!(
            method,
            "initialized"
                | "textDocument/didOpen"
                | "textDocument/didChange"
                | "textDocument/didClose"
                | "textDocument/didSave"
        ) {
            return error_response(id.value(), -32600, "LSP notification sent as a request");
        }
        self.current_request = Some(id.clone());
        let response = match self.lifecycle {
            Lifecycle::AwaitingInitialize => {
                if method == "initialize" {
                    self.initialize(id.value(), params)
                } else {
                    error_response(id.value(), -32002, "Server not initialized")
                }
            }
            Lifecycle::AwaitingInitialized => {
                if method == "initialize" {
                    error_response(id.value(), -32600, "Initialize request already received")
                } else {
                    error_response(id.value(), -32002, "Server not initialized")
                }
            }
            Lifecycle::Running => match method {
                "initialize" => {
                    error_response(id.value(), -32600, "Initialize request already received")
                }
                "shutdown" => {
                    self.lifecycle = Lifecycle::ShutdownRequested;
                    json!({ "jsonrpc": "2.0", "id": id.value(), "result": Value::Null })
                }
                "textDocument/completion" => self.completion(id.value(), params),
                "textDocument/definition" => self.definition(id.value(), params),
                "textDocument/hover" => self.hover(id.value(), params),
                "textDocument/references" => self.references(id.value(), params),
                "textDocument/rename" => self.rename(id.value(), params),
                _ => error_response(id.value(), -32601, "Method not found"),
            },
            Lifecycle::ShutdownRequested | Lifecycle::Exited(_) => {
                error_response(id.value(), -32600, "Server has shut down")
            }
        };
        self.current_request = None;
        if self.cancelled.remove(&id) {
            error_response(id.value(), REQUEST_CANCELLED, "Request cancelled")
        } else {
            response
        }
    }

    fn dispatch_notification(&mut self, method: &str, params: &Value) -> Option<Vec<Value>> {
        match self.lifecycle {
            Lifecycle::AwaitingInitialize => None,
            Lifecycle::AwaitingInitialized => {
                if method == "initialized" {
                    self.lifecycle = Lifecycle::Running;
                    None
                } else {
                    None
                }
            }
            Lifecycle::Running => match method {
                "textDocument/didOpen" => self.did_open(params),
                "textDocument/didChange" => self.did_change(params),
                "textDocument/didClose" => self.did_close(params),
                "textDocument/didSave" => None,
                "initialize" | "shutdown" => Some(vec![invalid_params_notification(format!(
                    "{method} must be sent as a request"
                ))]),
                // LSP 3.17: servers must ignore notifications they do not understand.
                _ => None,
            },
            Lifecycle::ShutdownRequested | Lifecycle::Exited(_) => None,
        }
    }

    fn initialize(&mut self, id: Value, params: &Value) -> Value {
        let root = match initialize_root(params, &self.process_root) {
            Ok(root) => root,
            Err(message) => return error_response(id, -32602, &message),
        };
        let filesystem = match OsFileSystem::new(&root) {
            Ok(filesystem) => filesystem,
            Err(error) => return error_response(id, -32603, &error.to_string()),
        };
        self.workspace_root = root.clone();
        self.state = ServiceState::new(filesystem);
        self.state.set_resolution_root(root);
        self.snapshots.clear();
        self.lifecycle = Lifecycle::AwaitingInitialized;
        json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": {
                "capabilities": {
                    "positionEncoding": "utf-16",
                    "textDocumentSync": { "openClose": true, "change": 1 },
                    "completionProvider": { "triggerCharacters": ["."] },
                    "definitionProvider": true,
                    "hoverProvider": true,
                    "referencesProvider": true,
                    "renameProvider": true
                },
                "serverInfo": { "name": "bamts-lsp", "version": "0.2.0" }
            }
        })
    }

    fn exit(&mut self, id: Option<RequestId>, params: &Value) -> Option<Vec<Value>> {
        if let Some(id) = id {
            return Some(vec![error_response(
                id.value(),
                -32600,
                "exit must be a notification",
            )]);
        }
        if !params.is_null() {
            return Some(vec![invalid_params_notification(
                "exit does not accept params".to_owned(),
            )]);
        }
        let exit = if self.lifecycle == Lifecycle::ShutdownRequested {
            Exit::Shutdown
        } else {
            Exit::Unrequested
        };
        self.lifecycle = Lifecycle::Exited(exit);
        None
    }

    fn cancel(&mut self, id: Option<RequestId>, params: &Value) -> Option<Vec<Value>> {
        if let Some(id) = id {
            return Some(vec![error_response(
                id.value(),
                -32600,
                "$/cancelRequest must be a notification",
            )]);
        }
        let Some(value) = params.get("id") else {
            return Some(vec![invalid_params_notification(
                "$/cancelRequest requires an id".to_owned(),
            )]);
        };
        let Some(cancelled) = RequestId::parse(value) else {
            return Some(vec![invalid_params_notification(
                "$/cancelRequest id must be a string or integer".to_owned(),
            )]);
        };
        if self.current_request.as_ref() == Some(&cancelled) || self.current_request.is_none() {
            self.cancelled.insert(cancelled);
        }
        None
    }

    fn document_path(&self, uri: &str) -> Result<PathBuf, String> {
        let path = uri_to_path(uri)?;
        canonicalize_confined(&path, &self.workspace_root)
    }

    fn did_open(&mut self, params: &Value) -> Option<Vec<Value>> {
        let Some(doc) = params.get("textDocument") else {
            return Some(vec![invalid_params_notification(
                "didOpen requires textDocument".to_owned(),
            )]);
        };
        let (Some(uri), Some(text)) = (
            doc.get("uri").and_then(Value::as_str),
            doc.get("text").and_then(Value::as_str),
        ) else {
            return Some(vec![invalid_params_notification(
                "didOpen requires uri and text".to_owned(),
            )]);
        };
        let Some(version) = doc.get("version").and_then(Value::as_u64) else {
            return Some(vec![invalid_params_notification(
                "didOpen requires an integer version".to_owned(),
            )]);
        };
        let path = match self.document_path(uri) {
            Ok(path) => path,
            Err(message) => return Some(vec![invalid_params_notification(message)]),
        };
        match self.state.open(&path, text, version) {
            Ok(snapshot) => {
                self.snapshots
                    .insert(snapshot.path().to_path_buf(), snapshot);
                Some(vec![self.publish_diagnostics(&path)])
            }
            Err(error) => Some(vec![show_message(&error)]),
        }
    }

    fn did_change(&mut self, params: &Value) -> Option<Vec<Value>> {
        let Some(doc) = params.get("textDocument") else {
            return Some(vec![invalid_params_notification(
                "didChange requires textDocument".to_owned(),
            )]);
        };
        let (Some(uri), Some(version)) = (
            doc.get("uri").and_then(Value::as_str),
            doc.get("version").and_then(Value::as_u64),
        ) else {
            return Some(vec![invalid_params_notification(
                "didChange requires uri and version".to_owned(),
            )]);
        };
        let Some(changes) = params.get("contentChanges").and_then(Value::as_array) else {
            return Some(vec![invalid_params_notification(
                "didChange requires contentChanges".to_owned(),
            )]);
        };
        if changes.len() != 1 {
            return Some(vec![invalid_params_notification(
                "full-sync didChange requires exactly one content change".to_owned(),
            )]);
        }
        let change = &changes[0];
        if change.get("range").is_some() || change.get("rangeLength").is_some() {
            return Some(vec![invalid_params_notification(
                "ranged document changes are not supported".to_owned(),
            )]);
        }
        let Some(text) = change.get("text").and_then(Value::as_str) else {
            return Some(vec![invalid_params_notification(
                "content change requires text".to_owned(),
            )]);
        };
        let path = match self.document_path(uri) {
            Ok(path) => path,
            Err(message) => return Some(vec![invalid_params_notification(message)]),
        };
        match self.state.update(&path, text, version) {
            Ok(snapshot) => {
                self.snapshots
                    .insert(snapshot.path().to_path_buf(), snapshot);
                Some(vec![self.publish_diagnostics(&path)])
            }
            Err(error) => {
                // Republish the last good set so the editor and the server
                // stay coherent instead of silently diverging on a failed
                // recomputation.
                let mut notifications = vec![show_message(&error)];
                if self.snapshots.contains_key(&path) {
                    notifications.push(self.publish_diagnostics(&path));
                }
                Some(notifications)
            }
        }
    }

    fn did_close(&mut self, params: &Value) -> Option<Vec<Value>> {
        let Some(uri) = params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(Value::as_str)
        else {
            return Some(vec![invalid_params_notification(
                "didClose requires a uri".to_owned(),
            )]);
        };
        let path = match self.document_path(uri) {
            Ok(path) => path,
            Err(message) => return Some(vec![invalid_params_notification(message)]),
        };
        let canonical_uri = path_to_uri(&path);
        match self.state.close(&path) {
            Ok(()) => {
                self.snapshots.remove(&path);
                Some(vec![json!({
                    "jsonrpc": "2.0",
                    "method": "textDocument/publishDiagnostics",
                    "params": { "uri": canonical_uri, "diagnostics": [] }
                })])
            }
            // A failed close leaves the document open server-side, so the
            // published set must not be cleared while state disagrees.
            Err(error) => Some(vec![show_message(&error)]),
        }
    }
    fn publish_diagnostics(&mut self, path: &Path) -> Value {
        let uri = path_to_uri(path);
        let entries = match self.state.diagnostics(path) {
            Ok(entries) => entries,
            Err(_) => self
                .snapshots
                .get(path)
                .map(|snapshot| {
                    snapshot
                        .diagnostics()
                        .iter()
                        .map(|diagnostic| DiagnosticEntry {
                            path: snapshot.path().to_path_buf(),
                            range: diagnostic.range(),
                            code: diagnostic.code().as_str(),
                            severity: diagnostic.severity(),
                            message: diagnostic.message().to_owned(),
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default(),
        };
        let diagnostics = entries
            .iter()
            .filter_map(|entry| self.lsp_diagnostic(entry))
            .collect::<Vec<_>>();
        json!({
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": { "uri": uri, "diagnostics": diagnostics }
        })
    }

    fn lsp_diagnostic(&self, entry: &DiagnosticEntry) -> Option<Value> {
        let snapshot = self.snapshots.get(&entry.path)?;
        let range = lsp_range(snapshot.source().source_text(), entry.range)?;
        let severity = match entry.severity {
            DiagnosticSeverity::Error => 1,
            DiagnosticSeverity::Warning => 2,
        };
        Some(json!({
            "range": range,
            "severity": severity,
            "code": entry.code,
            "source": "bamts",
            "message": entry.message
        }))
    }

    fn completion(&mut self, id: Value, params: &Value) -> Value {
        let Some((path, position)) = self.doc_position(params) else {
            return error_response(id, -32602, "Invalid params");
        };
        match self.state.completions(&path, position) {
            Ok(items) => {
                let snapshot = self.snapshots.get(&path);
                let result: Vec<Value> = items
                    .into_iter()
                    .map(|item| {
                        let mut value = json!({
                            "label": item.name,
                            "kind": completion_kind(item.kind)
                        });
                        if let Some(snapshot) = snapshot
                            && let Some(range) =
                                lsp_range(snapshot.source().source_text(), item.replacement)
                        {
                            value["textEdit"] = json!({
                                "range": range,
                                "newText": item.name
                            });
                        }
                        value
                    })
                    .collect();
                json!({ "jsonrpc": "2.0", "id": id, "result": result })
            }
            Err(error) => error_response(id, -32603, &error.to_string()),
        }
    }

    fn definition(&mut self, id: Value, params: &Value) -> Value {
        let Some((path, position)) = self.doc_position(params) else {
            return error_response(id, -32602, "Invalid params");
        };
        match self.state.definition(&path, position) {
            Ok(Some(location)) => json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": self.lsp_location(&location)
            }),
            Ok(None) => json!({ "jsonrpc": "2.0", "id": id, "result": Value::Null }),
            Err(error) => error_response(id, -32603, &error.to_string()),
        }
    }

    fn hover(&mut self, id: Value, params: &Value) -> Value {
        let Some((path, position)) = self.doc_position(params) else {
            return error_response(id, -32602, "Invalid params");
        };
        match self.state.quick_info(&path, position) {
            Ok(Some(info)) => {
                let mut result = json!({
                    "contents": { "kind": "plaintext", "value": info.display() }
                });
                if let Some(snapshot) = self.snapshots.get(&path)
                    && let Some(range) = lsp_range(snapshot.source().source_text(), info.range)
                {
                    result["range"] = range;
                }
                json!({ "jsonrpc": "2.0", "id": id, "result": result })
            }
            Ok(None) => json!({ "jsonrpc": "2.0", "id": id, "result": Value::Null }),
            Err(error) => error_response(id, -32603, &error.to_string()),
        }
    }

    fn references(&mut self, id: Value, params: &Value) -> Value {
        let Some((path, position)) = self.doc_position(params) else {
            return error_response(id, -32602, "Invalid params");
        };
        let include_declaration = params
            .get("context")
            .and_then(|context| context.get("includeDeclaration"))
            .and_then(Value::as_bool)
            .unwrap_or(true);
        match self.state.references(&path, position) {
            Ok(mut locations) => {
                if !include_declaration {
                    locations.retain(|location| !location.is_declaration);
                }
                let result: Vec<Value> = locations
                    .iter()
                    .filter_map(|location| self.lsp_location(location))
                    .collect();
                json!({ "jsonrpc": "2.0", "id": id, "result": result })
            }
            Err(error) => error_response(id, -32603, &error.to_string()),
        }
    }

    fn rename(&mut self, id: Value, params: &Value) -> Value {
        let Some((path, position)) = self.doc_position(params) else {
            return error_response(id, -32602, "Invalid params");
        };
        let Some(new_name) = params.get("newName").and_then(Value::as_str) else {
            return error_response(id, -32602, "Invalid params");
        };
        match self.state.rename(&path, position, new_name) {
            Ok(result) => {
                let mut changes = serde_json::Map::new();
                for edit in result.edit.edits {
                    let Some(snapshot) = self.snapshots.get(&edit.path) else {
                        continue;
                    };
                    let Some(range) = lsp_range(snapshot.source().source_text(), edit.range) else {
                        continue;
                    };
                    let uri = path_to_uri(&edit.path);
                    changes
                        .entry(uri)
                        .or_insert_with(|| json!([]))
                        .as_array_mut()
                        .expect("changes values are arrays")
                        .push(json!({ "range": range, "newText": edit.replacement }));
                }
                json!({
                    "jsonrpc": "2.0",
                    "id": id,
                    "result": { "changes": changes }
                })
            }
            // Unavailability is a null result per the rename contract:
            // clients gray out the affordance rather than raise an error.
            Err(ServiceError::RenameUnavailable) => {
                json!({ "jsonrpc": "2.0", "id": id, "result": null })
            }
            Err(error) => error_response(id, -32603, &error.to_string()),
        }
    }

    fn lsp_location(&self, location: &Location) -> Option<Value> {
        let snapshot = self.snapshots.get(&location.path)?;
        let range = lsp_range(snapshot.source().source_text(), location.range)?;
        Some(json!({
            "uri": path_to_uri(&location.path),
            "range": range
        }))
    }

    fn doc_position(&self, params: &Value) -> Option<(PathBuf, Utf16Pos)> {
        let uri = params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(Value::as_str)?;
        let position = params.get("position")?;
        let path = self.document_path(uri).ok()?;
        let line = u32::try_from(position.get("line").and_then(Value::as_u64)?).ok()?;
        let character = u32::try_from(position.get("character").and_then(Value::as_u64)?).ok()?;
        let snapshot = self.snapshots.get(&path)?;
        let position = lsp_position(snapshot.source().source_text().as_str(), line, character)?;
        Some((path.clone(), position))
    }
}

fn lsp_range(source: &SourceText, range: TextRange) -> Option<Value> {
    let (start_line, start_character) = source.line_column(range.start()).ok()?;
    let (end_line, end_character) = source.line_column(range.end()).ok()?;
    Some(json!({
        "start": { "line": start_line, "character": start_character },
        "end": { "line": end_line, "character": end_character }
    }))
}

fn lsp_position(source: &str, line: u32, character: u32) -> Option<Utf16Pos> {
    let requested_line = usize::try_from(line).ok()?;
    let requested_character = usize::try_from(character).ok()?;
    let mut current_line = 0usize;
    let mut current_character = 0usize;
    let mut utf16 = 0usize;
    let mut chars = source.chars().peekable();

    loop {
        let Some(ch) = chars.next() else {
            return (current_line == requested_line).then_some(Utf16Pos::new(utf16));
        };
        let ends_line = matches!(ch, '\r' | '\n' | '\u{2028}' | '\u{2029}');
        if current_line == requested_line && ends_line {
            return Some(Utf16Pos::new(utf16));
        }
        if ends_line {
            let width = if ch == '\r' && chars.peek() == Some(&'\n') {
                chars.next();
                2
            } else {
                1
            };
            utf16 += width;
            current_line += 1;
            current_character = 0;
            continue;
        }

        let width = ch.len_utf16();
        if current_line == requested_line {
            if current_character == requested_character {
                return Some(Utf16Pos::new(utf16));
            }
            if current_character < requested_character
                && requested_character < current_character + width
            {
                return None;
            }
            current_character += width;
        }
        utf16 += width;
    }
}

fn completion_kind(kind: SymbolKind) -> u32 {
    match kind {
        SymbolKind::Variable(_) => 6,
        _ => 6,
    }
}

fn uri_to_path(uri: &str) -> Result<PathBuf, String> {
    let rest = uri
        .strip_prefix("file://")
        .ok_or_else(|| format!("unsupported URI scheme: {uri}"))?;
    // RFC 8089: only the empty authority and `localhost` denote this
    // machine. Any other authority is a remote file; treating it as a
    // relative path would read and write under the server's working
    // directory instead.
    let path = match rest.split_once('/') {
        Some(("", path)) => path,
        Some(("localhost", path)) => path,
        Some((authority, _)) => {
            return Err(format!("nonlocal file URI authority: {authority}"));
        }
        None => return Err("file URI has no path".to_owned()),
    };
    let decoded = percent_decode(&format!("/{path}"))?;
    Ok(PathBuf::from(decoded))
}

fn path_to_uri(path: &Path) -> String {
    let display = path.to_string_lossy();
    let mut encoded = String::from("file://");
    for ch in display.chars() {
        match ch {
            'A'..='Z' | 'a'..='z' | '0'..='9' | '/' | '_' | '-' | '.' | '~' => encoded.push(ch),
            _ => {
                for byte in ch.encode_utf8(&mut [0; 4]).bytes() {
                    encoded.push_str(&format!("%{byte:02X}"));
                }
            }
        }
    }
    encoded
}

fn percent_decode(input: &str) -> Result<String, String> {
    let mut output = Vec::new();
    let bytes = input.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'%' => {
                let hex = bytes
                    .get(index + 1..index + 3)
                    .ok_or_else(|| "truncated percent-encoding".to_owned())?;
                let text =
                    std::str::from_utf8(hex).map_err(|_| "invalid percent-encoding".to_owned())?;
                let value = u8::from_str_radix(text, 16)
                    .map_err(|_| "invalid percent-encoding".to_owned())?;
                output.push(value);
                index += 3;
            }
            byte => {
                output.push(byte);
                index += 1;
            }
        }
    }
    String::from_utf8(output).map_err(|_| "URI path is not UTF-8".to_owned())
}

fn read_message(input: &mut impl BufRead) -> io::Result<Option<Vec<u8>>> {
    let mut content_length = None;
    let mut header_bytes = 0;
    loop {
        let mut header = String::new();
        // Bound the read itself so a peer cannot grow an unterminated line.
        let remaining = (MAX_HEADER_BYTES - header_bytes + 1) as u64;
        let read = input.take(remaining).read_line(&mut header)?;
        if read == 0 {
            return if header_bytes == 0 {
                Ok(None)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "stream ended inside an LSP header",
                ))
            };
        }
        header_bytes += read;
        if header_bytes > MAX_HEADER_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LSP header exceeds 8 KiB",
            ));
        }
        let header = header.trim_end_matches(['\r', '\n']);
        if header.is_empty() {
            break;
        }
        let Some((name, value)) = header.split_once(':') else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LSP header line has no separator",
            ));
        };
        if name.eq_ignore_ascii_case("Content-Length") {
            if content_length.is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "duplicate Content-Length",
                ));
            }
            content_length = Some(
                value
                    .trim()
                    .parse::<usize>()
                    .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?,
            );
        }
    }
    let Some(length) = content_length else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "missing Content-Length",
        ));
    };
    if length > MAX_MESSAGE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "LSP message exceeds 16 MiB",
        ));
    }
    let mut body = vec![0; length];
    input.read_exact(&mut body)?;
    Ok(Some(body))
}

fn write_json(output: &mut impl Write, value: &Value) -> io::Result<()> {
    let encoded = serde_json::to_vec(value)?;
    write!(output, "Content-Length: {}\r\n\r\n", encoded.len())?;
    output.write_all(&encoded)?;
    output.flush()
}

fn error_response(id: Value, code: i32, message: &str) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "error": { "code": code, "message": message }
    })
}

fn invalid_params_notification(message: String) -> Value {
    json!({
        "jsonrpc": "2.0",
        "method": "window/showMessage",
        "params": { "type": 1, "message": message }
    })
}

/// Validates the JSON-RPC 2.0 envelope of one decoded message.
///
/// LSP traffic is object-shaped requests (with `id`) and notifications
/// (without). Anything else — arrays, responses, wrong `jsonrpc` version,
/// non-string methods, malformed ids, unstructured params — is rejected with
/// the JSON-RPC "Invalid Request" error so the failure is deterministic
/// instead of silently interpreted.
fn validate_message(message: &Value) -> Result<Incoming, Value> {
    let invalid = |message: &str, id: Option<&RequestId>| {
        error_response(id.map_or(Value::Null, RequestId::value), -32600, message)
    };
    let Some(object) = message.as_object() else {
        return Err(invalid("Invalid Request: expected a JSON object", None));
    };
    // The id is parsed first so every later rejection can echo it back and
    // let clients correlate the failure; a malformed id answers as null.
    let id = object
        .get("id")
        .map(|value| {
            RequestId::parse(value).ok_or_else(|| {
                invalid(
                    "Invalid Request: id must be a string, integer, or null",
                    None,
                )
            })
        })
        .transpose()?;
    if object.get("jsonrpc").and_then(Value::as_str) != Some("2.0") {
        return Err(invalid(
            "Invalid Request: jsonrpc must be \"2.0\"",
            id.as_ref(),
        ));
    }
    let Some(method) = object.get("method").and_then(Value::as_str) else {
        return Err(invalid(
            "Invalid Request: method must be a string",
            id.as_ref(),
        ));
    };
    let params = match object.get("params") {
        None | Some(Value::Null) => Value::Null,
        Some(params @ (Value::Object(_) | Value::Array(_))) => params.clone(),
        Some(_) => {
            return Err(invalid(
                "Invalid Request: params must be structured",
                id.as_ref(),
            ));
        }
    };
    Ok(Incoming {
        id,
        method: method.to_owned(),
        params,
    })
}

/// Resolves the initialize root against the process root.
///
/// Precedence follows the protocol's evolution: `rootUri` first, the first
/// `workspaceFolders` entry when a modern client omits rootUri, legacy
/// `rootPath` next, and the process root when nothing names a workspace.
/// The resolved path is canonicalized and must remain within `root`.
fn initialize_root(params: &Value, process_root: &Path) -> Result<PathBuf, String> {
    if let Some(root_uri) = params.get("rootUri").filter(|value| !value.is_null()) {
        let uri = root_uri
            .as_str()
            .ok_or_else(|| "rootUri must be a string or null".to_owned())?;
        let path = uri_to_path(uri)?;
        return canonicalize_confined(&path, process_root);
    }
    if let Some(folder) = params
        .get("workspaceFolders")
        .and_then(Value::as_array)
        .and_then(|folders| folders.first())
    {
        let uri = folder
            .get("uri")
            .and_then(Value::as_str)
            .ok_or_else(|| "workspace folder requires a uri".to_owned())?;
        let path = uri_to_path(uri)?;
        return canonicalize_confined(&path, process_root);
    }
    if let Some(root_path) = params.get("rootPath").filter(|value| !value.is_null()) {
        let path = root_path
            .as_str()
            .ok_or_else(|| "rootPath must be a string or null".to_owned())?;
        return canonicalize_confined(Path::new(path), process_root);
    }
    Ok(process_root.to_path_buf())
}

/// Canonicalizes `path` and requires the result to stay within `root`.
///
/// Symlinks are resolved by canonicalization, so a link that escapes the
/// root is rejected just like a lexical `..` traversal.
fn canonicalize_confined(path: &Path, root: &Path) -> Result<PathBuf, String> {
    let canonical = path
        .canonicalize()
        .map_err(|error| format!("cannot canonicalize {}: {error}", path.display()))?;
    if canonical.strip_prefix(root).is_err() {
        return Err(format!(
            "path escapes the workspace root: {}",
            canonical.display()
        ));
    }
    Ok(canonical)
}

fn show_message(error: &ServiceError) -> Value {
    json!({
        "jsonrpc": "2.0",
        "method": "window/showMessage",
        "params": { "type": 1, "message": error.to_string() }
    })
}

fn fs_io(error: FileSystemError) -> io::Error {
    io::Error::other(error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn frame(value: &Value) -> Vec<u8> {
        let encoded = serde_json::to_vec(value).expect("json");
        let mut framed = format!("Content-Length: {}\r\n\r\n", encoded.len()).into_bytes();
        framed.extend_from_slice(&encoded);
        framed
    }

    fn read_all(bytes: &[u8]) -> Vec<Value> {
        let mut cursor = Cursor::new(bytes);
        let mut messages = Vec::new();
        while let Ok(Some(raw)) = read_message(&mut cursor) {
            messages.push(serde_json::from_slice(&raw).expect("json"));
        }
        messages
    }

    fn initialize(root: &Path) -> Value {
        json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "capabilities": {},
                "rootUri": path_to_uri(root)
            }
        })
    }

    fn error_codes(messages: &[Value], id: &Value) -> Vec<i64> {
        messages
            .iter()
            .filter(|message| message.get("id") == Some(id))
            .filter_map(|message| message["error"]["code"].as_i64())
            .collect()
    }

    fn results_with_id<'a>(messages: &'a [Value], id: &Value) -> Vec<&'a Value> {
        messages
            .iter()
            .filter(|message| message.get("id") == Some(id))
            .collect()
    }

    fn run_session(root: &Path, input: Vec<u8>) -> (Exit, Vec<Value>) {
        let mut output = Vec::new();
        let exit = run(Cursor::new(input), &mut output, root).expect("run");
        (exit, read_all(&output))
    }

    fn lifecycle_traffic(root: &Path, extra: &[Value]) -> (Exit, Vec<Value>) {
        let mut input = Vec::new();
        input.extend(frame(&initialize(root)));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        for message in extra {
            input.extend(frame(message));
        }
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 99,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        run_session(root, input)
    }

    fn open_document(uri: &str, text: &str) -> Value {
        json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "typescript",
                    "version": 1,
                    "text": text
                }
            }
        })
    }

    fn change_document(uri: &str, version: u64, changes: Value) -> Value {
        json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didChange",
            "params": {
                "textDocument": { "uri": uri, "version": version },
                "contentChanges": changes
            }
        })
    }

    fn query_request(id: i64, method: &str, uri: &str) -> Value {
        json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": {
                "textDocument": { "uri": uri },
                "position": { "line": 0, "character": 0 }
            }
        })
    }

    fn show_message_texts(messages: &[Value]) -> Vec<String> {
        messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str) == Some("window/showMessage")
            })
            .filter_map(|message| message["params"]["message"].as_str().map(str::to_owned))
            .collect()
    }

    #[test]
    fn handshake_frames_lifecycle_and_exit() {
        let root = tempfile::tempdir().expect("temp");
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "exit"
        })));
        let mut output = Vec::new();
        let exit = run(Cursor::new(input), &mut output, root.path()).expect("run");
        assert_eq!(exit, Exit::Shutdown);
        let messages = read_all(&output);
        assert_eq!(
            messages[0]["result"]["capabilities"]["positionEncoding"],
            "utf-16"
        );
        assert_eq!(
            messages[0]["result"]["capabilities"]["textDocumentSync"]["change"],
            1
        );
        assert_eq!(messages[1]["id"], 2);
        assert!(messages[1]["result"].is_null());
    }

    #[test]
    fn document_sync_publishes_diagnostics_from_service() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("case.ts");
        std::fs::write(&file, "const value: number = \"wrong\";\n").expect("seed");
        let uri = path_to_uri(&file);
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "typescript",
                    "version": 1,
                    "text": "const value: number = \"wrong\";\n"
                }
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didChange",
            "params": {
                "textDocument": { "uri": uri, "version": 2 },
                "contentChanges": [{ "text": "const value: number = 1;\n" }]
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didClose",
            "params": { "textDocument": { "uri": uri } }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let publishes: Vec<&Value> = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .collect();
        assert!(
            publishes[0]["params"]["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .any(|diagnostic| diagnostic["code"] == "BAMTS-C004"),
            "{publishes:?}"
        );
        assert!(
            publishes[2]["params"]["diagnostics"]
                .as_array()
                .expect("closed")
                .is_empty()
        );
    }

    #[test]
    fn close_clears_diagnostics_under_the_canonical_uri() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("caf\u{e9}.ts");
        std::fs::write(&file, "const value: number = \"wrong\";\n").expect("seed");
        let canonical = path_to_uri(&file);
        let variant = canonical.replace("%C3%A9", "%c3%a9");
        assert_ne!(variant, canonical);
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": variant,
                    "languageId": "typescript",
                    "version": 1,
                    "text": "const value: number = \"wrong\";\n"
                }
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didClose",
            "params": { "textDocument": { "uri": variant } }
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let publishes: Vec<&Value> = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .collect();
        // The open and the clear must address the same canonical URI even
        // when the client spelled its escapes differently.
        assert_eq!(publishes.len(), 2, "{messages:?}");
        assert_eq!(publishes[0]["params"]["uri"], json!(canonical));
        assert!(
            publishes[0]["params"]["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .any(|diagnostic| diagnostic["code"] == "BAMTS-C004")
        );
        assert_eq!(publishes[1]["params"]["uri"], json!(canonical));
        assert!(
            publishes[1]["params"]["diagnostics"]
                .as_array()
                .expect("cleared")
                .is_empty()
        );
    }

    #[test]
    fn failed_recomputation_preserves_last_published_diagnostics() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("stale.ts");
        std::fs::write(&file, "const value: number = \"wrong\";\n").expect("seed");
        let uri = path_to_uri(&file);
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "typescript",
                    "version": 1,
                    "text": "const value: number = \"wrong\";\n"
                }
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didChange",
            "params": {
                "textDocument": { "uri": uri, "version": 1 },
                "contentChanges": [{ "text": "const value: number = \"also wrong\";\n" }]
            }
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let publishes: Vec<&Value> = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .collect();
        assert_eq!(publishes.len(), 2, "{messages:?}");
        for publish in &publishes {
            assert!(
                publish["params"]["diagnostics"]
                    .as_array()
                    .expect("diagnostics")
                    .iter()
                    .any(|diagnostic| diagnostic["code"] == "BAMTS-C004"),
                "failed recomputation must preserve the last good set: {publishes:?}"
            );
        }
    }

    #[test]
    fn unavailable_rename_returns_null_result() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("ren.ts");
        std::fs::write(&file, "const answer = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "typescript",
                    "version": 1,
                    "text": "const answer = 1;\n"
                }
            }
        })));
        // Position 0 sits on the `const` keyword: nothing renames there.
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 7,
            "method": "textDocument/rename",
            "params": {
                "textDocument": { "uri": uri },
                "position": { "line": 0, "character": 0 },
                "newName": "renamed"
            }
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let rename_response = messages
            .iter()
            .find(|message| message.get("id") == Some(&json!(7)))
            .expect("rename response");
        assert!(
            rename_response.get("error").is_none(),
            "{rename_response:?}"
        );
        assert!(rename_response["result"].is_null(), "{rename_response:?}");
    }

    #[test]
    fn nonlocal_file_uri_authorities_are_rejected() {
        assert_eq!(
            uri_to_path("file:///tmp/a.ts").expect("empty authority"),
            PathBuf::from("/tmp/a.ts")
        );
        assert_eq!(
            uri_to_path("file://localhost/tmp/a.ts").expect("localhost"),
            PathBuf::from("/tmp/a.ts")
        );
        let rejected = uri_to_path("file://evil.com/share.ts");
        assert!(
            rejected.as_deref().is_err_and(|message| {
                message.contains("nonlocal file URI authority: evil.com")
            }),
            "{rejected:?}"
        );
        assert!(uri_to_path("file://evil.com").is_err());
    }

    #[test]
    fn references_exclude_declaration_only_when_asked() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("refs.ts");
        std::fs::write(&file, "const answer = 1;\nconst copy = answer;\n").expect("seed");
        let uri = path_to_uri(&file);
        let reference = |id: u64, include: bool| {
            json!({
                "jsonrpc": "2.0",
                "id": id,
                "method": "textDocument/references",
                "params": {
                    "textDocument": { "uri": uri },
                    "position": { "line": 1, "character": 13 },
                    "context": { "includeDeclaration": include }
                }
            })
        };
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "typescript",
                    "version": 1,
                    "text": "const answer = 1;\nconst copy = answer;\n"
                }
            }
        })));
        input.extend(frame(&reference(11, false)));
        input.extend(frame(&reference(12, true)));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let response = |id: u64| {
            messages
                .iter()
                .find(|message| message.get("id") == Some(&json!(id)))
                .expect("references response")["result"]
                .as_array()
                .expect("locations")
                .clone()
        };
        let excluded = response(11);
        let included = response(12);
        // Position 13 on line 1 is the `answer` use; the declaration lives
        // on line 0 and must drop out only when excluded.
        assert_eq!(excluded.len(), 1, "{excluded:?}");
        assert_eq!(excluded[0]["range"]["start"]["line"], 1);
        assert_eq!(included.len(), 2, "{included:?}");
    }

    #[test]
    fn initialize_honors_workspace_folders_fallback() {
        let root = tempfile::tempdir().expect("temp");
        let nested = root.path().join("nested");
        std::fs::create_dir(&nested).expect("nested root");
        std::fs::write(nested.join("a.ts"), "const a = 1;\n").expect("seed");
        std::fs::write(root.path().join("outside.ts"), "const b = 2;\n").expect("seed");
        let mut params = initialize(root.path());
        params["params"]["rootUri"] = Value::Null;
        params["params"]["workspaceFolders"] = json!([
            { "uri": path_to_uri(&nested), "name": "nested" }
        ]);
        let mut input = Vec::new();
        input.extend(frame(&params));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&open_document(
            &path_to_uri(&nested.join("a.ts")),
            "const a = 1;\n",
        )));
        input.extend(frame(&open_document(
            &path_to_uri(&root.path().join("outside.ts")),
            "const b = 2;\n",
        )));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let publishes: Vec<&Value> = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .collect();
        // The nested folder became the workspace root: its document opens
        // and publishes, while the file beside the process root is refused.
        assert_eq!(publishes.len(), 1, "{messages:?}");
        assert_eq!(
            publishes[0]["params"]["uri"],
            json!(path_to_uri(&nested.join("a.ts")))
        );
        assert!(
            messages.iter().any(|message| {
                message.get("method").and_then(Value::as_str) == Some("window/showMessage")
            }),
            "outside document must be refused: {messages:?}"
        );
    }

    #[test]
    fn queries_route_through_service_state() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("query.ts");
        let source = "const answer = 1;\nconst copy = answer;\n";
        std::fs::write(&file, source).expect("seed");
        let uri = path_to_uri(&file);
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "typescript",
                    "version": 1,
                    "text": source
                }
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 10,
            "method": "textDocument/definition",
            "params": {
                "textDocument": { "uri": uri },
                "position": { "line": 1, "character": 14 }
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 11,
            "method": "textDocument/completion",
            "params": {
                "textDocument": { "uri": uri },
                "position": { "line": 1, "character": 14 }
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let mut output = Vec::new();
        run(Cursor::new(input), &mut output, root.path()).expect("run");
        let messages = read_all(&output);
        let definition = messages
            .iter()
            .find(|message| message.get("id") == Some(&json!(10)))
            .expect("definition");
        assert_eq!(definition["result"]["uri"], uri);
        let completion = messages
            .iter()
            .find(|message| message.get("id") == Some(&json!(11)))
            .expect("completion");
        assert!(
            completion["result"]
                .as_array()
                .expect("items")
                .iter()
                .any(|item| item["label"] == "answer"),
            "{completion:?}"
        );
    }

    #[test]
    fn hover_reports_quick_info_with_queried_range_and_null_whitespace() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("hover.ts");
        let source = "const answer = 1;\nlet copy = answer;\n";
        std::fs::write(&file, source).expect("seed");
        let uri = path_to_uri(&file);
        // `answer` on line 1 spans characters 11..17; character 5 on line 0
        // is whitespace between tokens.
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document(&uri, source),
                json!({
                    "jsonrpc": "2.0",
                    "id": 10,
                    "method": "textDocument/hover",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 1, "character": 12 }
                    }
                }),
                json!({
                    "jsonrpc": "2.0",
                    "id": 11,
                    "method": "textDocument/hover",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 5 }
                    }
                }),
                json!({
                    "jsonrpc": "2.0",
                    "id": 12,
                    "method": "textDocument/hover",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 99, "character": 0 }
                    }
                }),
            ],
        );
        let hover = results_with_id(&messages, &json!(10));
        assert_eq!(hover.len(), 1);
        let result = &hover[0]["result"];
        assert_eq!(result["contents"]["kind"], "plaintext");
        let display = result["contents"]["value"].as_str().expect("display");
        assert!(
            display.contains("answer"),
            "display names the symbol: {display}"
        );
        assert_eq!(
            result["range"],
            json!({
                "start": { "line": 1, "character": 11 },
                "end": { "line": 1, "character": 17 }
            })
        );
        let whitespace = results_with_id(&messages, &json!(11));
        assert_eq!(whitespace.len(), 1);
        assert_eq!(whitespace[0]["result"], Value::Null);
        let invalid = results_with_id(&messages, &json!(12));
        assert_eq!(invalid.len(), 1);
        assert_eq!(invalid[0]["error"]["code"], json!(-32602));
    }

    #[test]
    fn hover_positions_use_utf16_units_past_non_bmp_text() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("astral.ts");
        // `😀` is one code point but two UTF-16 units, so the reference `s`
        // sits at characters 25..26 in LSP coordinates.
        let source = "let s = \"😀\"; let copy = s;";
        std::fs::write(&file, source).expect("seed");
        let uri = path_to_uri(&file);
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document(&uri, source),
                json!({
                    "jsonrpc": "2.0",
                    "id": 20,
                    "method": "textDocument/hover",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 25 }
                    }
                }),
                json!({
                    "jsonrpc": "2.0",
                    "id": 21,
                    "method": "textDocument/hover",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 10 }
                    }
                }),
            ],
        );
        let hover = results_with_id(&messages, &json!(20));
        assert_eq!(hover.len(), 1);
        let result = &hover[0]["result"];
        assert_eq!(result["contents"]["kind"], "plaintext");
        let display = result["contents"]["value"].as_str().expect("display");
        assert!(!display.is_empty(), "display is non-empty: {display}");
        assert_eq!(
            result["range"],
            json!({
                "start": { "line": 0, "character": 25 },
                "end": { "line": 0, "character": 26 }
            })
        );
        let invalid = results_with_id(&messages, &json!(21));
        assert_eq!(invalid.len(), 1);
        assert_eq!(invalid[0]["error"]["code"], json!(-32602));
    }

    #[test]
    fn lsp_position_counts_utf16_units() {
        let source = "a😀b";
        assert_eq!(lsp_position(source, 0, 0), Some(Utf16Pos::new(0)));
        assert_eq!(lsp_position(source, 0, 1), Some(Utf16Pos::new(1)));
        assert_eq!(lsp_position(source, 0, 2), None);
        assert_eq!(lsp_position(source, 0, 3), Some(Utf16Pos::new(3)));
    }

    #[test]
    fn lsp_position_respects_lines_and_utf16_units() {
        let source = "a😀\r\n😀b\nok";
        assert_eq!(lsp_position(source, 1, 0), Some(Utf16Pos::new(5)));
        assert_eq!(lsp_position(source, 1, 1), None);
        assert_eq!(lsp_position(source, 1, 2), Some(Utf16Pos::new(7)));
        assert_eq!(lsp_position(source, 2, 0), Some(Utf16Pos::new(9)));
        assert_eq!(lsp_position(source, 2, 100), Some(Utf16Pos::new(11)));
        assert_eq!(lsp_position(source, 9, 0), None);
    }

    #[test]
    fn initialize_advertises_exactly_supported_capabilities() {
        let root = tempfile::tempdir().expect("temp");
        let (_, messages) = lifecycle_traffic(root.path(), &[]);
        let init = results_with_id(&messages, &json!(1))
            .into_iter()
            .next()
            .expect("initialize response");
        let capabilities = init["result"]["capabilities"]
            .as_object()
            .expect("capabilities object");
        let mut advertised: Vec<&String> = capabilities.keys().collect();
        advertised.sort_unstable();
        assert_eq!(
            advertised,
            [
                "completionProvider",
                "definitionProvider",
                "hoverProvider",
                "positionEncoding",
                "referencesProvider",
                "renameProvider",
                "textDocumentSync"
            ]
        );
        let sync = &capabilities["textDocumentSync"];
        assert_eq!(sync["openClose"], json!(true));
        assert_eq!(sync["change"], json!(1));
        assert_eq!(init["result"]["serverInfo"]["name"], json!("bamts-lsp"));
    }

    #[test]
    fn requests_before_initialize_fail_with_server_not_initialized() {
        let root = tempfile::tempdir().expect("temp");
        let mut input = Vec::new();
        input.extend(frame(&query_request(
            7,
            "textDocument/definition",
            "file:///nowhere.ts",
        )));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 8,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Unrequested);
        assert_eq!(error_codes(&messages, &json!(7)), [-32002]);
        assert_eq!(error_codes(&messages, &json!(8)), [-32002]);
        // Notifications before initialize are ignored, never answered.
        assert!(
            messages
                .iter()
                .all(|message| message.get("method").is_none()),
            "no server-to-client notifications before initialize: {messages:?}"
        );
    }

    #[test]
    fn initialize_before_initialized_is_completed_and_repeats_fail() {
        let root = tempfile::tempdir().expect("temp");
        // Second initialize while still awaiting `initialized`.
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "initialize",
            "params": { "capabilities": {}, "rootUri": path_to_uri(root.path()) }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        // Third initialize once fully running.
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 3,
            "method": "initialize",
            "params": { "capabilities": {}, "rootUri": path_to_uri(root.path()) }
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Unrequested);
        assert_eq!(error_codes(&messages, &json!(2)), [-32600]);
        assert_eq!(error_codes(&messages, &json!(3)), [-32600]);
        assert!(
            results_with_id(&messages, &json!(1))[0]["result"]["capabilities"]
                .as_object()
                .is_some()
        );
    }

    #[test]
    fn requests_are_rejected_after_shutdown() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("after.ts");
        std::fs::write(&file, "const value = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&open_document(&uri, "const value = 1;\n")));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&query_request(100, "textDocument/definition", &uri)));
        input.extend(frame(&open_document(&uri, "const value = 2;\n")));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Shutdown);
        // Every request after shutdown fails.
        assert_eq!(error_codes(&messages, &json!(100)), [-32600]);
        // Notifications after shutdown are dropped: no second publish.
        let publishes = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .count();
        assert_eq!(publishes, 1);
    }

    #[test]
    fn exit_without_shutdown_reports_unrequested() {
        let root = tempfile::tempdir().expect("temp");
        let input = frame(&json!({ "jsonrpc": "2.0", "method": "exit" }));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Unrequested);
        assert!(messages.is_empty());
    }

    #[test]
    fn stream_end_without_exit_reports_unrequested() {
        let root = tempfile::tempdir().expect("temp");
        let (exit, _) = run_session(root.path(), Vec::new());
        assert_eq!(exit, Exit::Unrequested);
    }

    #[test]
    fn exit_as_request_is_rejected() {
        let root = tempfile::tempdir().expect("temp");
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 5,
            "method": "exit",
            "params": null
        })));
        // The rejected exit must not terminate the session.
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Unrequested);
        assert_eq!(error_codes(&messages, &json!(5)), [-32600]);
    }

    #[test]
    fn parse_errors_answer_with_null_id() {
        let root = tempfile::tempdir().expect("temp");
        let body = b"{not json";
        let mut input = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
        input.extend_from_slice(body);
        let (_, messages) = run_session(root.path(), input);
        assert_eq!(messages.len(), 1);
        assert!(messages[0]["id"].is_null());
        assert_eq!(messages[0]["error"]["code"], json!(-32700));
    }

    #[test]
    fn invalid_request_objects_are_rejected() {
        let root = tempfile::tempdir().expect("temp");
        let cases: Vec<(Value, Option<Value>)> = vec![
            // Missing jsonrpc member.
            (json!({ "id": 1, "method": "shutdown" }), Some(json!(1))),
            // Wrong protocol version.
            (
                json!({ "jsonrpc": "1.0", "id": 2, "method": "shutdown" }),
                Some(json!(2)),
            ),
            // jsonrpc not a string.
            (
                json!({ "jsonrpc": 2.0, "id": 3, "method": "shutdown" }),
                Some(json!(3)),
            ),
            // Missing method.
            (json!({ "jsonrpc": "2.0", "id": 4 }), Some(json!(4))),
            // Method not a string.
            (
                json!({ "jsonrpc": "2.0", "id": 5, "method": 42 }),
                Some(json!(5)),
            ),
            // Non-array, non-object message.
            (json!([1, 2, 3]), None),
            // Malformed id: fractional numbers are not valid ids.
            (
                json!({ "jsonrpc": "2.0", "id": 1.5, "method": "shutdown" }),
                None,
            ),
            // Malformed id: structured values are not valid ids.
            (
                json!({ "jsonrpc": "2.0", "id": { "n": 1 }, "method": "shutdown" }),
                None,
            ),
            // Malformed params: must be structured or omitted.
            (
                json!({ "jsonrpc": "2.0", "id": 6, "method": "shutdown", "params": 17 }),
                Some(json!(6)),
            ),
        ];
        for (invalid, id) in cases {
            let mut input = frame(&invalid);
            input.extend(frame(&initialize(root.path())));
            input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
            let (_, messages) = run_session(root.path(), input);
            let errors: Vec<&Value> = messages
                .iter()
                .filter(|message| message.get("error").is_some())
                .collect();
            assert_eq!(errors.len(), 1, "one rejection for {invalid}");
            assert_eq!(errors[0]["error"]["code"], json!(-32600), "for {invalid}");
            let expected_id = id.unwrap_or(Value::Null);
            assert_eq!(errors[0]["id"], expected_id, "for {invalid}");
            // The session must remain usable: initialize still answered.
            assert!(
                messages
                    .iter()
                    .any(|message| message.get("result").is_some()),
                "session survives {invalid}"
            );
        }
    }

    #[test]
    fn unknown_request_method_is_method_not_found() {
        let root = tempfile::tempdir().expect("temp");
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[json!({
                "jsonrpc": "2.0",
                "id": 21,
                "method": "textDocument/typeDefinition",
                "params": {}
            })],
        );
        assert_eq!(error_codes(&messages, &json!(21)), [-32601]);
    }

    #[test]
    fn notification_only_methods_rejected_as_requests() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("shape.ts");
        std::fs::write(&file, "const value = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        let (exit, messages) = lifecycle_traffic(
            root.path(),
            &[
                json!({
                    "jsonrpc": "2.0",
                    "method": "initialized",
                    "params": {}
                }),
                json!({ "jsonrpc": "2.0", "id": 30, "method": "textDocument/didOpen",
                        "params": { "textDocument": { "uri": uri, "languageId": "typescript",
                                                       "version": 1, "text": "const value = 1;\n" } } }),
                json!({ "jsonrpc": "2.0", "id": 31, "method": "initialized", "params": {} }),
            ],
        );
        assert_eq!(exit, Exit::Shutdown);
        assert_eq!(error_codes(&messages, &json!(30)), [-32600]);
        assert_eq!(error_codes(&messages, &json!(31)), [-32600]);
    }

    #[test]
    fn request_only_methods_sent_as_notifications_are_reported() {
        let root = tempfile::tempdir().expect("temp");
        let mut input = Vec::new();
        input.extend(frame(&initialize(root.path())));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "shutdown" })));
        // The malformed shutdown must not end the session.
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 51,
            "method": "textDocument/completion",
            "params": {
                "textDocument": { "uri": "file:///missing.ts" },
                "position": { "line": 0, "character": 0 }
            }
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Unrequested);
        let texts = show_message_texts(&messages);
        assert_eq!(texts.len(), 1, "{texts:?}");
        assert!(texts[0].contains("shutdown"), "{texts:?}");
        // The session kept serving requests after the malformed notification.
        assert_eq!(error_codes(&messages, &json!(51)), [-32602]);
    }

    #[test]
    fn queued_cancelled_request_never_succeeds() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("cancel.ts");
        std::fs::write(&file, "const answer = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        // The cancel notification arrives before the request it targets.
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document(&uri, "const answer = 1;\n"),
                json!({
                    "jsonrpc": "2.0",
                    "method": "$/cancelRequest",
                    "params": { "id": 40 }
                }),
                query_request(40, "textDocument/definition", &uri),
            ],
        );
        assert_eq!(error_codes(&messages, &json!(40)), [-32800]);
        assert!(results_with_id(&messages, &json!(40))[0]["error"].is_object());
    }

    #[test]
    fn string_ids_cancel_and_respond_symmetrically() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("cancel-str.ts");
        std::fs::write(&file, "const answer = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document(&uri, "const answer = 1;\n"),
                json!({
                    "jsonrpc": "2.0",
                    "method": "$/cancelRequest",
                    "params": { "id": "req-1" }
                }),
                json!({
                    "jsonrpc": "2.0",
                    "id": "req-1",
                    "method": "textDocument/completion",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 0, "character": 0 }
                    }
                }),
            ],
        );
        assert_eq!(error_codes(&messages, &json!("req-1")), [-32800]);
    }

    #[test]
    fn malformed_cancel_requests_are_reported() {
        let root = tempfile::tempdir().expect("temp");
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                json!({
                    "jsonrpc": "2.0",
                    "id": 50,
                    "method": "$/cancelRequest",
                    "params": { "id": 51 }
                }),
                json!({
                    "jsonrpc": "2.0",
                    "method": "$/cancelRequest",
                    "params": {}
                }),
                json!({
                    "jsonrpc": "2.0",
                    "method": "$/cancelRequest",
                    "params": { "id": true }
                }),
            ],
        );
        assert_eq!(error_codes(&messages, &json!(50)), [-32600]);
        let texts = show_message_texts(&messages);
        assert_eq!(texts.len(), 2, "{texts:?}");
        assert!(
            texts.iter().all(|text| text.contains("cancelRequest")),
            "{texts:?}"
        );
    }

    #[test]
    fn ranged_and_ambiguous_changes_are_rejected() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("sync.ts");
        std::fs::write(&file, "const value = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document(&uri, "const value = 1;\n"),
                // Ranged incremental change: not supported by the advertised
                // full sync (change: 1).
                change_document(
                    &uri,
                    2,
                    json!([{ "range": {
                        "start": { "line": 0, "character": 0 },
                        "end": { "line": 0, "character": 5 }
                    }, "text": "let" }]),
                ),
                // rangeLength without being a full change is still ranged.
                change_document(
                    &uri,
                    3,
                    json!([{ "rangeLength": 5, "text": "let value = 2;\n" }]),
                ),
                // Two changes are ambiguous under full sync.
                change_document(
                    &uri,
                    4,
                    json!([{ "text": "const a = 1;\n" }, { "text": "const b = 2;\n" }]),
                ),
                // Zero changes carry no document state.
                change_document(&uri, 5, json!([])),
                // A change entry without text is invalid.
                change_document(&uri, 6, json!([{ "range": null }])),
                // Non-string text is invalid.
                change_document(&uri, 7, json!([{ "text": 42 }])),
                // A final valid full change must still apply: rejections never
                // leave the document in a half-updated state.
                change_document(&uri, 8, json!([{ "text": "const value = 9;\n" }])),
            ],
        );
        let texts = show_message_texts(&messages);
        assert_eq!(
            texts,
            [
                "ranged document changes are not supported",
                "ranged document changes are not supported",
                "full-sync didChange requires exactly one content change",
                "full-sync didChange requires exactly one content change",
                "ranged document changes are not supported",
                "content change requires text",
            ]
        );
    }

    #[test]
    fn malformed_open_close_and_missing_version_are_reported() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("open.ts");
        std::fs::write(&file, "const value = 1;\n").expect("seed");
        let uri = path_to_uri(&file);
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen",
                        "params": { "textDocument": { "uri": uri, "version": 1 } } }),
                json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen",
                        "params": { "textDocument": { "uri": uri, "languageId": "typescript",
                                                       "version": 1 } } }),
                json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen",
                        "params": { "textDocument": { "uri": uri, "languageId": "typescript",
                                                       "text": "const value = 1;\n" } } }),
                json!({ "jsonrpc": "2.0", "method": "textDocument/didChange",
                        "params": { "textDocument": { "uri": uri },
                                    "contentChanges": [{ "text": "const value = 2;\n" }] } }),
                json!({ "jsonrpc": "2.0", "method": "textDocument/didClose",
                        "params": {} }),
            ],
        );
        let texts = show_message_texts(&messages);
        assert_eq!(
            texts,
            [
                "didOpen requires uri and text",
                "didOpen requires uri and text",
                "didOpen requires an integer version",
                "didChange requires uri and version",
                "didClose requires a uri",
            ]
        );
    }

    #[test]
    fn initialize_root_outside_process_root_is_rejected() {
        let process_root = tempfile::tempdir().expect("temp");
        let outside = tempfile::tempdir().expect("temp");
        let mut input = Vec::new();
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": { "capabilities": {}, "rootUri": path_to_uri(outside.path()) }
        })));
        // Still uninitialized after the failed initialize.
        input.extend(frame(&query_request(
            2,
            "textDocument/completion",
            "file:///x.ts",
        )));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(process_root.path(), input);
        assert_eq!(exit, Exit::Unrequested);
        assert_eq!(error_codes(&messages, &json!(1)), [-32602]);
        assert_eq!(error_codes(&messages, &json!(2)), [-32002]);
    }

    #[test]
    fn initialize_accepts_root_path_fallback_and_defaults() {
        let root = tempfile::tempdir().expect("temp");
        // rootUri: null with rootPath set falls back to rootPath.
        let mut input = Vec::new();
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "capabilities": {},
                "rootUri": Value::Null,
                "rootPath": root.path().to_str().expect("utf8")
            }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Shutdown);
        assert!(results_with_id(&messages, &json!(1))[0]["result"].is_object());
        // No root parameters at all: the process root stands in.
        let mut input = Vec::new();
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": { "capabilities": {} }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Shutdown);
        assert!(results_with_id(&messages, &json!(1))[0]["result"].is_object());
    }

    #[test]
    fn document_uris_must_stay_inside_the_workspace_root() {
        let root = tempfile::tempdir().expect("temp");
        let inner = root.path().join("inner");
        std::fs::create_dir(&inner).expect("mkdir");
        let outside_file = root.path().join("outside.ts");
        std::fs::write(&outside_file, "const outside = 1;\n").expect("seed");
        let workspace_file = inner.join("inside.ts");
        std::fs::write(&workspace_file, "const inside = 1;\n").expect("seed");
        // Lexical traversal out of the workspace root.
        let escape_uri = path_to_uri(&inner.join("..").join("outside.ts"));
        // A symlink inside the workspace pointing outside it.
        let link = inner.join("link.ts");
        std::os::unix::fs::symlink(&outside_file, &link).expect("symlink");
        let mut input = Vec::new();
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": { "capabilities": {}, "rootUri": path_to_uri(&inner) }
        })));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        // Every document outside the workspace root is refused: direct,
        // traversed, and symlinked alike.
        input.extend(frame(&open_document(
            &path_to_uri(&outside_file),
            "const outside = 1;\n",
        )));
        input.extend(frame(&open_document(&escape_uri, "const outside = 1;\n")));
        input.extend(frame(&open_document(
            &path_to_uri(&link),
            "const outside = 1;\n",
        )));
        // Documents inside the workspace root still work.
        input.extend(frame(&open_document(
            &path_to_uri(&workspace_file),
            "const inside = 1;\n",
        )));
        input.extend(frame(&json!({
            "jsonrpc": "2.0",
            "id": 99,
            "method": "shutdown",
            "params": null
        })));
        input.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
        let (exit, messages) = run_session(root.path(), input);
        assert_eq!(exit, Exit::Shutdown);
        let texts = show_message_texts(&messages);
        assert_eq!(texts.len(), 3, "{texts:?}");
        assert!(
            texts.iter().all(|text| text.contains("workspace root")),
            "{texts:?}"
        );
        // Exactly one diagnostics publish succeeded: the in-workspace file.
        let publishes = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .count();
        assert_eq!(publishes, 1);
    }

    #[test]
    fn non_file_uris_are_rejected() {
        let root = tempfile::tempdir().expect("temp");
        let (_, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document("untitled:Untitled-1", "const value = 1;\n"),
                json!({
                    "jsonrpc": "2.0",
                    "id": 70,
                    "method": "textDocument/completion",
                    "params": {
                        "textDocument": { "uri": "https://example.com/x.ts" },
                        "position": { "line": 0, "character": 0 }
                    }
                }),
            ],
        );
        let texts = show_message_texts(&messages);
        assert!(
            texts
                .iter()
                .any(|text| text.contains("unsupported URI scheme")),
            "{texts:?}"
        );
        assert_eq!(error_codes(&messages, &json!(70)), [-32602]);
    }

    #[test]
    fn percent_encoded_uris_resolve_to_the_same_document() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("with space.ts");
        std::fs::write(&file, "const answer = 1;\nconst copy = answer;\n").expect("seed");
        let uri = path_to_uri(&file);
        assert!(uri.contains("%20"), "{uri}");
        let (exit, messages) = lifecycle_traffic(
            root.path(),
            &[
                open_document(&uri, "const answer = 1;\nconst copy = answer;\n"),
                json!({
                    "jsonrpc": "2.0",
                    "id": 80,
                    "method": "textDocument/definition",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": { "line": 1, "character": 14 }
                    }
                }),
            ],
        );
        assert_eq!(exit, Exit::Shutdown);
        assert_eq!(error_codes(&messages, &json!(80)), Vec::<i64>::new());
        let definition = results_with_id(&messages, &json!(80))
            .into_iter()
            .next()
            .expect("definition response");
        assert_eq!(definition["result"]["uri"], json!(uri));
    }

    #[test]
    fn framing_rejects_messages_over_16_mib() {
        let oversized = MAX_MESSAGE_BYTES + 1;
        let header = format!("Content-Length: {oversized}\r\n\r\n");
        let mut cursor = Cursor::new(header.into_bytes());
        let error = read_message(&mut cursor).expect_err("oversized");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn framing_accepts_a_message_at_the_16_mib_bound() {
        let body = vec![0u8; MAX_MESSAGE_BYTES];
        let mut input = format!("Content-Length: {}\r\n\r\n", MAX_MESSAGE_BYTES).into_bytes();
        input.extend_from_slice(&body);
        let mut cursor = Cursor::new(input);
        let raw = read_message(&mut cursor)
            .expect("boundary message")
            .expect("body");
        assert_eq!(raw.len(), MAX_MESSAGE_BYTES);
    }

    #[test]
    fn framing_requires_content_length() {
        let mut cursor = Cursor::new(b"Content-Type: application/vscode-jsonrpc\r\n\r\n".to_vec());
        let error = read_message(&mut cursor).expect_err("missing length");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn framing_bounds_header_reads_before_a_newline() {
        for prefix in ["", "Content-Length: 2\r\n", "X: y\r\n"] {
            let bytes = format!("{prefix}X-Padding: {}", "x".repeat(16 * 1024));
            let mut input = Cursor::new(bytes);
            let error = read_message(&mut input).expect_err("header budget");
            assert_eq!(error.kind(), io::ErrorKind::InvalidData);
            assert_eq!(input.position(), 8193, "reject at the first excess byte");
        }
    }

    #[test]
    fn framing_rejects_duplicate_lengths_and_malformed_headers() {
        for bytes in [
            "Content-Length: 2\r\nContent-Length: 2\r\n\r\n{}",
            "Content-Length: 9\r\ncontent-length: 2\r\n\r\n{}",
            "Not a header\r\nContent-Length: 2\r\n\r\n{}",
        ] {
            let error = read_message(&mut Cursor::new(bytes)).expect_err(bytes);
            assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        }
    }

    #[test]
    fn framing_distinguishes_eof_from_a_truncated_header() {
        assert_eq!(
            read_message(&mut Cursor::new(b"")).expect("clean EOF"),
            None
        );
        for bytes in ["Content-Length: 2", "Content-Length: 2\r\n"] {
            let error = read_message(&mut Cursor::new(bytes)).expect_err("truncated header");
            assert_eq!(error.kind(), io::ErrorKind::UnexpectedEof);
        }
    }

    #[test]
    fn framing_preserves_exact_budget_and_fragmented_frame_boundaries() {
        let mut bytes = b"Content-Length: 2\r\nX-Padding: ".to_vec();
        bytes.resize(8192 - 4, b'x');
        bytes.extend_from_slice(b"\r\n\r\n{}");
        bytes.extend_from_slice(b"Content-Length: 2\r\n\r\n[]");
        for capacity in [1, 2, 3, 7, 13, 512, 8192] {
            let mut input = io::BufReader::with_capacity(capacity, Cursor::new(&bytes));
            assert_eq!(
                read_message(&mut input).expect("first frame"),
                Some(b"{}".to_vec())
            );
            assert_eq!(
                read_message(&mut input).expect("second frame"),
                Some(b"[]".to_vec())
            );
            assert_eq!(read_message(&mut input).expect("clean EOF"), None);
        }
    }

    /// A `BufRead` that serves framed messages in segments, running each
    /// segment's action just before its bytes become readable. This lets a
    /// test mutate the filesystem strictly between two processed messages.
    struct Segment {
        bytes: Vec<u8>,
        before: Option<Box<dyn FnOnce()>>,
    }

    struct SteppingReader {
        segments: std::vec::IntoIter<Segment>,
        current: Vec<u8>,
        offset: usize,
    }

    impl SteppingReader {
        fn new(segments: Vec<Segment>) -> Self {
            Self {
                segments: segments.into_iter(),
                current: Vec::new(),
                offset: 0,
            }
        }
    }

    impl BufRead for SteppingReader {
        fn fill_buf(&mut self) -> io::Result<&[u8]> {
            while self.offset >= self.current.len() {
                match self.segments.next() {
                    Some(segment) => {
                        if let Some(action) = segment.before {
                            action();
                        }
                        self.current = segment.bytes;
                        self.offset = 0;
                    }
                    None => return Ok(&[]),
                }
            }
            Ok(&self.current[self.offset..])
        }

        fn consume(&mut self, amount: usize) {
            self.offset += amount;
        }
    }

    impl io::Read for SteppingReader {
        fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
            let available = self.fill_buf()?;
            let amount = available.len().min(buffer.len());
            buffer[..amount].copy_from_slice(&available[..amount]);
            self.consume(amount);
            Ok(amount)
        }
    }

    #[test]
    fn unresolvable_import_publishes_ts2307_then_clears_on_fix() {
        let root = tempfile::tempdir().expect("temp");
        let file = root.path().join("case.ts");
        let uri = path_to_uri(&file);
        std::fs::write(&file, "import { x } from \"./missing.js\";\n").expect("seed");
        let source = "import { x } from \"./missing.js\";\n";
        let mut handshake = Vec::new();
        handshake.extend(frame(&initialize(root.path())));
        handshake.extend(frame(&json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })));
        // didOpen with an unresolvable relative import → publish carries TS2307.
        handshake.extend(frame(&open_document(&uri, source)));
        // The dependency is written only after that publish, then didChange
        // re-resolves and the next publish must drop TS2307.
        let dependency = root.path().join("missing.ts");
        let mut recovery: Vec<Segment> = Vec::new();
        recovery.push(Segment {
            bytes: {
                let mut bytes = Vec::new();
                bytes.extend(frame(&change_document(
                    &uri,
                    2,
                    json!([{ "text": source }]),
                )));
                bytes.extend(frame(&json!({
                    "jsonrpc": "2.0",
                    "id": 99,
                    "method": "shutdown",
                    "params": null
                })));
                bytes.extend(frame(&json!({ "jsonrpc": "2.0", "method": "exit" })));
                bytes
            },
            before: Some(Box::new(move || {
                std::fs::write(&dependency, "export const x = 1;\n").expect("write dep");
            })),
        });
        let segments = vec![Segment {
            bytes: handshake,
            before: None,
        }]
        .into_iter()
        .chain(recovery)
        .collect();
        let mut output = Vec::new();
        let exit = run(SteppingReader::new(segments), &mut output, root.path()).expect("run");
        assert_eq!(exit, Exit::Shutdown);
        let messages = read_all(&output);
        let publishes: Vec<&Value> = messages
            .iter()
            .filter(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
            })
            .collect();
        assert_eq!(publishes.len(), 2, "{messages:?}");
        let first = &publishes[0]["params"]["diagnostics"];
        let entries = first.as_array().expect("diagnostics array");
        let ts2307 = entries
            .iter()
            .find(|diagnostic| diagnostic["code"] == "2307")
            .expect("didOpen publish carries code 2307");
        assert_eq!(ts2307["severity"], 1, "{first:?}");
        // The catalog template's {0} placeholder is rendered with the
        // specifier; the rendered message must carry it and never leak '{'.
        assert_eq!(
            ts2307["message"],
            "Cannot find module './missing.js' or its corresponding type declarations."
        );
        assert!(
            !ts2307["message"]
                .as_str()
                .expect("message text")
                .contains('{'),
            "template placeholder leaked: {ts2307:?}"
        );
        let second = &publishes[1]["params"]["diagnostics"];
        assert!(
            !second
                .as_array()
                .expect("diagnostics array")
                .iter()
                .any(|diagnostic| diagnostic["code"] == "2307"),
            "didChange publish after the fix must drop TS2307: {second:?}"
        );
    }
}
