//! JSON-RPC wire framing and bounded protocol values.

use std::io::{self, BufRead, Read, Write};

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

/// The largest accepted frame body. A larger declared length is drained whole so
/// the stream stays byte-aligned for the following frame.
pub(crate) const MAX_FRAME_BYTES: usize = 32 * 1024 * 1024;

/// The largest accepted header block. Exceeding it leaves no recoverable body
/// length, so the connection closes rather than desynchronize.
pub(crate) const MAX_HEADER_BYTES: usize = 8 * 1024;

/// Bytes copied per iteration while draining an oversize body.
const DRAIN_CHUNK: usize = 8 * 1024;

pub(crate) const JSONRPC_VERSION: &str = "2.0";

pub(crate) const CODE_PARSE_ERROR: i64 = -32700;
pub(crate) const CODE_INVALID_REQUEST: i64 = -32600;
pub(crate) const CODE_METHOD_NOT_FOUND: i64 = -32601;
pub(crate) const CODE_INVALID_PARAMS: i64 = -32602;
pub(crate) const CODE_INTERNAL_ERROR: i64 = -32603;
pub(crate) const CODE_REQUEST_CANCELLED: i64 = -32800;
pub(crate) const CODE_FRAME_TOO_LARGE: i64 = -32001;
pub(crate) const CODE_NOT_INITIALIZED: i64 = -32002;
pub(crate) const CODE_ROOT_CONFINEMENT: i64 = -32003;
pub(crate) const CODE_SERVICE_ERROR: i64 = -32004;
pub(crate) const CODE_INTAKE_FULL: i64 = -32005;
pub(crate) const CODE_FLOODED: i64 = -32006;

/// A request identifier. Absent identifiers mark notifications.
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(untagged)]
pub enum Id {
    Number(i64),
    Text(String),
}

/// One decoded protocol request.
#[derive(Clone, Debug, Deserialize)]
pub struct Request {
    #[serde(default)]
    pub id: Option<Id>,
    pub method: String,
    #[serde(default)]
    pub params: Option<Value>,
}

/// One protocol error payload.
#[derive(Clone, Debug, Serialize)]
pub struct ErrorObject {
    pub code: i64,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

/// One protocol response. Exactly one of `result` and `error` is present.
#[derive(Clone, Debug, Serialize)]
pub struct Response {
    pub jsonrpc: &'static str,
    pub id: Option<Id>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<ErrorObject>,
}

impl Response {
    pub(crate) fn success(id: Option<Id>, result: Value) -> Self {
        Self {
            jsonrpc: JSONRPC_VERSION,
            id,
            result: Some(result),
            error: None,
        }
    }

    pub(crate) fn failure(id: Option<Id>, error: ApiError) -> Self {
        Self {
            jsonrpc: JSONRPC_VERSION,
            id,
            result: None,
            error: Some(error.into_error_object()),
        }
    }
}

/// Every typed transport and session failure. One conversion site produces the
/// wire form so no code path invents an ad-hoc error shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ApiError {
    /// A frame body was not valid JSON, or headers were unrecoverable.
    Parse(String),
    /// A frame decoded as JSON but not as a request.
    InvalidRequest(String),
    /// A declared body length exceeded [`MAX_FRAME_BYTES`].
    FrameTooLarge { declared: usize, limit: usize },
    /// The method name is not served.
    MethodNotFound(String),
    /// Parameters were missing, of the wrong type, or out of range.
    InvalidParams(String),
    /// A request arrived before a successful `initialize`.
    NotInitialized,
    /// `initialize` ran twice on one session.
    AlreadyInitialized,
    /// A path left the session root.
    RootConfinement(String),
    /// The request identifier was cancelled before dispatch.
    Cancelled,
    /// The bounded ordinary request partition is full.
    IntakeFull,
    /// The bounded reject partition is exhausted; the session terminates.
    Flooded,
    /// A compiler-service failure that is not a confinement violation.
    Service(String),
    /// An invariant of this transport failed.
    Internal(String),
}

impl ApiError {
    #[must_use]
    pub(crate) fn code(&self) -> i64 {
        match self {
            Self::Parse(_) => CODE_PARSE_ERROR,
            Self::InvalidRequest(_) | Self::AlreadyInitialized => CODE_INVALID_REQUEST,
            Self::FrameTooLarge { .. } => CODE_FRAME_TOO_LARGE,
            Self::MethodNotFound(_) => CODE_METHOD_NOT_FOUND,
            Self::InvalidParams(_) => CODE_INVALID_PARAMS,
            Self::NotInitialized => CODE_NOT_INITIALIZED,
            Self::RootConfinement(_) => CODE_ROOT_CONFINEMENT,
            Self::Cancelled => CODE_REQUEST_CANCELLED,
            Self::IntakeFull => CODE_INTAKE_FULL,
            Self::Flooded => CODE_FLOODED,
            Self::Service(_) => CODE_SERVICE_ERROR,
            Self::Internal(_) => CODE_INTERNAL_ERROR,
        }
    }

    /// Projects the typed failure onto its single wire form.
    #[must_use]
    pub fn into_error_object(self) -> ErrorObject {
        let code = self.code();
        let (message, data) = match self {
            Self::Parse(detail) => (format!("parse error: {detail}"), None),
            Self::InvalidRequest(detail) => (format!("invalid request: {detail}"), None),
            Self::FrameTooLarge { declared, limit } => (
                format!("frame body of {declared} bytes exceeds the {limit} byte limit"),
                Some(json!({ "declared": declared, "limit": limit })),
            ),
            Self::MethodNotFound(method) => (
                format!("method not found: {method}"),
                Some(json!({ "method": method })),
            ),
            Self::InvalidParams(detail) => (format!("invalid params: {detail}"), None),
            Self::NotInitialized => (
                "session is not initialized; call initialize first".to_owned(),
                None,
            ),
            Self::AlreadyInitialized => ("session is already initialized".to_owned(), None),
            Self::RootConfinement(detail) => (format!("path escapes session root: {detail}"), None),
            Self::Cancelled => ("request was cancelled".to_owned(), None),
            Self::IntakeFull => (
                "request intake is full; retry after in-flight work completes".to_owned(),
                None,
            ),
            Self::Flooded => (
                "request flood exhausted the transport response budget".to_owned(),
                None,
            ),
            Self::Service(detail) => (format!("service error: {detail}"), None),
            Self::Internal(detail) => (format!("internal error: {detail}"), None),
        };
        ErrorObject {
            code,
            message,
            data,
        }
    }
}

/// One decoded frame, or a recoverable framing fault.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Frame {
    /// A complete body of the declared length.
    Payload(Vec<u8>),
    /// A body larger than the limit, already drained so the stream stays aligned.
    Oversize { declared: usize },
    /// Headers that leave no recoverable body length.
    Malformed(String),
    /// The peer closed the stream at a frame boundary.
    Eof,
}

/// Writes one framed payload.
pub(crate) fn write_frame<W: Write>(writer: &mut W, payload: &[u8]) -> io::Result<()> {
    write!(writer, "Content-Length: {}\r\n\r\n", payload.len())?;
    writer.write_all(payload)?;
    writer.flush()
}

pub(crate) fn write_response<W: Write>(writer: &mut W, response: &Response) -> io::Result<()> {
    let encoded = serde_json::to_vec(response)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    write_frame(writer, &encoded)
}

/// Reads one frame. Fragmentation is resolved by `read_line` and `read_exact`;
/// an oversize body is drained in bounded chunks so the next frame still parses.
pub(crate) fn read_frame<R: BufRead>(reader: &mut R) -> io::Result<Frame> {
    let mut declared: Option<usize> = None;
    let mut header_bytes = 0usize;
    let mut saw_header = false;

    loop {
        let mut line = String::new();
        // Read at most one byte beyond the remaining budget. Checking after an
        // unbounded read_line lets an unterminated header allocate indefinitely.
        let remaining = (MAX_HEADER_BYTES - header_bytes + 1) as u64;
        let read = match reader.take(remaining).read_line(&mut line) {
            Ok(read) => read,
            Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                return Ok(Frame::Malformed(
                    "header block is not valid UTF-8".to_owned(),
                ));
            }
            Err(error) => return Err(error),
        };

        if read == 0 {
            return Ok(if saw_header {
                Frame::Malformed("stream ended inside a header block".to_owned())
            } else {
                Frame::Eof
            });
        }

        header_bytes = header_bytes.saturating_add(read);
        if header_bytes > MAX_HEADER_BYTES {
            return Ok(Frame::Malformed(format!(
                "header block exceeds {MAX_HEADER_BYTES} bytes"
            )));
        }

        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        saw_header = true;

        let Some((name, value)) = trimmed.split_once(':') else {
            return Ok(Frame::Malformed(format!(
                "header line has no separator: {trimmed}"
            )));
        };
        if name.trim().eq_ignore_ascii_case("content-length") {
            if declared.is_some() {
                return Ok(Frame::Malformed(
                    "header block repeats content-length".to_owned(),
                ));
            }
            match value.trim().parse::<usize>() {
                Ok(length) => declared = Some(length),
                Err(error) => {
                    return Ok(Frame::Malformed(format!(
                        "content-length is not a length: {error}"
                    )));
                }
            }
        }
    }

    let Some(declared) = declared else {
        return Ok(Frame::Malformed(
            "header block has no content-length".to_owned(),
        ));
    };

    if declared > MAX_FRAME_BYTES {
        return drain_body(reader, declared);
    }

    let mut body = vec![0u8; declared];
    match reader.read_exact(&mut body) {
        Ok(()) => Ok(Frame::Payload(body)),
        Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => Ok(Frame::Malformed(
            "stream ended inside a frame body".to_owned(),
        )),
        Err(error) => Err(error),
    }
}

/// Consumes exactly `declared` bytes in bounded chunks, never allocating them.
pub(crate) fn drain_body<R: BufRead>(reader: &mut R, declared: usize) -> io::Result<Frame> {
    let mut remaining = declared;
    let mut scratch = [0u8; DRAIN_CHUNK];
    while remaining > 0 {
        let chunk = remaining.min(scratch.len());
        let read = reader.read(&mut scratch[..chunk])?;
        if read == 0 {
            return Ok(Frame::Malformed(
                "stream ended inside an oversize body".to_owned(),
            ));
        }
        remaining -= read;
    }
    Ok(Frame::Oversize { declared })
}
