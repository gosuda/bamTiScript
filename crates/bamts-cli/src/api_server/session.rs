//! Compiler-backed JSON-RPC session dispatch.

use std::{
    future::Future,
    io,
    num::NonZeroUsize,
    ops::ControlFlow,
    path::{Path, PathBuf},
    pin::Pin,
    sync::Arc,
    task::{Context, Poll, Waker},
};

use bamts_compiler::{
    checker::SymbolKind,
    diagnostic::DiagnosticSeverity,
    public_ast::{self, NodeRef},
    service::{
        Completion, DiagnosticEntry, DocumentSnapshot, Location, QuickInfo, QuickInfoKind,
        RenameResult, ServiceError, ServiceSnapshot,
        r#async::{AsyncService, CancellationToken},
        filesystem::{FileSystem, OsFileSystem},
        sync::SyncService,
    },
    source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos},
    syntax::{Node, NodeData, NodeId, SyntaxKind, VariableKind},
};
use serde_json::{Map, Value, json};

use crate::{
    args::parse_args,
    context::ExecutionContext,
    driver::{self, DriverError},
};

use super::wire::{ApiError, Request, Response};
const MAX_IN_FLIGHT: usize = 64;

/// Polls a service future that completes without suspending. The async service
/// contributes bounding and cancellation, never a suspension point, so a pending
/// poll is a transport invariant failure rather than a wait.
fn service_error(error: &ServiceError) -> ApiError {
    match error {
        ServiceError::FileSystem(inner) if inner.kind() == std::io::ErrorKind::PermissionDenied => {
            ApiError::RootConfinement(inner.to_string())
        }
        ServiceError::Cancelled => ApiError::Cancelled,
        ServiceError::InvalidPosition { .. } | ServiceError::InvalidRename(_) => {
            ApiError::InvalidParams(error.to_string())
        }
        _ => ApiError::Service(error.to_string()),
    }
}

fn complete_now<T>(future: impl Future<Output = T>) -> Result<T, ApiError> {
    let waker = Waker::noop();
    let mut context = Context::from_waker(waker);
    let mut future: Pin<Box<_>> = Box::pin(future);
    match future.as_mut().poll(&mut context) {
        Poll::Ready(value) => Ok(value),
        Poll::Pending => Err(ApiError::Internal(
            "service future suspended unexpectedly".to_owned(),
        )),
    }
}

/// One compiler service rooted at `initialize`, plus the cancellation ledger.
struct Compiler {
    filesystem: OsFileSystem,
    sync: SyncService<OsFileSystem>,
    r#async: AsyncService<OsFileSystem>,
}

pub(crate) struct Planned {
    request: Request,
    cancellation: CancellationToken,
}

pub struct Session {
    compiler: Option<Compiler>,
    stopped: bool,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}
/// Reads a node identifier from a JSON request object under a given key.
type NodeIdReader = fn(&Map<String, Value>, &str) -> Result<NodeId, ApiError>;

impl Session {
    #[must_use]
    pub fn new() -> Self {
        Self {
            compiler: None,
            stopped: false,
        }
    }

    /// Whether the loop should stop after the current dispatch batch.
    #[must_use]
    pub const fn stopped(&self) -> bool {
        self.stopped
    }
    pub(crate) fn plan(
        &self,
        request: Request,
        cancellation: &CancellationToken,
    ) -> Result<Planned, ApiError> {
        cancellation.check().map_err(|_| ApiError::Cancelled)?;
        Ok(Planned {
            request,
            cancellation: cancellation.clone(),
        })
    }

    pub(crate) fn apply(&mut self, planned: Planned) -> Option<Response> {
        self.handle(planned.request, &planned.cancellation)
    }

    fn compiler(&self) -> Result<&Compiler, ApiError> {
        self.compiler.as_ref().ok_or(ApiError::NotInitialized)
    }

    /// Handles one request. Notifications return no response.
    pub fn handle(
        &mut self,
        request: Request,
        cancellation: &CancellationToken,
    ) -> Option<Response> {
        let Request { id, method, params } = request;

        if id.is_none() {
            self.notify(&method);
            let _ = self.request(&method, params.as_ref(), cancellation);
            return None;
        }

        let outcome = self.request(&method, params.as_ref(), cancellation);
        Some(match outcome {
            Ok(result) => Response::success(id, result),
            Err(error) => Response::failure(id, error),
        })
    }

    fn notify(&mut self, method: &str) {
        if method == "exit" {
            self.stopped = true;
        }
    }

    fn request(
        &mut self,
        method: &str,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        match method {
            "initialize" => self.initialize(params),
            "shutdown" => {
                self.stopped = true;
                Ok(Value::Null)
            }
            "service/open" => self.open(params, cancellation),
            "service/update" => self.update(params, cancellation),
            "service/close" => self.close(params, cancellation),
            "service/snapshot" => self.snapshot(params, cancellation),
            "service/completions" => self.completions(params, cancellation),
            "service/definition" => self.definition(params, cancellation),
            "service/quickInfo" => self.quick_info(params, cancellation),
            "service/references" => self.references(params, cancellation),
            "service/rename" => self.rename(params, cancellation),
            "service/diagnostics" => self.diagnostics(params, cancellation),
            "ast/id" => self.ast_id(params, cancellation),
            "ast/range" => self.ast_range(params, cancellation),
            "ast/syntaxKind" => self.ast_syntax_kind(params, cancellation),
            "ast/nodeKind" => self.ast_node_kind(params, cancellation),
            "ast/is" => self.ast_is(params, cancellation),
            "ast/factory/create" => self.ast_factory(params, FactoryResult::Create, cancellation),
            "ast/factory/update" => self.ast_factory(params, FactoryResult::Update, cancellation),
            "ast/factory/asNode" => self.ast_factory(params, FactoryResult::AsNode, cancellation),
            "ast/factory/intoOwned" => {
                self.ast_factory(params, FactoryResult::IntoOwned, cancellation)
            }
            "ast/utils/textOfRange" => self.ast_text_of_range(params),
            "ast/utils/nodeText" => self.ast_node_text(params, cancellation),
            "ast/utils/containsRange" => self.ast_contains_range(params),
            "ast/utils/containsPosition" => self.ast_contains_position(params),
            "ast/utils/narrowestContaining" => self.ast_narrowest_containing(params, cancellation),
            "ast/scanner/scan" => self.ast_scan(params, cancellation),
            "ast/visitor/visitSourceFile" => self.ast_visit_source_file(params, cancellation),
            "ast/visitor/visitNode" => self.ast_visit_node(params, cancellation),
            "ast/clone" => self.ast_clone(params, None, cancellation),
            "ast/cloneWithId" => self.ast_clone(params, Some(require_node_id), cancellation),
            "compiler/execute" => self.execute(params, cancellation),
            "compiler/version" => Ok(json!({ "version": crate::args::version_message() })),
            "compiler/explain" => Self::explain(params),
            other => Err(ApiError::MethodNotFound(other.to_owned())),
        }
    }

    /// Roots the session's single compiler service. Confinement is delegated to
    /// OsFileSystem, which is the service's own filesystem seam.
    fn initialize(&mut self, params: Option<&Value>) -> Result<Value, ApiError> {
        if self.compiler.is_some() {
            return Err(ApiError::AlreadyInitialized);
        }
        let object = params_object(params)?;
        let root = require_str(object, "root")?;
        let filesystem = OsFileSystem::new(root).map_err(|error| {
            if error.kind() == io::ErrorKind::PermissionDenied {
                ApiError::RootConfinement(error.to_string())
            } else {
                ApiError::InvalidParams(format!("service root is unusable: {error}"))
            }
        })?;
        let root = filesystem.root().to_path_buf();
        let sync = SyncService::new(filesystem.clone());
        let in_flight = NonZeroUsize::new(MAX_IN_FLIGHT)
            .ok_or_else(|| ApiError::Internal("async bound is zero".to_owned()))?;
        let r#async = AsyncService::from_sync(sync.clone(), in_flight);
        self.compiler = Some(Compiler {
            filesystem,
            sync,
            r#async,
        });
        Ok(json!({ "root": path_text(&root), "methods": SERVICE_METHODS }))
    }

    fn open(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let text = require_str(object, "text")?.to_owned();
        let version = require_u64(object, "version")?;
        let compiler = self.compiler()?;
        let snapshot = if wants_async(object) {
            complete_now(compiler.r#async.open(&path, text, version, cancellation))?
        } else {
            compiler
                .sync
                .open_with_cancel(&path, text, version, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(document_value(
            snapshot.path(),
            snapshot.version(),
            snapshot.is_open(),
        ))
    }

    fn update(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let text = require_str(object, "text")?.to_owned();
        let version = require_u64(object, "version")?;
        let compiler = self.compiler()?;
        let snapshot = if wants_async(object) {
            complete_now(compiler.r#async.update(&path, text, version, cancellation))?
        } else {
            compiler
                .sync
                .update_with_cancel(&path, text, version, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(document_value(
            snapshot.path(),
            snapshot.version(),
            snapshot.is_open(),
        ))
    }

    fn close(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let compiler = self.compiler()?;
        if wants_async(object) {
            complete_now(compiler.r#async.close(&path, cancellation))?
        } else {
            compiler.sync.close_with_cancel(&path, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(json!({ "path": path, "closed": true }))
    }

    fn snapshot(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = optional_object(params)?;
        let compiler = self.compiler()?;
        let snapshot = if wants_async(&object) {
            complete_now(compiler.r#async.snapshot(cancellation))?
        } else {
            compiler.sync.snapshot()
        }
        .map_err(|error| service_error(&error))?;
        Ok(snapshot_value(&snapshot))
    }

    fn completions(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let position = require_position(object)?;
        let compiler = self.compiler()?;
        let completions = if wants_async(object) {
            complete_now(compiler.r#async.completions(&path, position, cancellation))?
        } else {
            compiler
                .sync
                .completions_with_cancel(&path, position, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(Value::Array(
            completions.iter().map(completion_value).collect(),
        ))
    }

    fn definition(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let position = require_position(object)?;
        let compiler = self.compiler()?;
        let location = if wants_async(object) {
            complete_now(compiler.r#async.definition(&path, position, cancellation))?
        } else {
            compiler
                .sync
                .definition_with_cancel(&path, position, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(location.as_ref().map_or(Value::Null, location_value))
    }

    fn quick_info(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let position = require_position(object)?;
        let compiler = self.compiler()?;
        let info = if wants_async(object) {
            complete_now(compiler.r#async.quick_info(&path, position, cancellation))?
        } else {
            compiler
                .sync
                .quick_info_with_cancel(&path, position, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        match info {
            Some(info) => Ok(quick_info_value(&info)),
            None => Ok(Value::Null),
        }
    }

    fn references(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let position = require_position(object)?;
        let compiler = self.compiler()?;
        let locations = if wants_async(object) {
            complete_now(compiler.r#async.references(&path, position, cancellation))?
        } else {
            compiler
                .sync
                .references_with_cancel(&path, position, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(Value::Array(locations.iter().map(location_value).collect()))
    }

    fn rename(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let position = require_position(object)?;
        let new_name = require_str(object, "newName")?.to_owned();
        let compiler = self.compiler()?;
        let result = if wants_async(object) {
            complete_now(
                compiler
                    .r#async
                    .rename(&path, position, &new_name, cancellation),
            )?
        } else {
            compiler
                .sync
                .rename_with_cancel(&path, position, &new_name, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(rename_value(&result))
    }

    fn diagnostics(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let path = require_str(object, "path")?.to_owned();
        let compiler = self.compiler()?;
        let entries = if wants_async(object) {
            complete_now(compiler.r#async.diagnostics(&path, cancellation))?
        } else {
            compiler
                .sync
                .diagnostics_with_cancel(&path, cancellation.clone())
        }
        .map_err(|error| service_error(&error))?;
        Ok(Value::Array(entries.iter().map(diagnostic_value).collect()))
    }

    fn ast_document(
        &self,
        object: &Map<String, Value>,
    ) -> Result<(ServiceSnapshot, PathBuf), ApiError> {
        let compiler = self.compiler()?;
        let path = require_str(object, "path")?;
        let path = compiler
            .filesystem
            .normalize(Path::new(path))
            .map_err(|error| {
                if error.kind() == io::ErrorKind::PermissionDenied {
                    ApiError::RootConfinement(error.to_string())
                } else {
                    ApiError::InvalidParams(error.to_string())
                }
            })?;
        let snapshot = compiler
            .sync
            .snapshot()
            .map_err(|error| service_error(&error))?;
        if snapshot.document(&path).is_none() {
            return Err(ApiError::Service(format!(
                "document is not in the session snapshot: {}",
                path.display()
            )));
        }
        Ok((snapshot, path))
    }

    fn ast_id(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let node = resolve_node(
            snapshot.document(&path).expect("validated document"),
            object,
            cancellation,
        )?;
        Ok(node.id().map_or(Value::Null, |id| json!(id.get())))
    }

    fn ast_range(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let node = resolve_node(
            snapshot.document(&path).expect("validated document"),
            object,
            cancellation,
        )?;
        Ok(range_value(node.range()))
    }

    fn ast_syntax_kind(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let node = resolve_node(
            snapshot.document(&path).expect("validated document"),
            object,
            cancellation,
        )?;
        Ok(syntax_kind_value(node.syntax_kind()))
    }

    fn ast_node_kind(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let node = resolve_node(
            snapshot.document(&path).expect("validated document"),
            object,
            cancellation,
        )?;
        Ok(node
            .node_kind()
            .map_or(Value::Null, |kind| json!(format!("{kind:?}"))))
    }

    fn ast_is(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let predicate = require_str(object, "predicate")?;
        let (snapshot, path) = self.ast_document(object)?;
        let node = resolve_node(
            snapshot.document(&path).expect("validated document"),
            object,
            cancellation,
        )?;
        let kind = node.syntax_kind();
        let matches = match predicate {
            "token" => public_ast::is::is_token(kind),
            "node" => public_ast::is::is_node(kind),
            "keyword" => public_ast::is::is_keyword(kind),
            "statement" => public_ast::is::is_statement(kind),
            "expression" => public_ast::is::is_expression(kind),
            "typeNode" => public_ast::is::is_type_node(kind),
            "declaration" => public_ast::is::is_declaration(kind),
            "literal" => public_ast::is::is_literal(kind),
            other => {
                return Err(ApiError::InvalidParams(format!(
                    "predicate must be token, node, keyword, statement, expression, typeNode, declaration, or literal; got {other}"
                )));
            }
        };
        Ok(json!(matches))
    }

    fn ast_factory(
        &self,
        params: Option<&Value>,
        result: FactoryResult,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        let original = resolve_node(document, object, cancellation)?;
        let range = require_named_range(object, "range")?;
        validate_source_range(document, range)?;
        match result {
            FactoryResult::Create => {
                create_node_value(original, require_node_id(object, "id")?, range)
            }
            FactoryResult::Update | FactoryResult::AsNode | FactoryResult::IntoOwned => {
                update_node_value(
                    original,
                    require_node_id(object, "changedId")?,
                    range,
                    result,
                )
            }
        }
    }

    fn ast_text_of_range(&self, params: Option<&Value>) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let range = require_named_range(object, "range")?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        public_ast::utils::text_of_range(document.source().source_text(), range)
            .map(|text| json!(text))
            .ok_or_else(|| ApiError::InvalidParams("range is outside the source text".to_owned()))
    }

    fn ast_node_text(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        let node = resolve_node(document, object, cancellation)?;
        public_ast::utils::node_text(document.source().source_text(), node)
            .map(|text| json!(text))
            .ok_or_else(|| {
                ApiError::InvalidParams("node range is outside the source text".to_owned())
            })
    }

    fn ast_contains_range(&self, params: Option<&Value>) -> Result<Value, ApiError> {
        self.compiler()?;
        let object = params_object(params)?;
        let outer = require_named_range(object, "outer")?;
        let inner = require_named_range(object, "inner")?;
        Ok(json!(public_ast::utils::contains_range(outer, inner)))
    }

    fn ast_contains_position(&self, params: Option<&Value>) -> Result<Value, ApiError> {
        self.compiler()?;
        let object = params_object(params)?;
        let range = require_named_range(object, "range")?;
        let position = require_position(object)?;
        Ok(json!(public_ast::utils::contains_position(range, position)))
    }

    fn ast_narrowest_containing(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let position = require_position(object)?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        let nodes = collect_nodes(NodeRef::SourceFile(document.source()), cancellation)?;
        Ok(public_ast::utils::narrowest_containing(nodes, position)
            .map_or(Value::Null, node_projection))
    }

    fn ast_scan(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (source_id, script_kind, text) = if let Some(text) = object.get("text") {
            let text = text
                .as_str()
                .ok_or_else(|| ApiError::InvalidParams("text must be a string".to_owned()))?;
            (
                SourceId::new(require_optional_u32(object, "sourceId", 0)?),
                require_script_kind(object)?,
                text.to_owned(),
            )
        } else {
            let (snapshot, path) = self.ast_document(object)?;
            let document = snapshot.document(&path).expect("validated document");
            (
                document.source().source_id(),
                document.source().script_kind(),
                document.source().source_text().as_str().to_owned(),
            )
        };
        let source =
            SourceText::new(text).map_err(|error| ApiError::InvalidParams(error.to_string()))?;
        let scanned = bamts_compiler::scanner::scan_with_cancel(
            source_id,
            script_kind,
            Arc::new(source),
            cancellation.clone(),
        )
        .map_err(|_| ApiError::Cancelled)?;
        let product = scanned.product();
        let mut tokens: Vec<Value> = product
            .tokens()
            .iter()
            .map(|token| scanner_token_value(product, token))
            .collect();
        tokens.push(scanner_token_value(product, product.eof()));
        Ok(json!({
            "sourceId": product.source_id().get(),
            "scriptKind": format!("{:?}", product.script_kind()),
            "tokens": tokens,
            "diagnosticCount": scanned.diagnostics().len(),
        }))
    }

    fn ast_visit_source_file(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        Ok(Value::Array(
            collect_nodes(NodeRef::SourceFile(document.source()), cancellation)?
                .into_iter()
                .map(node_projection)
                .collect(),
        ))
    }

    fn ast_visit_node(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        let node = resolve_node(document, object, cancellation)?;
        Ok(Value::Array(
            collect_nodes(node, cancellation)?
                .into_iter()
                .map(node_projection)
                .collect(),
        ))
    }

    fn ast_clone(
        &self,
        params: Option<&Value>,
        replacement_id: Option<NodeIdReader>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let (snapshot, path) = self.ast_document(object)?;
        let document = snapshot.document(&path).expect("validated document");
        let node = resolve_node(document, object, cancellation)?;
        clone_node_value(
            node,
            replacement_id.map(|read| read(object, "id")).transpose()?,
        )
    }

    /// Runs one already-shaped CLI command through the existing driver after
    /// routing every source input through the initialized service filesystem.
    fn execute(
        &self,
        params: Option<&Value>,
        cancellation: &CancellationToken,
    ) -> Result<Value, ApiError> {
        let compiler = self.compiler()?;
        let object = params_object(params)?;
        let raw = object
            .get("args")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                ApiError::InvalidParams("args must be an array of strings".to_owned())
            })?;
        let mut argv = Vec::with_capacity(raw.len());
        for token in raw {
            let token = token.as_str().ok_or_else(|| {
                ApiError::InvalidParams("args must contain only strings".to_owned())
            })?;
            argv.push(token.to_owned());
        }
        let mut args = parse_args(&argv)
            .map_err(|error| ApiError::InvalidParams(format!("argv rejected: {error}")))?;
        let normalize = |path: &str| {
            compiler
                .filesystem
                .normalize(Path::new(path))
                .map(|path| path_text(&path))
                .map_err(|error| {
                    if error.kind() == io::ErrorKind::PermissionDenied {
                        ApiError::RootConfinement(error.to_string())
                    } else {
                        ApiError::InvalidParams(error.to_string())
                    }
                })
        };
        args.entrypoint = args.entrypoint.as_deref().map(normalize).transpose()?;
        args.extra_inputs = args
            .extra_inputs
            .iter()
            .map(|path| normalize(path))
            .collect::<Result<Vec<_>, _>>()?;
        args.output.file = args.output.file.as_deref().map(normalize).transpose()?;
        args.output.dir = args.output.dir.as_deref().map(normalize).transpose()?;
        let context =
            ExecutionContext::new(compiler.filesystem.root(), std::env::vars_os().collect())
                .map_err(|error| driver_error(&error))?;
        match driver::execute_in_context_with_cancel(&args, &context, cancellation.clone()) {
            Ok(outcome) => Ok(json!({
                "stdout": String::from_utf8_lossy(&outcome.stdout),
                "stderr": String::from_utf8_lossy(&outcome.stderr),
                "exitCode": outcome.exit_code,
            })),
            Err(error) => Err(driver_error(&error)),
        }
    }

    fn explain(params: Option<&Value>) -> Result<Value, ApiError> {
        let object = params_object(params)?;
        let rule = require_str(object, "rule")?;
        crate::args::explain_rule(rule)
            .map(|explanation| json!({ "rule": rule, "explanation": explanation }))
            .map_err(|error| ApiError::InvalidParams(error.to_string()))
    }
}

#[derive(Clone, Copy)]
enum FactoryResult {
    Create,
    Update,
    AsNode,
    IntoOwned,
}

struct FindNode<'ast> {
    id: NodeId,
    cancel: &'ast CancellationToken,
    cancelled: bool,
}

impl<'ast> public_ast::visitor::Visitor<'ast> for FindNode<'ast> {
    type Break = NodeRef<'ast>;

    fn visit(&mut self, node: NodeRef<'ast>) -> ControlFlow<Self::Break> {
        if self.cancel.is_cancelled() {
            self.cancelled = true;
            return ControlFlow::Break(node);
        }
        if node.id() == Some(self.id) {
            ControlFlow::Break(node)
        } else {
            ControlFlow::Continue(())
        }
    }
}

struct CollectNodes<'ast> {
    nodes: Vec<NodeRef<'ast>>,
    cancel: &'ast CancellationToken,
    cancelled: bool,
}

impl<'ast> public_ast::visitor::Visitor<'ast> for CollectNodes<'ast> {
    type Break = ();

    fn visit(&mut self, node: NodeRef<'ast>) -> ControlFlow<Self::Break> {
        if self.cancel.is_cancelled() {
            self.cancelled = true;
            return ControlFlow::Break(());
        }
        self.nodes.push(node);
        ControlFlow::Continue(())
    }
}

fn collect_nodes<'ast>(
    root: NodeRef<'ast>,
    cancel: &'ast CancellationToken,
) -> Result<Vec<NodeRef<'ast>>, ApiError> {
    let mut collector = CollectNodes {
        nodes: Vec::new(),
        cancel,
        cancelled: false,
    };
    let _ = public_ast::visitor::visit_node(root, &mut collector);
    if collector.cancelled {
        Err(ApiError::Cancelled)
    } else {
        Ok(collector.nodes)
    }
}

fn find_node<'ast>(
    document: &'ast DocumentSnapshot,
    id: NodeId,
    cancel: &'ast CancellationToken,
) -> Result<Option<NodeRef<'ast>>, ApiError> {
    let mut finder = FindNode {
        id,
        cancel,
        cancelled: false,
    };
    let result = match public_ast::visitor::visit_source_file(document.source(), &mut finder) {
        ControlFlow::Break(node) => Some(node),
        ControlFlow::Continue(()) => None,
    };
    if finder.cancelled {
        Err(ApiError::Cancelled)
    } else {
        Ok(result)
    }
}

fn resolve_node<'a>(
    document: &'a DocumentSnapshot,
    object: &Map<String, Value>,
    cancellation: &'a CancellationToken,
) -> Result<NodeRef<'a>, ApiError> {
    if object.contains_key("nodeId") {
        let id = require_node_id(object, "nodeId")?;
        return find_node(document, id, cancellation)?.ok_or_else(|| {
            ApiError::InvalidParams(format!(
                "nodeId {} is not in the document snapshot",
                id.get()
            ))
        });
    }
    if object.contains_key("position") {
        let position = require_position(object)?;
        let nodes = collect_nodes(NodeRef::SourceFile(document.source()), cancellation)?;
        return public_ast::utils::narrowest_containing(nodes, position).ok_or_else(|| {
            ApiError::InvalidParams(format!(
                "position {} is not contained by an AST node",
                position.get()
            ))
        });
    }
    cancellation.check().map_err(|_| ApiError::Cancelled)?;
    Ok(NodeRef::SourceFile(document.source()))
}

fn node_projection(node: NodeRef<'_>) -> Value {
    json!({
        "id": node.id().map(NodeId::get),
        "range": range_value(node.range()),
        "syntaxKind": syntax_kind_value(node.syntax_kind()),
        "nodeKind": node.node_kind().map(|kind| format!("{kind:?}")),
    })
}

fn syntax_kind_value(kind: SyntaxKind) -> Value {
    match kind {
        SyntaxKind::Node(kind) => json!({ "category": "node", "kind": format!("{kind:?}") }),
        SyntaxKind::Token(kind) => json!({ "category": "token", "kind": format!("{kind:?}") }),
    }
}

fn require_node_id(object: &Map<String, Value>, key: &str) -> Result<NodeId, ApiError> {
    let value = require_u64(object, key)?;
    let value = u32::try_from(value)
        .map_err(|_| ApiError::InvalidParams(format!("{key} exceeds the node-id space")))?;
    Ok(NodeId::new(value))
}

fn require_optional_u32(
    object: &Map<String, Value>,
    key: &str,
    default: u32,
) -> Result<u32, ApiError> {
    match object.get(key) {
        None => Ok(default),
        Some(value) => {
            let value = value.as_u64().ok_or_else(|| {
                ApiError::InvalidParams(format!("{key} must be a non-negative integer"))
            })?;
            u32::try_from(value)
                .map_err(|_| ApiError::InvalidParams(format!("{key} exceeds the u32 range")))
        }
    }
}

fn require_named_range(object: &Map<String, Value>, key: &str) -> Result<TextRange, ApiError> {
    let range = object
        .get(key)
        .and_then(Value::as_object)
        .ok_or_else(|| ApiError::InvalidParams(format!("{key} must be a range object")))?;
    let start = require_u64(range, "start")?;
    let end = require_u64(range, "end")?;
    let start = usize::try_from(start)
        .map_err(|_| ApiError::InvalidParams(format!("{key}.start exceeds this platform")))?;
    let end = usize::try_from(end)
        .map_err(|_| ApiError::InvalidParams(format!("{key}.end exceeds this platform")))?;
    TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end))
        .map_err(|error| ApiError::InvalidParams(error.to_string()))
}

fn validate_source_range(document: &DocumentSnapshot, range: TextRange) -> Result<(), ApiError> {
    public_ast::utils::text_of_range(document.source().source_text(), range)
        .map(|_| ())
        .ok_or_else(|| ApiError::InvalidParams("range is outside the source text".to_owned()))
}

fn require_script_kind(object: &Map<String, Value>) -> Result<ScriptKind, ApiError> {
    match object
        .get("scriptKind")
        .and_then(Value::as_str)
        .unwrap_or("TypeScript")
    {
        "JavaScript" | "js" => Ok(ScriptKind::JavaScript),
        "JavaScriptReact" | "jsx" => Ok(ScriptKind::JavaScriptReact),
        "TypeScript" | "ts" => Ok(ScriptKind::TypeScript),
        "TypeScriptReact" | "tsx" => Ok(ScriptKind::TypeScriptReact),
        "Json" | "json" => Ok(ScriptKind::Json),
        other => Err(ApiError::InvalidParams(format!(
            "unsupported scriptKind: {other}"
        ))),
    }
}

fn scanner_token_value(
    source: &public_ast::scanner::ScannedSource,
    token: &bamts_compiler::syntax::Token,
) -> Value {
    json!({
        "kind": format!("{:?}", token.kind()),
        "range": range_value(token.range()),
        "text": source.token_text(token),
        "missing": token.is_missing(),
    })
}

fn owned_node_projection<T: NodeData>(node: &Node<T>) -> Value {
    json!({
        "id": node.id().get(),
        "range": range_value(node.range()),
        "syntaxKind": syntax_kind_value(node.syntax_kind()),
        "nodeKind": format!("{:?}", node.kind()),
    })
}

fn create_from_node<T>(node: &Node<T>, id: NodeId, range: TextRange) -> Value
where
    T: NodeData + Clone,
{
    let created = public_ast::factory::create_node(id, range, node.data().clone());
    owned_node_projection(&created)
}

fn updated_from_node<T>(
    node: &Node<T>,
    id: NodeId,
    range: TextRange,
    result: FactoryResult,
) -> Value
where
    T: NodeData + Clone + Eq,
{
    let updated = public_ast::factory::update_node(node, id, range, node.data().clone());
    match result {
        FactoryResult::Update => {
            json!({ "original": updated.is_original(), "node": owned_node_projection(updated.as_node()) })
        }
        FactoryResult::AsNode => owned_node_projection(updated.as_node()),
        FactoryResult::IntoOwned => updated
            .into_owned()
            .as_ref()
            .map_or(Value::Null, owned_node_projection),
        FactoryResult::Create => unreachable!("create uses create_from_node"),
    }
}

fn cloned_from_node<T>(node: &Node<T>, id: Option<NodeId>) -> Value
where
    T: NodeData + Clone,
{
    let cloned = id.map_or_else(
        || public_ast::clone::clone_node(node),
        |id| public_ast::clone::clone_node_with_id(node, id),
    );
    owned_node_projection(&cloned)
}

macro_rules! canonical_node_match {
    ($node:expr, $operation:ident ( $($argument:expr),* $(,)? )) => {
        match $node {
            NodeRef::Statement(node) => $operation(node, $($argument),*),
            NodeRef::Expression(node) => $operation(node, $($argument),*),
            NodeRef::Identifier(node) => $operation(node, $($argument),*),
            NodeRef::StringLiteral(node) => $operation(node, $($argument),*),
            NodeRef::TypeNode(node) => $operation(node, $($argument),*),
            NodeRef::BindingPattern(node) => $operation(node, $($argument),*),
            NodeRef::AssignmentTarget(node) => $operation(node, $($argument),*),
            NodeRef::Parameter(node) => $operation(node, $($argument),*),
            NodeRef::VariableDeclarator(node) => $operation(node, $($argument),*),
            NodeRef::Block(node) => $operation(node, $($argument),*),
            NodeRef::ClassMember(node) => $operation(node, $($argument),*),
            NodeRef::ObjectMember(node) => $operation(node, $($argument),*),
            NodeRef::ImportSpecifier(node) => $operation(node, $($argument),*),
            NodeRef::ExportSpecifier(node) => $operation(node, $($argument),*),
            NodeRef::TypeAnnotation(node) => $operation(node, $($argument),*),
            NodeRef::TypeParameter(node) => $operation(node, $($argument),*),
            NodeRef::TypeMember(node) => $operation(node, $($argument),*),
            NodeRef::CatchClause(node) => $operation(node, $($argument),*),
            NodeRef::SwitchCase(node) => $operation(node, $($argument),*),
            NodeRef::EnumMember(node) => $operation(node, $($argument),*),
            NodeRef::Decorator(node) => $operation(node, $($argument),*),
            NodeRef::JsxOpeningElement(node) => $operation(node, $($argument),*),
            NodeRef::JsxClosingElement(node) => $operation(node, $($argument),*),
            NodeRef::JsxAttribute(node) => $operation(node, $($argument),*),
            NodeRef::JsxSpreadAttribute(node) => $operation(node, $($argument),*),
            NodeRef::JsxExpressionContainer(node) => $operation(node, $($argument),*),
            NodeRef::JsxSpreadChild(node) => $operation(node, $($argument),*),
            NodeRef::JsxText(node) => $operation(node, $($argument),*),
            NodeRef::SourceFile(_) | NodeRef::Token(_) => {
                return Err(ApiError::InvalidParams(
                    "factory and clone operations require a canonical non-root node".to_owned(),
                ));
            }
        }
    };
}

fn create_node_value(node: NodeRef<'_>, id: NodeId, range: TextRange) -> Result<Value, ApiError> {
    Ok(canonical_node_match!(node, create_from_node(id, range)))
}

fn update_node_value(
    node: NodeRef<'_>,
    id: NodeId,
    range: TextRange,
    result: FactoryResult,
) -> Result<Value, ApiError> {
    Ok(canonical_node_match!(
        node,
        updated_from_node(id, range, result)
    ))
}

fn clone_node_value(node: NodeRef<'_>, id: Option<NodeId>) -> Result<Value, ApiError> {
    Ok(canonical_node_match!(node, cloned_from_node(id)))
}

/// The ten mandatory service methods, reported by `initialize`.
pub(crate) const SERVICE_METHODS: [&str; 10] = [
    "service/open",
    "service/update",
    "service/close",
    "service/snapshot",
    "service/completions",
    "service/definition",
    "service/quickInfo",
    "service/references",
    "service/rename",
    "service/diagnostics",
];

fn driver_error(error: &DriverError) -> ApiError {
    if matches!(error, DriverError::Cancelled) {
        return ApiError::Cancelled;
    }
    if error.is_usage_error() {
        return ApiError::InvalidParams(error.to_string());
    }
    ApiError::Service(
        error
            .rendered_diagnostic()
            .map_or_else(|| error.to_string(), ToOwned::to_owned),
    )
}

fn params_object(params: Option<&Value>) -> Result<&Map<String, Value>, ApiError> {
    params
        .and_then(Value::as_object)
        .ok_or_else(|| ApiError::InvalidParams("params must be an object".to_owned()))
}

fn optional_object(params: Option<&Value>) -> Result<Map<String, Value>, ApiError> {
    match params {
        None | Some(Value::Null) => Ok(Map::new()),
        Some(Value::Object(object)) => Ok(object.clone()),
        Some(_) => Err(ApiError::InvalidParams(
            "params must be an object".to_owned(),
        )),
    }
}

fn require_str<'a>(object: &'a Map<String, Value>, key: &str) -> Result<&'a str, ApiError> {
    object
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| ApiError::InvalidParams(format!("{key} must be a string")))
}

fn require_u64(object: &Map<String, Value>, key: &str) -> Result<u64, ApiError> {
    object
        .get(key)
        .and_then(Value::as_u64)
        .ok_or_else(|| ApiError::InvalidParams(format!("{key} must be a non-negative integer")))
}

fn require_position(object: &Map<String, Value>) -> Result<Utf16Pos, ApiError> {
    let offset = require_u64(object, "position")?;
    let offset = usize::try_from(offset)
        .map_err(|_| ApiError::InvalidParams("position exceeds this platform".to_owned()))?;
    Ok(Utf16Pos::new(offset))
}

fn wants_async(object: &Map<String, Value>) -> bool {
    object.get("async").and_then(Value::as_bool) == Some(true)
}

pub(crate) fn path_text(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

fn range_value(range: TextRange) -> Value {
    json!({ "start": range.start().get(), "end": range.end().get() })
}

fn document_value(path: &Path, version: u64, open: bool) -> Value {
    json!({ "path": path_text(path), "version": version, "open": open })
}

fn snapshot_value(snapshot: &ServiceSnapshot) -> Value {
    let documents: Vec<Value> = snapshot
        .documents()
        .map(|document| document_value(document.path(), document.version(), document.is_open()))
        .collect();
    json!({ "documents": documents })
}

fn completion_value(completion: &Completion) -> Value {
    json!({
        "name": completion.name,
        "kind": symbol_kind_name(completion.kind),
        "replacement": range_value(completion.replacement),
    })
}

fn location_value(location: &Location) -> Value {
    json!({ "path": path_text(&location.path), "range": range_value(location.range) })
}

fn quick_info_value(info: &QuickInfo) -> Value {
    json!({
        "name": info.name,
        "kind": quick_info_kind_name(info.kind),
        "typeDisplay": info.type_display,
        "display": info.display(),
        "range": range_value(info.range),
    })
}

fn rename_value(result: &RenameResult) -> Value {
    let edits: Vec<Value> = result
        .edit
        .edits
        .iter()
        .map(|edit| {
            json!({
                "path": path_text(&edit.path),
                "range": range_value(edit.range),
                "replacement": edit.replacement,
            })
        })
        .collect();
    json!({ "symbol": result.symbol, "edits": edits })
}

fn diagnostic_value(entry: &DiagnosticEntry) -> Value {
    json!({
        "path": path_text(&entry.path),
        "range": range_value(entry.range),
        "code": entry.code,
        "severity": severity_name(entry.severity),
        "message": entry.message,
    })
}

const fn severity_name(severity: DiagnosticSeverity) -> &'static str {
    match severity {
        DiagnosticSeverity::Error => "error",
        DiagnosticSeverity::Warning => "warning",
    }
}

const fn quick_info_kind_name(kind: QuickInfoKind) -> &'static str {
    match kind {
        QuickInfoKind::Symbol(kind) => symbol_kind_name(kind),
        QuickInfoKind::Property => "property",
    }
}

const fn symbol_kind_name(kind: SymbolKind) -> &'static str {
    match kind {
        SymbolKind::IntrinsicValue => "intrinsicValue",
        SymbolKind::IntrinsicType => "intrinsicType",
        SymbolKind::Variable(VariableKind::Var) => "var",
        SymbolKind::Variable(VariableKind::Let) => "let",
        SymbolKind::Variable(VariableKind::Const) => "const",
        SymbolKind::Variable(VariableKind::Using) => "using",
        SymbolKind::Variable(VariableKind::AwaitUsing) => "awaitUsing",
        SymbolKind::Function => "function",
        SymbolKind::Parameter => "parameter",
        SymbolKind::Class => "class",
        SymbolKind::Interface => "interface",
        SymbolKind::TypeAlias => "typeAlias",
        SymbolKind::Enum => "enum",
        SymbolKind::EnumMember => "enumMember",
        SymbolKind::TypeParameter => "typeParameter",
        SymbolKind::Import => "import",
        SymbolKind::Namespace => "namespace",
    }
}
