use std::{
    fs,
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use super::{
    ExecutableProgram, JsxRoutingDecision, ModuleEdgeKind, ModuleTarget, ProgramLoadError,
    ProgramLoader, ProgramLowerErrorKind, ProgramLowerPhase, ProgramOutputKind,
    ReferenceDirectiveKind, ResolutionFlavor, ResolutionMode, ResolvedProgram, lower_program,
    lower_program_with_cancel,
};
use crate::checker::ProgramCheckOptions;
use crate::{
    lower::LowerOptions,
    pipeline::{FrontendMode, compile_program_frontend},
    project::{ProjectConfig, ProjectRoot},
    service::filesystem::{FileMetadata, FileSystem, FileSystemError, OsFileSystem},
    source::JsxEmit,
};
use bamts_bytecode::{
    BindingId, BindingKind, EcmaString, EdgeId, EdgeKind, EdgeTarget, ExportSource, Instruction,
    ProgramModule, ProgramVerifyErrorKind, ResolvedExport, Verified,
};
use bamts_cancel::CancellationToken;

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "bamts-program-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    fn write(&self, path: &str, source: &str) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn loader(&self) -> ProgramLoader {
        self.loader_with_config("{}")
    }

    fn loader_with_config(&self, config_source: &str) -> ProgramLoader {
        let root = ProjectRoot::new(fs::canonicalize(&self.0).unwrap()).unwrap();
        let config =
            ProjectConfig::parse(&root, self.0.join("tsconfig.json"), config_source).unwrap();
        ProgramLoader::new(&root, config.options()).unwrap()
    }
}
struct CountingFileSystem {
    inner: OsFileSystem,
    shared: PathBuf,
    shared_reads: AtomicU64,
    total_reads: AtomicU64,
}

impl CountingFileSystem {
    fn new(root: &Path, shared: &Path) -> Self {
        let inner = OsFileSystem::new(root).unwrap();
        let shared = inner.normalize(shared).unwrap();
        Self {
            inner,
            shared,
            shared_reads: AtomicU64::new(0),
            total_reads: AtomicU64::new(0),
        }
    }
}

impl FileSystem for CountingFileSystem {
    fn normalize(&self, path: &Path) -> Result<PathBuf, FileSystemError> {
        self.inner.normalize(path)
    }

    fn read(&self, path: &Path) -> Result<String, FileSystemError> {
        let path = self.inner.normalize(path)?;
        self.total_reads.fetch_add(1, Ordering::Relaxed);
        if path == self.shared {
            self.shared_reads.fetch_add(1, Ordering::Relaxed);
        }
        self.inner.read(&path)
    }

    fn metadata(&self, path: &Path) -> Result<FileMetadata, FileSystemError> {
        self.inner.metadata(path)
    }

    fn read_dir(&self, path: &Path) -> Result<Vec<PathBuf>, FileSystemError> {
        self.inner.read_dir(path)
    }
}
struct CancellingFileSystem {
    inner: OsFileSystem,
    cancel: CancellationToken,
    cancel_at: u64,
    reads: AtomicU64,
}

impl CancellingFileSystem {
    fn new(root: &Path, cancel: CancellationToken, cancel_at: u64) -> Self {
        Self {
            inner: OsFileSystem::new(root).unwrap(),
            cancel,
            cancel_at,
            reads: AtomicU64::new(0),
        }
    }
}

impl FileSystem for CancellingFileSystem {
    fn normalize(&self, path: &Path) -> Result<PathBuf, FileSystemError> {
        self.inner.normalize(path)
    }

    fn read(&self, path: &Path) -> Result<String, FileSystemError> {
        let source = self.inner.read(path)?;
        let reads = self.reads.fetch_add(1, Ordering::Relaxed) + 1;
        if reads == self.cancel_at {
            self.cancel.cancel();
        }
        Ok(source)
    }

    fn metadata(&self, path: &Path) -> Result<FileMetadata, FileSystemError> {
        self.inner.metadata(path)
    }

    fn read_dir(&self, path: &Path) -> Result<Vec<PathBuf>, FileSystemError> {
        self.inner.read_dir(path)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn lower_fixture(fixture: &Fixture, entrypoint: &str) -> ExecutableProgram {
    let resolved = fixture.loader().load(entrypoint).unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    lower_program(
        &resolved,
        &frontend,
        LowerOptions {
            javascript_compatibility: true,
            ..LowerOptions::default()
        },
    )
    .unwrap()
}
#[test]
fn pre_cancelled_load_preserves_typed_path_context() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "export const value = 1;");
    let cancel = CancellationToken::new();
    cancel.cancel();

    let error = fixture
        .loader()
        .load_with_cancel("main.ts", &cancel)
        .expect_err("pre-cancelled loading must stop before filesystem work");
    assert!(matches!(
        error,
        ProgramLoadError::Cancelled { path, .. } if path == Path::new("main.ts")
    ));
}

#[test]
fn load_cancellation_after_read_stops_before_dependency_traversal() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import './dependency.js';");
    fixture.write("dependency.ts", "export const value = 1;");
    let cancel = CancellationToken::new();
    let root = ProjectRoot::new(fs::canonicalize(&fixture.0).unwrap()).unwrap();
    let config = ProjectConfig::parse(&root, fixture.0.join("tsconfig.json"), "{}").unwrap();
    let filesystem = Arc::new(CancellingFileSystem::new(&fixture.0, cancel.clone(), 1));
    let loader_filesystem: Arc<dyn FileSystem> = filesystem.clone();
    let loader =
        ProgramLoader::with_file_system(&root, config.options(), loader_filesystem).unwrap();

    let error = loader
        .load_with_cancel("main.ts", &cancel)
        .expect_err("cancellation after the first read must stop traversal");
    assert!(matches!(
        error,
        ProgramLoadError::Cancelled { path, .. } if path.ends_with("main.ts")
    ));
    assert_eq!(filesystem.reads.load(Ordering::Relaxed), 1);
}
#[test]
fn load_cancellation_after_package_read_retains_package_path() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import 'pkg';");
    fixture.write(
        "node_modules/pkg/package.json",
        r#"{"name":"pkg","exports":{".":"./index.ts"}}"#,
    );
    fixture.write("node_modules/pkg/index.ts", "export const value = 1;");
    let cancel = CancellationToken::new();
    let root = ProjectRoot::new(fs::canonicalize(&fixture.0).unwrap()).unwrap();
    let config = ProjectConfig::parse(&root, fixture.0.join("tsconfig.json"), "{}").unwrap();
    let filesystem = Arc::new(CancellingFileSystem::new(&fixture.0, cancel.clone(), 2));
    let loader_filesystem: Arc<dyn FileSystem> = filesystem.clone();
    let loader =
        ProgramLoader::with_file_system(&root, config.options(), loader_filesystem).unwrap();

    let error = loader
        .load_with_cancel("main.ts", &cancel)
        .expect_err("cancellation after package.json read must stop package parsing");
    assert!(matches!(
        error,
        ProgramLoadError::Cancelled { path, .. } if path.ends_with("node_modules/pkg/package.json")
    ));
    assert_eq!(filesystem.reads.load(Ordering::Relaxed), 2);
}

#[test]
fn pre_cancelled_lowering_preserves_stage_and_path_context() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "export const value = 1;");
    let resolved = fixture.loader().load("main.ts").unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let cancel = CancellationToken::new();
    cancel.cancel();

    let error = lower_program_with_cancel(&resolved, &frontend, LowerOptions::default(), &cancel)
        .expect_err("pre-cancelled lowering must stop at the frontend boundary");
    assert_eq!(error.module, resolved.entrypoint().path());
    assert_eq!(error.phase, ProgramLowerPhase::Frontend);
    assert!(matches!(error.kind, ProgramLowerErrorKind::Cancelled(_)));
}

#[test]
fn malformed_surrogate_metadata_is_a_typed_error() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "const x = 1; export { x as \"\\uD800\" };");
    let resolved = fixture.loader().load("main.ts").unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let error = lower_program(
        &resolved,
        &frontend,
        LowerOptions {
            javascript_compatibility: true,
            ..LowerOptions::default()
        },
    )
    .expect_err("ill-formed metadata must not reach host String conversion");
    assert_eq!(error.phase, ProgramLowerPhase::Metadata);
    assert_eq!(error.kind, ProgramLowerErrorKind::IllFormedMetadataString);
}

fn module_name(module: &ProgramModule<Verified>) -> String {
    match &module.code().constants()[module.name().get() as usize] {
        bamts_bytecode::Constant::String(name) => name
            .to_utf8_strict()
            .expect("compiler-produced module metadata is well-formed"),
        _ => panic!("verified module name is a string"),
    }
}

fn module<'a>(program: &'a ExecutableProgram, name: &str) -> &'a ProgramModule<Verified> {
    program
        .wire()
        .modules()
        .iter()
        .find(|module| module_name(module) == name)
        .unwrap_or_else(|| panic!("missing module {name}"))
}

fn constant_string(module: &ProgramModule<Verified>, id: bamts_bytecode::ConstantId) -> String {
    match &module.code().constants()[id.get() as usize] {
        bamts_bytecode::Constant::String(value) => value
            .to_utf8_strict()
            .expect("compiler-produced linkage metadata is well-formed"),
        _ => panic!("verified linkage constant is a string"),
    }
}

fn instructions(module: &ProgramModule<Verified>) -> impl Iterator<Item = Instruction> + '_ {
    module
        .code()
        .functions()
        .iter()
        .flat_map(|function| function.code().iter().copied())
}

fn names(program: &super::ResolvedProgram) -> Vec<&str> {
    program
        .modules()
        .iter()
        .map(|module| module.path().file_name().unwrap().to_str().unwrap())
        .collect()
}

#[test]
fn program_lowering_inlines_a_local_const_enum_member() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "const enum K { X = 2, Y = X + 3 } K.Y !== 5;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(
        !instructions(main)
            .any(|instruction| matches!(instruction, Instruction::LoadGlobal { .. }))
    );
}

#[test]
fn program_lowering_binds_a_qualified_import_equals_without_a_runtime_edge() {
    let fixture = Fixture::new();
    fixture.write(
            "main.ts",
            "declare namespace A { export namespace B { export const value: number; } } import X = A.B; const observed = X;",
        );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(main.edges().is_empty());
    let binding = main
        .bindings()
        .iter()
        .find(|binding| constant_string(main, binding.name) == "X")
        .expect("qualified import equals declares a module binding");
    assert!(matches!(binding.kind, BindingKind::Lexical));
    assert!(
        !instructions(main).any(|instruction| matches!(instruction, Instruction::Import { .. }))
    );
}

#[test]
fn program_lowering_erases_ambient_qualified_import_equals_without_load_global() {
    let fixture = Fixture::new();
    fixture.write(
            "main.ts",
            "declare namespace A { export namespace B { export const value: number; } } import X = A.B; type Alias = X;",
        );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(
        !instructions(main)
            .any(|instruction| matches!(instruction, Instruction::LoadGlobal { .. })),
        "ambient qualified import-equals must not fall back to LoadGlobal"
    );
}

#[test]
fn program_lowering_elides_a_sole_imported_const_enum_binding() {
    let fixture = Fixture::new();
    fixture.write("a.ts", "export const enum K { X = 2, Y = X + 3 }");
    fixture.write(
        "main.ts",
        "import { K } from './a.ts'; if (K.Y !== 5) throw 'incorrect';",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(main.bindings().is_empty());
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);
    assert_eq!(constant_string(main, main.edges()[0].specifier), "./a.ts");
}

#[test]
fn program_lowering_elides_only_imported_const_enum_bindings() {
    let fixture = Fixture::new();
    fixture.write(
        "a.ts",
        "export const enum K { X = 2, Y = X + 3 } export const value = 7;",
    );
    fixture.write(
        "main.ts",
        "import { K, value } from './a.ts'; if (K.Y !== 5 || value !== 7) throw 'incorrect';",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);
    assert_eq!(main.bindings().len(), 1);
    let binding = &main.bindings()[0];
    assert_eq!(constant_string(main, binding.name), "value");
    assert!(matches!(binding.kind, BindingKind::Imported { .. }));
}

#[test]
fn program_lowering_distinguishes_same_named_enum_and_value_imports() {
    let fixture = Fixture::new();
    fixture.write("enum.ts", "export const enum K { Y = 5 }");
    fixture.write("value.ts", "export const K = 7;");
    fixture.write(
            "main.ts",
            "import { K as enum_k } from './enum.ts'; import { K } from './value.ts'; if (enum_k.Y !== 5 || K !== 7) throw 'incorrect';",
        );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.bindings().len(), 1);
    let binding = &main.bindings()[0];
    assert_eq!(constant_string(main, binding.name), "K");
    assert!(matches!(binding.kind, BindingKind::Imported { .. }));
}

#[test]
fn program_lowering_retains_module_evaluation_for_elided_const_enum_imports() {
    let fixture = Fixture::new();
    fixture.write(
        "enum_dep.ts",
        "export let evaluated = 0; evaluated += 1; export const enum K { X = 1, Y = X + 2 }",
    );
    fixture.write(
        "type_dep.ts",
        "export let type_evaluated = 0; type_evaluated += 1; export const enum OnlyType { Z = 9 }",
    );
    fixture.write(
        "mixed_dep.ts",
        "export const enum MixedEnum { A = 4 } export const value = 7;",
    );
    fixture.write(
            "main.ts",
            "import { K } from './enum_dep.ts'; import type { OnlyType } from './type_dep.ts'; import { MixedEnum, value } from './mixed_dep.ts'; type Shape = K; const typed: OnlyType = 9 as OnlyType; if (value !== 7) throw 'incorrect'; typed as Shape;",
        );

    let resolved = fixture.loader().load("main.ts").unwrap();
    let runtime: Vec<_> = resolved
        .runtime_modules()
        .iter()
        .map(|module| module.path().file_name().unwrap().to_str().unwrap())
        .collect();
    assert!(
        runtime.contains(&"enum_dep.ts"),
        "non-type-only const-enum import keeps the dependency in the runtime closure"
    );
    assert!(runtime.contains(&"mixed_dep.ts"));
    assert!(
        !runtime.contains(&"type_dep.ts"),
        "import type stays outside the runtime closure"
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let enum_dep = module(&executable, "enum_dep.ts");
    let mixed_dep = module(&executable, "mixed_dep.ts");

    assert!(
        main.edges().iter().any(|edge| {
            edge.kind == EdgeKind::Static
                && constant_string(main, edge.specifier) == "./enum_dep.ts"
        }),
        "elided const-enum import retains a side-effect StaticRuntime edge"
    );
    assert!(
        main.bindings()
            .iter()
            .all(|binding| constant_string(main, binding.name) != "K"),
        "importer emits no runtime local for the const enum"
    );
    assert!(
        enum_dep
            .bindings()
            .iter()
            .all(|binding| constant_string(enum_dep, binding.name) != "K"),
        "exported const enum itself has no runtime binding"
    );
    assert!(
        enum_dep
            .bindings()
            .iter()
            .any(|binding| constant_string(enum_dep, binding.name) == "evaluated"),
        "observable top-level work in the enum module remains"
    );

    assert!(
        main.edges()
            .iter()
            .all(|edge| constant_string(main, edge.specifier) != "./type_dep.ts"),
        "import type is erased from wire edges"
    );
    let provenance = executable
        .provenance()
        .iter()
        .find(|item| item.source().path().ends_with("main.ts"))
        .expect("main provenance");
    assert!(
        provenance
            .type_only_edges()
            .any(|edge| edge.specifier() == "./type_dep.ts")
    );

    let mixed_edges: Vec<_> = main
        .edges()
        .iter()
        .filter(|edge| constant_string(main, edge.specifier) == "./mixed_dep.ts")
        .collect();
    assert_eq!(mixed_edges.len(), 1);
    assert_eq!(mixed_edges[0].kind, EdgeKind::Static);
    assert_eq!(
        main.bindings()
            .iter()
            .filter(|binding| matches!(binding.kind, BindingKind::Imported { .. }))
            .count(),
        1
    );
    let value = main
        .bindings()
        .iter()
        .find(|binding| constant_string(main, binding.name) == "value")
        .expect("mixed import keeps the real value binding once");
    assert!(matches!(value.kind, BindingKind::Imported { .. }));
    assert!(
        main.bindings()
            .iter()
            .all(|binding| constant_string(main, binding.name) != "MixedEnum")
    );
    assert!(
        mixed_dep
            .bindings()
            .iter()
            .all(|binding| constant_string(mixed_dep, binding.name) != "MixedEnum")
    );
}

#[test]
fn program_lowering_binds_export_star_namespace_as_live_export_metadata() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 7;");
    fixture.write("main.ts", "export * as ns from './dep.ts';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);

    let binding = main
        .bindings()
        .iter()
        .find(|binding| constant_string(main, binding.name) == "*namespace:ns*")
        .expect("export * as ns keeps a synthetic namespace binding");
    assert!(
        matches!(binding.kind, BindingKind::Namespace { edge } if edge == EdgeId::new(0)),
        "namespace export binds the existing module namespace object"
    );

    let export = main
        .exports()
        .iter()
        .find(|export| constant_string(main, export.name) == "ns")
        .expect("export * as ns exposes the named export");
    assert!(
        matches!(export.source, ExportSource::Local(binding) if constant_string(main, main.bindings()[binding.get() as usize].name) == "*namespace:ns*"),
        "named namespace export points at the namespace binding"
    );
}

#[test]
fn program_lowering_keeps_static_imports_live_without_snapshot_opcodes() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export let value = 1; value = 2;");
    fixture.write(
        "main.ts",
        "import { value as observed } from './dep.js'; export { observed };",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);
    let binding = main
        .bindings()
        .iter()
        .find(|binding| constant_string(main, binding.name) == "observed")
        .unwrap();
    assert!(matches!(binding.kind, BindingKind::Imported { .. }));
    assert!(!instructions(main).any(|instruction| matches!(
        instruction,
        Instruction::Import { .. } | Instruction::GetProperty { .. } | Instruction::Export { .. }
    )));

    let main_id = executable.wire().entry();
    let export = main
        .exports()
        .iter()
        .find(|export| constant_string(main, export.name) == "observed")
        .unwrap();
    assert!(matches!(export.source, ExportSource::Local(_)));
    assert!(matches!(
        executable.wire().resolve_export(main_id, &EcmaString::encode("observed")),
        Some(ResolvedExport::Local { module, .. })
            if module != main_id
    ));
}

#[test]
fn program_lowering_links_external_import_equals_as_one_namespace_binding() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "import util = require('node:util'); util.parseArgs;",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].target, EdgeTarget::External);
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);
    assert_eq!(main.bindings().len(), 1);
    let binding = &main.bindings()[0];
    assert_eq!(constant_string(main, binding.name), "util");
    assert!(matches!(
        binding.kind,
        BindingKind::Namespace { edge } if edge == EdgeId::new(0)
    ));
    assert!(!instructions(main).any(|instruction| matches!(
        instruction,
        Instruction::Import { .. } | Instruction::Export { .. }
    )));
}

#[test]
fn program_lowering_links_local_import_equals_as_one_namespace_binding() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 7;");
    fixture.write("main.ts", "import dep = require('./dep.js'); dep.value;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert!(matches!(main.edges()[0].target, EdgeTarget::Local(_)));
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);
    assert_eq!(main.bindings().len(), 1);
    let binding = &main.bindings()[0];
    assert_eq!(constant_string(main, binding.name), "dep");
    assert!(matches!(
        binding.kind,
        BindingKind::Namespace { edge } if edge == EdgeId::new(0)
    ));
}

#[test]
fn program_lowering_links_local_export_assignment_import_equals_as_default_binding() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export = { value: 7 };");
    fixture.write("main.ts", "import dep = require('./dep.js'); dep;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert!(matches!(main.edges()[0].target, EdgeTarget::Local(_)));
    assert_eq!(main.edges()[0].kind, EdgeKind::Static);
    assert_eq!(main.bindings().len(), 1);
    let binding = &main.bindings()[0];
    assert_eq!(constant_string(main, binding.name), "dep");
    assert!(matches!(
        binding.kind,
        BindingKind::Imported { edge, name }
            if edge == EdgeId::new(0) && constant_string(main, name) == "default"
    ));
}

#[test]
fn program_lowering_records_namespace_imports() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1; export default 2;");
    fixture.write(
        "main.ts",
        "import fallback, * as namespace from './dep.js'; fallback; namespace.value;",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(main.bindings().iter().any(|binding| {
        constant_string(main, binding.name) == "namespace"
            && matches!(binding.kind, BindingKind::Namespace { .. })
    }));
    assert!(main.bindings().iter().any(|binding| {
        constant_string(main, binding.name) == "fallback"
            && matches!(
                binding.kind,
                BindingKind::Imported { name, .. }
                    if constant_string(main, name) == "default"
            )
    }));
}

#[test]
fn program_lowering_resolves_alias_reexports() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const original = 1;");
    fixture.write("main.ts", "export { original as renamed } from './dep.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let export = main
        .exports()
        .iter()
        .find(|export| constant_string(main, export.name) == "renamed")
        .unwrap();
    assert!(matches!(export.source, ExportSource::Indirect { .. }));
    assert!(matches!(
        executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("renamed")),
        Some(ResolvedExport::Local { module, .. })
            if module != executable.wire().entry()
    ));
}

#[test]
fn program_lowering_omits_ambiguous_star_exports() {
    let fixture = Fixture::new();
    fixture.write(
        "a.ts",
        "export const collision = 1; export const onlyA = 1;",
    );
    fixture.write(
        "b.ts",
        "export const collision = 2; export const onlyB = 2;",
    );
    fixture.write("main.ts", "export * from './a.js'; export * from './b.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let names: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert!(names.iter().any(|name| name == "onlyA"));
    assert!(names.iter().any(|name| name == "onlyB"));
    assert!(!names.iter().any(|name| name == "collision"));
}

#[test]
fn program_lowering_keeps_diamond_star_reexports_unambiguous() {
    let fixture = Fixture::new();
    fixture.write("a.ts", "export const value = 1;");
    fixture.write("b.ts", "export { value } from './a.js';");
    fixture.write("main.ts", "export * from './a.js'; export * from './b.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(
        main.exports()
            .iter()
            .filter(|export| constant_string(main, export.name) == "value")
            .count(),
        1
    );
    assert!(
        executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
            .is_some()
    );
}

#[test]
fn program_lowering_canonicalizes_external_reexport_identity() {
    let fixture = Fixture::new();
    fixture.write("a.ts", "export { readFile } from 'node:fs';");
    fixture.write("b.ts", "export { readFile } from 'node:fs';");
    fixture.write("main.ts", "export * from './a.js'; export * from './b.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(
        main.exports()
            .iter()
            .filter(|export| constant_string(main, export.name) == "readFile")
            .count(),
        1
    );
    assert!(matches!(
        executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("readFile")),
        Some(ResolvedExport::External { .. })
    ));
}

#[test]
fn program_lowering_discovers_transitive_star_exports() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export let value = 1;");
    fixture.write("mid.ts", "export * from './dep.js';");
    fixture.write("main.ts", "export * from './mid.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let export = main
        .exports()
        .iter()
        .find(|export| constant_string(main, export.name) == "value")
        .unwrap();
    assert!(matches!(export.source, ExportSource::Indirect { .. }));
    let resolved = executable
        .wire()
        .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
        .expect("transitive star export must resolve");
    let ResolvedExport::Local {
        module: resolved, ..
    } = resolved
    else {
        panic!("transitive star export must stay local");
    };
    assert_eq!(
        module_name(&executable.wire().modules()[resolved.get() as usize]),
        "dep.ts"
    );
}

#[test]
fn program_lowering_preserves_explicit_shadowing_over_star_reexports() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;");
    fixture.write(
        "main.ts",
        "export { value as shadowed } from './dep.js'; export * from './dep.js';",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(main.exports().iter().any(|export| {
        constant_string(main, export.name) == "shadowed"
            && matches!(export.source, ExportSource::Indirect { .. })
    }));
    assert_eq!(
        main.exports()
            .iter()
            .filter(|export| constant_string(main, export.name) == "value")
            .count(),
        1
    );
    assert!(
        executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
            .is_some()
    );
}

#[test]
fn program_lowering_downstream_star_prefers_explicit_over_star_collision() {
    let fixture = Fixture::new();
    fixture.write("other.ts", "export const value = 1;");
    fixture.write(
        "mid.ts",
        "export const value = 2; export * from './other.js';",
    );
    fixture.write("main.ts", "export * from './mid.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(
        main.exports()
            .iter()
            .filter(|export| constant_string(main, export.name) == "value")
            .count(),
        1
    );
    let resolved = executable
        .wire()
        .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
        .expect("downstream star must expose mid's explicit value unambiguously");
    let ResolvedExport::Local {
        module: resolved, ..
    } = resolved
    else {
        panic!("explicit-over-star reexport must stay local");
    };
    assert_eq!(
        module_name(&executable.wire().modules()[resolved.get() as usize]),
        "mid.ts"
    );
}

#[test]
fn program_lowering_excludes_default_from_star_reexports() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export default 1; export const named = 2;");
    fixture.write("main.ts", "export * from './dep.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let names: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert_eq!(names, ["named"]);
    assert!(
        executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("default"))
            .is_none()
    );
}

#[test]
fn program_lowering_terminates_cyclic_star_reexports_without_pollution() {
    let fixture = Fixture::new();
    fixture.write("a.ts", "export * from './b.js'; export const a = 1;");
    fixture.write("b.ts", "export * from './a.js'; export const b = 2;");
    fixture.write("main.ts", "export * from './a.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let names: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert_eq!(names, ["a", "b"]);
    for name in ["a", "b"] {
        let resolved = executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode(name))
            .expect("cyclic star graph must resolve both direct exports");
        let ResolvedExport::Local {
            module: resolved, ..
        } = resolved
        else {
            panic!("star reexport must stay local");
        };
        assert_eq!(
            module_name(&executable.wire().modules()[resolved.get() as usize]),
            format!("{name}.ts")
        );
    }
}

#[test]
fn program_lowering_star_reexports_track_live_imported_cells() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export let value = 1;");
    fixture.write(
        "mid.ts",
        "import { value } from './dep.js'; export { value };",
    );
    fixture.write("main.ts", "export * from './mid.js';");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let export = main
        .exports()
        .iter()
        .find(|export| constant_string(main, export.name) == "value")
        .unwrap();
    assert!(matches!(export.source, ExportSource::Indirect { .. }));
    let dep_index = executable
        .wire()
        .modules()
        .iter()
        .position(|candidate| module_name(candidate) == "dep.ts")
        .unwrap() as u32;
    let resolved = executable
        .wire()
        .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
        .expect("live imported cell reexport must resolve");
    let ResolvedExport::Local { module, binding } = resolved else {
        panic!("live imported cell reexport must stay local");
    };
    assert_eq!(module.get(), dep_index);
    assert_eq!(binding, BindingId::new(0));
}

#[test]
fn program_lowering_materializes_default_expression_binding() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "export default 1 + 2;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let binding_index = main
        .bindings()
        .iter()
        .position(|binding| constant_string(main, binding.name) == "*default*")
        .unwrap();
    assert_eq!(main.bindings()[binding_index].kind, BindingKind::Lexical);
    assert!(main.exports().iter().any(|export| {
        constant_string(main, export.name) == "default"
            && export.source
                == ExportSource::Local(bamts_bytecode::BindingId::new(binding_index as u32))
    }));
    assert!(
        !instructions(main).any(|instruction| matches!(instruction, Instruction::Export { .. }))
    );
}

#[test]
fn program_lowering_materializes_export_assignment_as_default_export() {
    let fixture = Fixture::new();
    fixture.write("equal.ts", "export = 1 + 2;");
    fixture.write(
        "main.ts",
        "import * as equal from './equal.ts'; import fallback from './equal.ts';",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let equal = module(&executable, "equal.ts");
    let binding_index = equal
        .bindings()
        .iter()
        .position(|binding| constant_string(equal, binding.name) == "*export=*")
        .expect("export assignment owns a dedicated binding");
    assert_eq!(equal.bindings()[binding_index].kind, BindingKind::Lexical);
    assert!(equal.exports().iter().any(|export| {
        constant_string(equal, export.name) == "default"
            && export.source
                == ExportSource::Local(bamts_bytecode::BindingId::new(binding_index as u32))
    }));
    assert!(
        !instructions(equal).any(|instruction| matches!(instruction, Instruction::Export { .. }))
    );

    let main = module(&executable, "main.ts");
    assert!(main.bindings().iter().any(|binding| {
        constant_string(main, binding.name) == "equal"
            && matches!(binding.kind, BindingKind::Namespace { .. })
    }));
    assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "fallback"
                && matches!(binding.kind, BindingKind::Imported { name, .. } if constant_string(main, name) == "default")
        }));
}

#[test]
fn export_assignment_combined_with_default_export_is_rejected_during_link() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "export = 1; export default 2;");

    let resolved = fixture.loader().load("main.ts").unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
    assert_eq!(error.phase, ProgramLowerPhase::Link);
    assert!(matches!(
        error.kind,
        ProgramLowerErrorKind::Link(bamts_bytecode::ProgramVerifyError {
            kind: ProgramVerifyErrorKind::DuplicateExport { .. },
            ..
        })
    ));
}

#[test]
fn program_lowering_initializes_default_named_class_binding() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "export default class Foo {}; Foo;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(main.bindings().iter().any(|binding| {
        constant_string(main, binding.name) == "Foo" && binding.kind == BindingKind::Lexical
    }));
    let stored: Vec<_> = instructions(main)
        .filter_map(|instruction| match instruction {
            Instruction::StoreGlobal { name, .. } => Some(constant_string(main, name)),
            _ => None,
        })
        .collect();
    assert!(stored.iter().any(|name| name == "Foo"));
    assert!(stored.iter().any(|name| name == "*default*"));
}

#[test]
fn program_lowering_erases_type_only_edges_from_wire_but_retains_provenance() {
    let fixture = Fixture::new();
    fixture.write("types.ts", "export interface Shape { value: number }");
    fixture.write(
        "main.ts",
        "import type { Shape } from './types.js'; let x: Shape;",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert!(main.edges().is_empty());
    assert!(
        main.bindings()
            .iter()
            .all(|binding| { constant_string(main, binding.name) != "Shape" })
    );
    let provenance = executable
        .provenance()
        .iter()
        .find(|item| item.source().path().ends_with("main.ts"))
        .unwrap();
    assert_eq!(provenance.type_only_edges().count(), 1);
}

#[test]
fn program_lowering_links_cycles_with_hoisted_and_tdz_bindings() {
    let fixture = Fixture::new();
    fixture.write(
            "a.ts",
            "import { fromB } from './b.js'; export let fromA = fromB; export var hoistedVar; export class LexicalClass {}",
        );
    fixture.write(
        "b.ts",
        "import { fromA } from './a.js'; export function fromB() { return fromA; }",
    );

    let executable = lower_fixture(&fixture, "a.ts");
    let a = module(&executable, "a.ts");
    let b = module(&executable, "b.ts");
    assert!(a.bindings().iter().any(|binding| {
        constant_string(a, binding.name) == "fromA" && binding.kind == BindingKind::Lexical
    }));
    assert!(a.bindings().iter().any(|binding| {
        constant_string(a, binding.name) == "hoistedVar" && binding.kind == BindingKind::Hoisted
    }));
    assert!(a.bindings().iter().any(|binding| {
        constant_string(a, binding.name) == "LexicalClass" && binding.kind == BindingKind::Lexical
    }));
    assert!(b.bindings().iter().any(|binding| {
        constant_string(b, binding.name) == "fromB" && binding.kind == BindingKind::Hoisted
    }));
    assert!(a.edges().iter().all(|edge| edge.kind == EdgeKind::Static));
    assert!(b.edges().iter().all(|edge| edge.kind == EdgeKind::Static));
}

#[test]
fn program_lowering_keeps_dynamic_import_as_dynamic_instruction_edge() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;");
    fixture.write("main.ts", "const pending = import('./dep.js');");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].kind, EdgeKind::Dynamic);
    assert!(
        instructions(main)
            .any(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
    );
}
#[test]
fn dynamic_missing_literal_does_not_fail_program_load() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "const pending = import('./THIS_FILE_DOES_NOT_EXIST.js'); pending;",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("missing dynamic target loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.kind(), ModuleEdgeKind::DynamicRuntime);
    assert!(edge.is_unresolved());
}

#[test]
fn dynamic_empty_specifier_does_not_fail_program_load() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "{ import(''); }");
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("empty dynamic specifier loads");
    let main = resolved.entrypoint();
    assert!(
        main.dependencies()
            .iter()
            .all(|edge| edge.kind() != ModuleEdgeKind::StaticRuntime)
    );
}

#[test]
fn dynamic_valid_target_stays_local() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;");
    fixture.write("main.ts", "const pending = import('./dep.js'); pending;");
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("valid dynamic target loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.kind(), ModuleEdgeKind::DynamicRuntime);
    assert!(!edge.is_unresolved());
    let executable = lower_fixture(&fixture, "main.ts");
    let main_wire = module(&executable, "main.ts");
    assert_eq!(main_wire.edges()[0].kind, EdgeKind::Dynamic);
}
#[test]
fn dynamic_link_failure_does_not_fail_program_link() {
    let fixture = Fixture::new();
    fixture.write("circular-1.ts", "export { x } from './circular-2.js';");
    fixture.write("circular-2.ts", "export { x } from './circular-1.js';");
    fixture.write(
        "main.ts",
        "const pending = import('./circular-1.js'); pending;",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("dynamic link fixture loads");
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let executable = lower_program(&resolved, &frontend, LowerOptions::default())
        .expect("dynamic link failure becomes runtime rejection");
    let main_wire = module(&executable, "main.ts");
    assert!(
        main_wire
            .edges()
            .iter()
            .any(|edge| edge.kind == EdgeKind::Dynamic)
    );
}
#[test]
fn dynamic_link_failure_keeps_shared_dependency_of_surviving_branch() {
    let fixture = Fixture::new();
    fixture.write("shared.ts", "export const value = 1;");
    fixture.write(
        "good.ts",
        "import { value } from './shared.js';\nexport const got = value;\n",
    );
    fixture.write(
        "bad.ts",
        "import { value } from './shared.js';\n\
             export { x } from './bad-2.js';\n\
             export const other = value;\n",
    );
    fixture.write("bad-2.ts", "export { x } from './bad.js';\n");
    fixture.write(
        "main.ts",
        "const good = import('./good.js');\nconst bad = import('./bad.js');\ngood;\nbad;\n",
    );
    let executable = lower_fixture(&fixture, "main.ts");
    let good = module(&executable, "good.ts");
    let shared_edge = good
        .edges()
        .iter()
        .find(|edge| constant_string(good, edge.specifier) == "./shared.js")
        .expect("the surviving branch keeps its shared edge");
    assert!(
        matches!(shared_edge.target, EdgeTarget::Local(_)),
        "the shared dependency stays local instead of being excluded with the failure"
    );
    module(&executable, "shared.ts");
}

#[test]
fn dynamic_assemble_failures_quarantine_every_failing_module_together() {
    let fixture = Fixture::new();
    fixture.write("good.ts", "export const got = 1;\n");
    fixture.write("bad1.js", "export const bad = 1;\n");
    fixture.write("bad2.js", "export const bad = 2;\n");
    fixture.write(
        "main.ts",
        "const good = import('./good.js');\n\
             const one = import('./bad1.js');\n\
             const two = import('./bad2.js');\n\
             good;\none;\ntwo;\n",
    );
    let resolved = fixture.loader().load("main.ts").unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let executable = lower_program(
        &resolved,
        &frontend,
        LowerOptions {
            javascript_compatibility: false,
            ..LowerOptions::default()
        },
    )
    .expect("two dynamic-only assemble failures quarantine without failing the run");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 3);
    assert!(
        main.edges()
            .iter()
            .all(|edge| edge.kind == EdgeKind::Dynamic)
    );
    for name in ["bad1.js", "bad2.js"] {
        assert!(
            module(&executable, name).edges().is_empty(),
            "{name} is stubbed instead of failing the run"
        );
    }
    module(&executable, "good.ts");
}

#[test]
fn reference_path_directive_adds_type_only_dependency() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;\n");
    fixture.write(
        "main.ts",
        "/// <reference path=\"./dep.ts\" />\nexport const x = 1;\n",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("path directive loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.kind(), ModuleEdgeKind::TypeOnly);
    assert_eq!(
        edge.reference_directive(),
        Some(ReferenceDirectiveKind::Path)
    );
    assert!(!edge.is_unresolved());
    assert!(matches!(edge.target(), ModuleTarget::Local(_)));
    let executable = lower_fixture(&fixture, "main.ts");
    let main_wire = module(&executable, "main.ts");
    assert!(
        main_wire.edges().is_empty(),
        "a reference directive creates no runtime edge"
    );
}

#[test]
fn reference_path_directive_without_dot_slash_resolves_beside_importer() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;\n");
    fixture.write(
        "main.ts",
        "/// <reference path=\"dep.ts\" />\nexport const x = 1;\n",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("bare path directive loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.specifier(), "dep.ts");
    assert_eq!(
        edge.reference_directive(),
        Some(ReferenceDirectiveKind::Path)
    );
    assert!(!edge.is_unresolved());
    assert!(matches!(edge.target(), ModuleTarget::Local(_)));
}

#[test]
fn reference_path_directive_without_dot_slash_stays_in_importer_directory() {
    let fixture = Fixture::new();
    fixture.write("nested/dep.ts", "export const value = 1;\n");
    fixture.write(
        "nested/main.ts",
        "/// <reference path=\"dep.ts\" />\nexport const x = 1;\n",
    );
    fixture.write("dep.ts", "export const shadow = 2;\n");
    let resolved = fixture
        .loader()
        .load("nested/main.ts")
        .expect("nested bare path directive loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert!(!edge.is_unresolved());
    let target = edge.target().local_source_id().expect("local target");
    let nested = resolved
        .module(target)
        .expect("referenced module is in the program");
    assert!(
        nested.path().ends_with("nested/dep.ts"),
        "bare path resolves beside the importer, got {}",
        nested.path().display()
    );
}

#[test]
fn reference_path_directive_to_missing_file_does_not_fail_program_load() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "/// <reference path=\"./missing.ts\" />\nexport const x = 1;\n",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("missing path directive loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.kind(), ModuleEdgeKind::TypeOnly);
    assert_eq!(
        edge.reference_directive(),
        Some(ReferenceDirectiveKind::Path)
    );
    assert!(edge.is_unresolved());
}

#[test]
fn reference_path_directive_to_self_loads_once() {
    let fixture = Fixture::new();
    fixture.write(
        "self.ts",
        "///<reference path='self.ts'/>\nclass Named { }\n",
    );
    let resolved = fixture
        .loader()
        .load("self.ts")
        .expect("self reference loads");
    assert_eq!(resolved.modules().len(), 1);
    let entry = resolved.entrypoint();
    assert_eq!(entry.dependencies().len(), 1);
    assert_eq!(
        entry.dependencies()[0].reference_directive(),
        Some(ReferenceDirectiveKind::Path)
    );
}

#[test]
fn reference_lib_directive_records_external_lib_edge() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "/// <reference lib=\"dom\" />\nexport const x = 1;\n",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("lib directive loads");
    assert_eq!(resolved.modules().len(), 1);
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.kind(), ModuleEdgeKind::TypeOnly);
    assert_eq!(
        edge.reference_directive(),
        Some(ReferenceDirectiveKind::Lib)
    );
    assert_eq!(edge.specifier(), "dom");
    assert!(matches!(
        edge.target(),
        ModuleTarget::External(name) if name.as_ref() == "lib:dom"
    ));
    let executable = lower_fixture(&fixture, "main.ts");
    let main_wire = module(&executable, "main.ts");
    assert!(
        main_wire.edges().is_empty(),
        "a reference directive creates no runtime edge"
    );
}

#[test]
fn reference_directive_after_first_statement_is_ignored() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;\n");
    fixture.write(
        "main.ts",
        "export const x = 1;\n/// <reference path=\"./dep.ts\" />\n",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("trailing comment loads");
    assert_eq!(resolved.modules().len(), 1);
    assert!(resolved.entrypoint().dependencies().is_empty());
}

#[test]
fn reference_types_directive_resolves_at_types_package() {
    let fixture = Fixture::new();
    fixture.write(
        "node_modules/@types/foo/index.d.ts",
        "export const value: number;\n",
    );
    fixture.write(
        "main.ts",
        "/// <reference types=\"foo\" />\nexport const x = 1;\n",
    );
    let resolved = fixture
        .loader()
        .load("main.ts")
        .expect("types directive loads");
    let main = resolved.entrypoint();
    assert_eq!(main.dependencies().len(), 1);
    let edge = &main.dependencies()[0];
    assert_eq!(edge.kind(), ModuleEdgeKind::TypeOnly);
    assert_eq!(
        edge.reference_directive(),
        Some(ReferenceDirectiveKind::Types)
    );
    assert!(!edge.is_unresolved());
    assert!(matches!(edge.target(), ModuleTarget::Local(_)));
    let executable = lower_fixture(&fixture, "main.ts");
    let main_wire = module(&executable, "main.ts");
    assert!(
        main_wire.edges().is_empty(),
        "a reference directive creates no runtime edge"
    );
}

#[test]
fn program_lowering_coalesces_static_and_dynamic_imports_of_one_target() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;");
    fixture.write(
        "main.ts",
        "import { value } from './dep.js'; const pending = import('./dep.js'); value;",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].kind, EdgeKind::StaticAndDynamic);
    assert!(main.bindings().iter().any(|binding| {
        constant_string(main, binding.name) == "value"
            && matches!(binding.kind, BindingKind::Imported { .. })
    }));
    assert!(
        instructions(main)
            .any(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
    );
}

#[test]
fn program_lowering_emits_import_meta_without_linkage_metadata() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "const meta = import.meta; meta.url;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let loads = instructions(main)
        .filter(|instruction| matches!(instruction, Instruction::LoadImportMeta { .. }))
        .count();
    assert_eq!(loads, 1);
    assert!(main.edges().is_empty());
    assert!(main.bindings().iter().any(|binding| {
        constant_string(main, binding.name) == "meta"
            && matches!(binding.kind, BindingKind::Lexical)
    }));
    assert!(main.exports().is_empty());
    assert_eq!(module_name(main), "main.ts");
}

#[test]
fn program_lowering_rejects_same_specifier_with_different_targets() {
    let fixture = Fixture::new();
    fixture.write("dep.ts", "export const value = 1;");
    fixture.write("other.ts", "export const other = 2;");
    fixture.write(
            "main.ts",
            "import { value } from './dep.js'; const pending = import('./dep.js'); import './other.js'; value;",
        );
    let mut resolved = fixture.loader().load("main.ts").unwrap();
    let other = resolved
        .modules()
        .iter()
        .find(|module| module.path().ends_with("other.ts"))
        .unwrap()
        .source_id();
    let modules = Arc::get_mut(&mut resolved.modules).unwrap();
    let main = modules
        .iter_mut()
        .find(|module| module.path().ends_with("main.ts"))
        .unwrap();
    let dependencies = Arc::make_mut(&mut main.dependencies);
    dependencies
        .iter_mut()
        .find(|edge| edge.kind == ModuleEdgeKind::DynamicRuntime)
        .unwrap()
        .target = ModuleTarget::Local(other);

    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
    assert_eq!(error.phase, ProgramLowerPhase::Metadata);
    assert_eq!(
        error.kind,
        ProgramLowerErrorKind::ConflictingRuntimeEdge {
            specifier: "./dep.js".to_owned(),
        }
    );
}

#[test]
fn program_lowering_binds_export_namespace_as_single_value_export() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "export namespace N {}");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    let binding_index = main
        .bindings()
        .iter()
        .position(|binding| constant_string(main, binding.name) == "N")
        .expect("export namespace owns one local binding");
    assert_eq!(main.bindings()[binding_index].kind, BindingKind::Hoisted);
    let exports: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert_eq!(exports, ["N"]);
    assert_eq!(
        main.exports()[0].source,
        ExportSource::Local(BindingId::new(binding_index as u32))
    );
}

#[test]
fn program_lowering_merges_duplicate_export_namespaces_into_one_export() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "export namespace N { export const x = 1; } export namespace N { export const y = 2; }",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(
        main.bindings()
            .iter()
            .filter(|binding| constant_string(main, binding.name) == "N")
            .count(),
        1,
        "merged namespaces share one binding"
    );
    let exports: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert_eq!(exports, ["N"]);
}

#[test]
fn program_lowering_merges_export_function_and_export_namespace_without_duplicate_export() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "export function F() { return 1; } export namespace F { export const x = 2; }",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(
        main.bindings()
            .iter()
            .filter(|binding| constant_string(main, binding.name) == "F")
            .count(),
        1
    );
    let exports: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert_eq!(exports, ["F"]);
}

#[test]
fn program_lowering_merges_export_class_and_export_namespace_without_duplicate_export() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "export class C {} export namespace C { export const x = 1; }",
    );

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(
        main.bindings()
            .iter()
            .filter(|binding| constant_string(main, binding.name) == "C")
            .count(),
        1,
        "class/namespace merge must not emit DuplicateBinding"
    );
    let exports: Vec<_> = main
        .exports()
        .iter()
        .map(|export| constant_string(main, export.name))
        .collect();
    assert_eq!(exports, ["C"]);
}

#[test]
fn program_lowering_preserves_true_duplicate_namespace_exports() {
    let fixture = Fixture::new();
    // Specifier-form duplicates remain link failures even after namespace merge
    // dedup for declaration exports.
    fixture.write("main.ts", "const N = 1; export { N }; export { N };");

    let resolved = fixture.loader().load("main.ts").unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
    assert_eq!(error.phase, ProgramLowerPhase::Link);
    assert!(matches!(
        error.kind,
        ProgramLowerErrorKind::Link(bamts_bytecode::ProgramVerifyError {
            kind: ProgramVerifyErrorKind::DuplicateExport { .. },
            ..
        })
    ));
}

#[test]
fn program_lowering_rejects_duplicate_exports_during_link() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "const value = 1; export { value }; export { value };",
    );
    let resolved = fixture.loader().load("main.ts").unwrap();
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
    assert_eq!(error.phase, ProgramLowerPhase::Link);
    assert!(matches!(
        error.kind,
        ProgramLowerErrorKind::Link(bamts_bytecode::ProgramVerifyError {
            kind: ProgramVerifyErrorKind::DuplicateExport { .. },
            ..
        })
    ));
}

#[test]
fn program_lowering_preserves_external_identity_only_in_provenance() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import * as fs from 'node:fs'; fs.readFile;");

    let executable = lower_fixture(&fixture, "main.ts");
    let main = module(&executable, "main.ts");
    assert_eq!(main.edges().len(), 1);
    assert_eq!(main.edges()[0].target, EdgeTarget::External);
    let provenance = executable
        .provenance()
        .iter()
        .find(|item| item.source().path().ends_with("main.ts"))
        .unwrap();
    assert!(matches!(
        provenance.edges()[0].target(),
        ModuleTarget::External(specifier) if specifier.as_ref() == "node:fs"
    ));
}

#[test]
fn program_lowering_is_deterministic_and_names_modules_root_relatively() {
    let fixture = Fixture::new();
    fixture.write("lib/dep.ts", "export const value = 1;");
    fixture.write("src/main.ts", "export { value } from '../lib/dep.js';");

    let first = lower_fixture(&fixture, "src/main.ts");
    let second = lower_fixture(&fixture, "src/main.ts");
    assert_eq!(first.wire().encode(), second.wire().encode());
    assert_eq!(
        first
            .wire()
            .modules()
            .iter()
            .map(module_name)
            .collect::<Vec<_>>(),
        ["lib/dep.ts", "src/main.ts"]
    );
    for (left, right) in first.wire().modules().iter().zip(second.wire().modules()) {
        assert_eq!(left.code().encode(), right.code().encode());
    }
}

#[test]
fn resolves_extensions_and_directory_indexes_dependency_first() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import './leaf.js'; import './branch';");
    fixture.write("leaf.ts", "export const leaf = 1;");
    fixture.write("branch/index.ts", "export const branch = 1;");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["leaf.ts", "index.ts", "main.ts"]);
}

#[test]
fn excludes_type_only_dependencies_from_runtime_closure() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "import type { Shape } from './shape'; import { value } from './value'; void value;",
    );
    fixture.write("shape.ts", "export interface Shape { x: number }");
    fixture.write("value.ts", "export const value = 1;");

    let program = fixture.loader().load("main.ts").unwrap();
    let runtime: Vec<_> = program
        .runtime_modules()
        .iter()
        .map(|module| module.path().file_name().unwrap().to_str().unwrap())
        .collect();

    assert_eq!(runtime, ["value.ts", "main.ts"]);
    assert!(
        program.entrypoint().dependencies().iter().any(|edge| {
            edge.kind() == ModuleEdgeKind::TypeOnly && edge.specifier() == "./shape"
        })
    );
}

#[test]
fn deduplicates_diamond_dependencies_by_canonical_path() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import './left'; import './right';");
    fixture.write("left.ts", "import './shared';");
    fixture.write("right.ts", "import './shared';");
    fixture.write("shared.ts", "export const shared = 1;");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(
        names(&program),
        ["shared.ts", "left.ts", "right.ts", "main.ts"]
    );
    assert_eq!(program.modules().len(), 4);
}

#[test]
fn multi_root_load_compiles_every_root_and_reads_shared_source_once() {
    let fixture = Fixture::new();
    fixture.write(
        "a.ts",
        "import { shared } from './shared'; export const a = shared;",
    );
    fixture.write(
        "b.ts",
        "import { shared } from './shared'; export const b = shared;",
    );
    fixture.write("shared.ts", "export const shared = 1;");

    let root = ProjectRoot::new(fs::canonicalize(&fixture.0).unwrap()).unwrap();
    let config = ProjectConfig::parse(&root, fixture.0.join("tsconfig.json"), "{}").unwrap();
    let filesystem = Arc::new(CountingFileSystem::new(&fixture.0, Path::new("shared.ts")));
    let loader_filesystem: Arc<dyn FileSystem> = filesystem.clone();
    let loader =
        ProgramLoader::with_file_system(&root, config.options(), loader_filesystem).unwrap();

    let program = loader
        .load_roots(&[PathBuf::from("b.ts"), PathBuf::from("a.ts")])
        .unwrap();
    let frontend = compile_program_frontend(&program, FrontendMode::Check);

    assert_eq!(names(&program), ["shared.ts", "a.ts", "b.ts"]);
    assert_eq!(program.roots().len(), 2);
    assert_eq!(frontend.modules().len(), 3);
    assert!(frontend.modules().iter().all(|module| !module.has_errors()));
    assert_eq!(filesystem.shared_reads.load(Ordering::Relaxed), 1);
    assert_eq!(filesystem.total_reads.load(Ordering::Relaxed), 3);
}

#[test]
fn multi_root_load_is_input_order_independent_and_keeps_explicit_dependency_root() {
    let fixture = Fixture::new();
    fixture.write("a.ts", "import './shared'; export const a: string = 1;");
    fixture.write("b.ts", "import './shared'; export const b: boolean = 2;");
    fixture.write("shared.ts", "export const shared = 3;");
    let loader = fixture.loader();
    let forward = loader
        .load_roots(&[
            PathBuf::from("a.ts"),
            PathBuf::from("b.ts"),
            PathBuf::from("shared.ts"),
            PathBuf::from("a.ts"),
        ])
        .unwrap();
    let reversed = loader
        .load_roots(&[
            PathBuf::from("a.ts"),
            PathBuf::from("shared.ts"),
            PathBuf::from("b.ts"),
            PathBuf::from("a.ts"),
        ])
        .unwrap();

    let graph = |program: &super::ResolvedProgram| {
        program
            .modules()
            .iter()
            .map(|module| {
                (
                    module.source_id(),
                    module
                        .path()
                        .strip_prefix(program.root().path())
                        .unwrap()
                        .to_path_buf(),
                    module
                        .dependencies()
                        .iter()
                        .map(|edge| {
                            (
                                edge.kind(),
                                edge.specifier().to_owned(),
                                edge.target().clone(),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>()
    };
    let diagnostics = |program: &super::ResolvedProgram| {
        compile_program_frontend(program, FrontendMode::Check)
            .modules()
            .iter()
            .flat_map(|module| module.diagnostics().iter().cloned())
            .collect::<Vec<_>>()
    };

    let forward_diagnostics = diagnostics(&forward);
    let reversed_diagnostics = diagnostics(&reversed);
    assert!(!forward_diagnostics.is_empty());
    assert_eq!(forward.roots(), reversed.roots());
    assert_eq!(graph(&forward), graph(&reversed));
    assert_eq!(forward_diagnostics, reversed_diagnostics);
    assert_eq!(
        forward
            .roots()
            .iter()
            .map(|source_id| {
                forward
                    .module(*source_id)
                    .unwrap()
                    .path()
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
            })
            .collect::<Vec<_>>(),
        ["a.ts", "b.ts", "shared.ts"]
    );
}

#[test]
fn multi_root_load_rejects_missing_and_empty_root_sets_with_typed_errors() {
    let fixture = Fixture::new();
    fixture.write("present.ts", "export const present = true;");
    let loader = fixture.loader();

    let error = loader
        .load_roots(&[PathBuf::from("present.ts"), PathBuf::from("missing.ts")])
        .unwrap_err();
    assert!(matches!(
        error,
        ProgramLoadError::Read { path, source }
            if path.ends_with("missing.ts") && source.kind() == std::io::ErrorKind::NotFound
    ));
    assert!(matches!(
        loader.load_roots(&[]).unwrap_err(),
        ProgramLoadError::NoRoots
    ));
}

#[test]
fn preserves_cycles_without_duplicate_modules() {
    let fixture = Fixture::new();
    fixture.write("a.ts", "import './b';");
    fixture.write("b.ts", "import './a';");

    let program = fixture.loader().load("a.ts").unwrap();
    let b = &program.modules()[0];

    assert_eq!(names(&program), ["b.ts", "a.ts"]);
    assert_eq!(
        b.dependencies()[0].target(),
        &ModuleTarget::Local(program.entrypoint_id())
    );
}

#[test]
fn loads_a_long_acyclic_import_chain_iteratively() {
    // Deep enough that the previous recursive DFS would blow the thread stack,
    // but cheap to materialize: one tiny file per hop.
    const DEPTH: usize = 4096;
    let fixture = Fixture::new();
    for index in 0..DEPTH {
        let name = format!("m{index}.ts");
        let source = if index + 1 == DEPTH {
            "export {};\n".to_string()
        } else {
            format!("import './m{}.ts';\n", index + 1)
        };
        fixture.write(&name, &source);
    }

    let program = fixture.loader().load("m0.ts").unwrap();

    assert_eq!(program.modules().len(), DEPTH);
    assert_eq!(program.entrypoint_id().get(), 0);
    assert_eq!(
        program.modules().last().map(|module| module.source_id()),
        Some(program.entrypoint_id())
    );
    assert_eq!(
        program.modules()[0]
            .path()
            .file_name()
            .unwrap()
            .to_str()
            .unwrap(),
        format!("m{}.ts", DEPTH - 1)
    );
    assert_eq!(
        program.modules()[0].source_id().get(),
        u32::try_from(DEPTH - 1).unwrap()
    );
    assert_eq!(
        program.entrypoint().dependencies()[0].target(),
        &ModuleTarget::Local(program.modules()[DEPTH - 2].source_id())
    );
}

#[test]
fn resolves_package_exports_entry() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import { answer } from 'waybread'; void answer;");
    fixture.write(
        "node_modules/waybread/package.json",
        r#"{"name":"waybread","exports":{".":{"import":"./src/entry.js"}}}"#,
    );
    fixture.write(
        "node_modules/waybread/src/entry.ts",
        "export const answer = 42;",
    );

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["entry.ts", "main.ts"]);
}
#[test]
fn resolves_package_import_maps() {
    let fixture = Fixture::new();
    fixture.write(
        "package.json",
        r##"{"name":"root","imports":{"#waybread":"./src/alias.js"}}"##,
    );
    fixture.write(
        "main.ts",
        "import { answer } from '#waybread'; void answer;",
    );
    fixture.write("src/alias.ts", "export const answer = 42;");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["alias.ts", "main.ts"]);
}

#[test]
fn decodes_escaped_module_specifiers() {
    let fixture = Fixture::new();
    fixture.write("main.ts", r#"import './\u0066oo';"#);
    fixture.write("foo.ts", "export const answer = 42;");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["foo.ts", "main.ts"]);
}

#[test]
fn rejects_ill_formed_utf16_module_specifiers() {
    for source in [
        r#"import type { T } from "\uD800";"#,
        r#"type T = import("\uD800").T;"#,
    ] {
        let fixture = Fixture::new();
        fixture.write("main.ts", source);

        assert!(matches!(
            fixture.loader().load("main.ts"),
            Err(ProgramLoadError::IllFormedModuleSpecifier { .. })
        ));
    }
}

#[test]
fn rejects_relative_traversal_before_loading() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import '../outside.ts';");

    let error = fixture.loader().load("main.ts").unwrap_err();

    assert!(matches!(
        error,
        ProgramLoadError::InvalidSpecifier { .. } | ProgramLoadError::UnresolvedModule(_)
    ));
}

#[test]
fn retains_literal_dynamic_import_edges() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "async function load() { return import('./later'); }",
    );
    fixture.write("later.ts", "export const later = 1;");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["later.ts", "main.ts"]);
    assert_eq!(
        program.entrypoint().dependencies()[0].kind(),
        ModuleEdgeKind::DynamicRuntime
    );
    assert_eq!(program.runtime_modules().len(), 1);
}

#[test]
fn retains_dynamic_imports_from_class_decorators() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "@import('./class') class C {\n\
             @import('./constructor') constructor() {}\n\
             @import('./method') method() {}\n\
             @import('./property') property;\n\
             @import('./accessor') accessor value;\n\
             }",
    );
    for module in ["class", "constructor", "method", "property", "accessor"] {
        fixture.write(&format!("{module}.ts"), "export {};");
    }

    let program = fixture.loader().load("main.ts").unwrap();
    let dependencies = program.entrypoint().dependencies();
    assert_eq!(dependencies.len(), 5);
    assert!(
        dependencies
            .iter()
            .all(|dependency| dependency.kind() == ModuleEdgeKind::DynamicRuntime)
    );
    assert_eq!(
        dependencies
            .iter()
            .map(|dependency| dependency.specifier())
            .collect::<Vec<_>>(),
        [
            "./class",
            "./constructor",
            "./method",
            "./property",
            "./accessor",
        ]
    );
}

#[test]
fn classifies_import_types_without_creating_dynamic_runtime_edges() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "type Shape = import('./shape').Shape; void 0;");
    fixture.write("shape.ts", "export interface Shape { x: number }");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["shape.ts", "main.ts"]);
    assert_eq!(
        program.entrypoint().dependencies()[0].kind(),
        ModuleEdgeKind::TypeOnly
    );
    assert_eq!(program.runtime_modules().len(), 1);
}

#[test]
fn unresolved_runtime_edge_reports_typed_diagnostic() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import './missing';");

    let ProgramLoadError::UnresolvedModule(diagnostic) =
        fixture.loader().load("main.ts").unwrap_err()
    else {
        panic!("expected unresolved-module diagnostic");
    };

    assert_eq!(diagnostic.kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(diagnostic.specifier(), "./missing");
    assert_eq!(
        diagnostic.importer().file_name(),
        Some(Path::new("main.ts").as_os_str())
    );
}

#[test]
fn retains_node_builtin_as_external_static_runtime_edge() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "import { parseArgs } from 'node:util'; void parseArgs;",
    );

    let program = fixture.loader().load("main.ts").unwrap();
    let edge = &program.entrypoint().dependencies()[0];

    assert_eq!(names(&program), ["main.ts"]);
    assert_eq!(edge.kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(edge.target().external_specifier(), Some("node:util"));
    assert_eq!(program.runtime_modules().len(), 1);
}

#[test]
fn preserves_unresolved_type_package_as_external_identity() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import type { JsonValue } from 'type-fest';");

    let program = fixture.loader().load("main.ts").unwrap();
    let edge = &program.entrypoint().dependencies()[0];

    assert_eq!(edge.kind(), ModuleEdgeKind::TypeOnly);
    assert_eq!(edge.target().external_specifier(), Some("type-fest"));
    assert_eq!(program.runtime_modules().len(), 1);
}

#[test]
fn unresolved_ordinary_runtime_package_is_rejected() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import 'waybread';");

    let ProgramLoadError::UnresolvedModule(diagnostic) =
        fixture.loader().load("main.ts").unwrap_err()
    else {
        panic!("expected unresolved-module diagnostic");
    };

    assert_eq!(diagnostic.kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(diagnostic.specifier(), "waybread");
}

#[test]
fn retains_dynamic_engine_module_as_external_edge() {
    let fixture = Fixture::new();
    fixture.write(
        "package.json",
        r##"{"name":"root","imports":{"#engine":"engine:clock"}}"##,
    );
    fixture.write(
        "main.ts",
        "async function load() { return import('#engine'); }",
    );

    let program = fixture.loader().load("main.ts").unwrap();
    let edge = &program.entrypoint().dependencies()[0];

    assert_eq!(edge.kind(), ModuleEdgeKind::DynamicRuntime);
    assert_eq!(edge.specifier(), "#engine");
    assert_eq!(edge.target().external_specifier(), Some("engine:clock"));
    assert_eq!(program.runtime_modules().len(), 1);
}

#[test]
fn local_type_package_takes_precedence_over_external_fallback() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import type { Shape } from 'waybread';");
    fixture.write(
        "node_modules/waybread/package.json",
        r#"{"name":"waybread","types":"./index.d.ts"}"#,
    );
    fixture.write(
        "node_modules/waybread/index.d.ts",
        "export interface Shape { x: number }",
    );

    let program = fixture.loader().load("main.ts").unwrap();
    let edge = &program.entrypoint().dependencies()[0];

    assert_eq!(names(&program), ["index.d.ts", "main.ts"]);
    assert!(matches!(edge.target(), ModuleTarget::Local(_)));
}

#[test]
fn records_flavor_and_mode_for_type_only_runtime_and_dynamic_edges() {
    let fixture = Fixture::new();
    fixture.write("types.ts", "export interface Shape { value: number }");
    fixture.write("value.ts", "export const value = 1;");
    fixture.write("later.ts", "export const later = 2;");
    fixture.write(
        "main.ts",
        "import type { Shape } from './types.js';\n\
             import { value } from './value.js';\n\
             const observed: Shape = value;\n\
             const pending = import('./later.js');\n\
             void pending;",
    );

    let program = fixture.loader().load("main.ts").unwrap();
    let dependencies = program.entrypoint().dependencies();

    assert_eq!(
        names(&program),
        ["types.ts", "value.ts", "later.ts", "main.ts"]
    );
    assert_eq!(dependencies[0].kind(), ModuleEdgeKind::TypeOnly);
    assert_eq!(dependencies[0].flavor(), ResolutionFlavor::Types);
    assert_eq!(dependencies[0].mode(), ResolutionMode::Import);
    assert_eq!(dependencies[1].kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(dependencies[1].flavor(), ResolutionFlavor::Runtime);
    assert_eq!(dependencies[1].mode(), ResolutionMode::Import);
    assert_eq!(dependencies[2].kind(), ModuleEdgeKind::DynamicRuntime);
    assert_eq!(dependencies[2].flavor(), ResolutionFlavor::Runtime);
    assert_eq!(dependencies[2].mode(), ResolutionMode::Import);
}

#[test]
fn import_equals_require_pins_require_mode_and_condition_target() {
    let fixture = Fixture::new();
    fixture.write(
        "node_modules/waybread/package.json",
        r#"{"name":"waybread","exports":{".":{"import":"./esm.js","require":"./cjs.js"}}}"#,
    );
    fixture.write("node_modules/waybread/esm.ts", "export const crumb = 1;");
    fixture.write("node_modules/waybread/cjs.ts", "export const crumb = 2;");
    fixture.write(
        "main.ts",
        "import loaf = require('waybread');\n\
             import { crumb } from 'waybread';\n\
             void loaf; void crumb;",
    );

    let program = fixture.loader().load("main.ts").unwrap();
    let dependencies = program.entrypoint().dependencies();

    assert_eq!(names(&program), ["cjs.ts", "esm.ts", "main.ts"]);
    assert_eq!(dependencies[0].kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(dependencies[0].flavor(), ResolutionFlavor::Runtime);
    assert_eq!(dependencies[0].mode(), ResolutionMode::Require);
    assert!(matches!(dependencies[0].target(), ModuleTarget::Local(_)));
    assert_eq!(dependencies[1].kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(dependencies[1].flavor(), ResolutionFlavor::Runtime);
    assert_eq!(dependencies[1].mode(), ResolutionMode::Import);
    assert!(matches!(dependencies[1].target(), ModuleTarget::Local(_)));
}

#[test]
fn declaration_importer_edges_resolve_with_types_flavor() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import './lib';");
    fixture.write("lib.d.ts", "import './peer';");
    fixture.write("peer.ts", "export const value = 1;");

    let program = fixture.loader().load("main.ts").unwrap();

    assert_eq!(names(&program), ["peer.ts", "lib.d.ts", "main.ts"]);
    assert_eq!(
        program.entrypoint().dependencies()[0].flavor(),
        ResolutionFlavor::Runtime
    );
    let lib = &program.modules()[1];
    assert_eq!(
        lib.path().file_name().and_then(|name| name.to_str()),
        Some("lib.d.ts")
    );
    assert_eq!(lib.dependencies()[0].flavor(), ResolutionFlavor::Types);
    assert_eq!(lib.dependencies()[0].mode(), ResolutionMode::Import);
}

#[test]
fn lowers_and_verifies_every_manifest_pinned_corpus_program() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let manifest = fs::read_to_string(repository.join("corpus/manifest.toml")).unwrap();
    let entrypoints: Vec<_> = manifest
        .lines()
        .filter_map(|line| {
            line.strip_prefix("entrypoint = \"")
                .and_then(|value| value.strip_suffix('"'))
        })
        .collect();
    assert!(
        !entrypoints.is_empty(),
        "corpus manifest must declare projects"
    );

    let root = ProjectRoot::new(repository).unwrap();
    let config = ProjectConfig::parse(&root, root.path().join("tsconfig.json"), "{}").unwrap();
    let loader = ProgramLoader::new(&root, config.options()).unwrap();
    for entrypoint in entrypoints {
        let resolved = loader
            .load(entrypoint)
            .unwrap_or_else(|error| panic!("{entrypoint}: {error}"));
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let executable = lower_program(
            &resolved,
            &frontend,
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{entrypoint}: {error}"));
        assert_eq!(executable.wire().modules().len(), resolved.modules().len());
    }
}

#[test]
fn compiler_module_option_controls_commonjs_wrapper_bindings() {
    let fixture = Fixture::new();
    fixture.write(
        "main.ts",
        "module; exports; require; __filename; __dirname;",
    );

    let commonjs = fixture
        .loader_with_config(r#"{"compilerOptions": {"module": "CommonJS"}}"#)
        .load("main.ts")
        .unwrap();
    assert!(commonjs.is_commonjs());
    let commonjs_frontend = compile_program_frontend(&commonjs, FrontendMode::Check);
    assert!(commonjs_frontend.modules().iter().all(|module| {
        module
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code().as_str() != "BAMTS-C002")
    }));

    let esm = fixture.loader().load("main.ts").unwrap();
    assert!(!esm.is_commonjs());
    let esm_frontend = compile_program_frontend(&esm, FrontendMode::Check);
    assert!(esm_frontend.modules().iter().any(|module| {
        module
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code().as_str() == "BAMTS-C002")
    }));
}

#[test]
fn jsx_runtime_linkage_adds_default_runtime_to_resolved_graph() {
    let fixture = Fixture::new();
    fixture.write(
            "main.tsx",
            "import { jsx as authored } from 'react/jsx-runtime'; void authored; export const view = <div />;",
        );
    fixture.write(
        "node_modules/react/package.json",
        r#"{"name":"react","exports":{"./jsx-runtime":"./jsx-runtime.ts"}}"#,
    );
    fixture.write(
        "node_modules/react/jsx-runtime.ts",
        "export function jsx() {} export function jsxs() {} export const Fragment = 0;",
    );

    let program = fixture
        .loader_with_config(r#"{"compilerOptions":{"jsx":"react-jsx"}}"#)
        .load("main.tsx")
        .unwrap();
    let main = program.entrypoint();
    let runtime = main
        .dependencies()
        .iter()
        .find(|edge| edge.specifier() == "react/jsx-runtime")
        .expect("automatic JSX creates one ordinary runtime dependency");
    assert_eq!(runtime.kind(), ModuleEdgeKind::StaticRuntime);
    assert_eq!(
        main.dependencies()
            .iter()
            .filter(|edge| edge.specifier() == "react/jsx-runtime")
            .count(),
        1,
        "source-authored and generated runtime demand share one edge"
    );
    let ModuleTarget::Local(runtime_id) = runtime.target() else {
        panic!("fixture runtime resolves through the canonical local graph");
    };
    assert_eq!(
        program.module(*runtime_id).unwrap().path(),
        fixture.0.join("node_modules/react/jsx-runtime.ts")
    );
}

#[test]
fn jsx_runtime_linkage_reuses_runtime_node_across_roots() {
    let fixture = Fixture::new();
    fixture.write("a.tsx", "export const a = <div />;");
    fixture.write("b.tsx", "export const b = <span />;");
    fixture.write(
        "runtime/jsx-runtime.ts",
        "export function jsx() {} export function jsxs() {} export const Fragment = 0;",
    );
    let program = fixture
        .loader_with_config(
            r#"{"compilerOptions":{"jsx":"react-jsx","jsxImportSource":"./runtime"}}"#,
        )
        .load_roots(&[PathBuf::from("b.tsx"), PathBuf::from("a.tsx")])
        .unwrap();
    let runtime_targets: Vec<_> = program
        .roots()
        .iter()
        .map(|root| {
            program
                .module(*root)
                .unwrap()
                .dependencies()
                .iter()
                .find(|edge| edge.specifier() == "./runtime/jsx-runtime")
                .unwrap()
                .target()
                .clone()
        })
        .collect();
    assert_eq!(runtime_targets[0], runtime_targets[1]);
    assert_eq!(
        program
            .modules()
            .iter()
            .filter(|module| module.path().ends_with("runtime/jsx-runtime.ts"))
            .count(),
        1
    );
}

#[test]
fn jsx_runtime_linkage_reports_missing_runtime_through_resolver() {
    let fixture = Fixture::new();
    fixture.write("main.tsx", "export const view = <div />;");
    let error = fixture
        .loader_with_config(r#"{"compilerOptions":{"jsx":"react-jsx"}}"#)
        .load("main.tsx")
        .expect_err("missing automatic runtime must be a module-resolution error");
    let ProgramLoadError::UnresolvedModule(diagnostic) = error else {
        panic!("expected typed unresolved-module diagnostic");
    };
    assert_eq!(diagnostic.specifier(), "react/jsx-runtime");
}

#[test]
fn jsx_runtime_linkage_uses_dev_source_and_collision_free_imported_bindings() {
    let fixture = Fixture::new();
    fixture.write(
        "main.tsx",
        "const __bamts_jsx_jsxDEV = 0; export const view = <><div /></>;",
    );
    fixture.write(
        "runtime/jsx-dev-runtime.ts",
        "export function jsxDEV() {} export const Fragment = 0;",
    );
    let resolved = fixture
        .loader_with_config(
            r#"{"compilerOptions":{"jsx":"react-jsxdev","jsxImportSource":"./runtime"}}"#,
        )
        .load("main.tsx")
        .unwrap();
    assert!(resolved.entrypoint().dependencies().iter().any(|edge| {
        edge.kind() == ModuleEdgeKind::StaticRuntime
            && edge.specifier() == "./runtime/jsx-dev-runtime"
    }));

    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let executable = lower_program(
        &resolved,
        &frontend,
        LowerOptions {
            javascript_compatibility: true,
            ..LowerOptions::default()
        },
    )
    .unwrap();
    let main = module(&executable, "main.tsx");
    let imported: Vec<_> = main
        .bindings()
        .iter()
        .filter_map(|binding| match binding.kind {
            BindingKind::Imported { name, .. } => Some((
                constant_string(main, binding.name),
                constant_string(main, name),
            )),
            _ => None,
        })
        .collect();
    assert!(imported.contains(&("__bamts_jsx_jsxDEV_2".to_owned(), "jsxDEV".to_owned())));
    assert!(imported.contains(&("__bamts_jsx_Fragment".to_owned(), "Fragment".to_owned())));
    assert!(
        main.bindings()
            .iter()
            .all(|binding| constant_string(main, binding.name) != "_jsxDEV")
    );
}

#[test]
fn jsx_runtime_linkage_preserve_and_classic_add_no_runtime_edge() {
    for jsx in ["preserve", "react"] {
        let fixture = Fixture::new();
        fixture.write("main.tsx", "export const view = <div />;");
        let config = format!(r#"{{"compilerOptions":{{"jsx":"{jsx}"}}}}"#);
        let program = fixture
            .loader_with_config(&config)
            .load("main.tsx")
            .unwrap();
        assert!(program.entrypoint().dependencies().is_empty(), "{jsx}");
    }
}

#[test]
fn jsx_options_survive_loading_and_select_one_output_route() {
    let fixture = Fixture::new();
    fixture.write("main.tsx", "export const view = 1;");
    let program = fixture
        .loader_with_config(
            r#"{"compilerOptions":{
                    "jsx":"react-jsx",
                    "jsxFactory":"h",
                    "jsxFragmentFactory":"Fragment",
                    "jsxImportSource":"@scope/runtime"
                }}"#,
        )
        .load("main.tsx")
        .unwrap();

    assert_eq!(program.jsx(), Some(JsxEmit::ReactJsx));
    assert_eq!(program.jsx_factory(), Some("h"));
    assert_eq!(program.jsx_fragment_factory(), Some("Fragment"));
    assert_eq!(program.jsx_import_source(), Some("@scope/runtime"));
    assert_eq!(
        program.jsx_routing_decision(ProgramOutputKind::JavaScript),
        JsxRoutingDecision::TransformAndEmit
    );
    assert_eq!(
        program.jsx_routing_decision(ProgramOutputKind::NativeExecutable),
        JsxRoutingDecision::Lower
    );
}
#[test]
fn declaration_overlay_preserves_runtime_target_identity() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import Queue from './index.js'; void Queue;");
    fixture.write("index.js", "export default class Queue {}");
    fixture.write(
        "index.d.ts",
        "export default class Queue<Value> { value: Value; }",
    );

    let program = fixture.loader().load("main.ts").unwrap();
    let edge = &program.entrypoint().dependencies()[0];
    let runtime_id = edge
        .target()
        .local_source_id()
        .expect("local runtime target");
    let type_id = edge
        .type_target()
        .and_then(ModuleTarget::local_source_id)
        .expect("local declaration overlay");

    assert_ne!(runtime_id, type_id);
    assert!(
        program
            .module(runtime_id)
            .unwrap()
            .path()
            .ends_with("index.js")
    );
    assert!(
        program
            .module(type_id)
            .unwrap()
            .path()
            .ends_with("index.d.ts")
    );
    assert!(
        program
            .module(type_id)
            .unwrap()
            .source()
            .is_declaration_file()
    );
    assert_eq!(
        program
            .runtime_modules()
            .iter()
            .filter(|module| module.source_id() == type_id)
            .count(),
        0,
        "checker overlay must not enter the eager runtime closure"
    );
}

#[test]
fn runtime_edge_without_declaration_overlay_has_no_type_target() {
    let fixture = Fixture::new();
    fixture.write("main.ts", "import Queue from './index.js'; void Queue;");
    fixture.write("index.js", "export default class Queue {}");

    let program = fixture.loader().load("main.ts").unwrap();
    let edge = &program.entrypoint().dependencies()[0];

    assert!(edge.target().local_source_id().is_some());
    assert!(edge.type_target().is_none());
    assert_eq!(names(&program), ["index.js", "main.ts"]);
}

#[test]
fn program_loader_enforces_source_budgets_and_stable_codes() {
    assert_eq!(
        super::accumulate_session_bytes(0, super::MAX_SESSION_SOURCE_BYTES),
        Ok(super::MAX_SESSION_SOURCE_BYTES)
    );
    assert_eq!(
        super::accumulate_session_bytes(super::MAX_SESSION_SOURCE_BYTES - 1, 2),
        Err(super::MAX_SESSION_SOURCE_BYTES + 1)
    );
    assert_eq!(
        super::accumulate_session_bytes(usize::MAX, 1),
        Err(usize::MAX)
    );

    let fixture = Fixture::new();
    fixture.write("main.ts", "import './left'; import './right';");
    fixture.write("left.ts", "import './shared';");
    fixture.write("right.ts", "import './shared';");
    fixture.write("shared.ts", "export const shared = 1;");
    let program = fixture.loader().load("main.ts").unwrap();
    assert_eq!(program.modules().len(), 4, "diamond imports load once");

    let exact = "a".repeat(crate::source::MAX_SOURCE_BYTES);
    fixture.write("exact.ts", &exact);
    fixture.loader().load("exact.ts").unwrap();

    let oversized = "a".repeat(crate::source::MAX_SOURCE_BYTES + 1);
    fixture.write("oversized.ts", &oversized);
    let error = fixture.loader().load("oversized.ts").unwrap_err();
    let ProgramLoadError::SourceTooLarge { path, len } = &error else {
        panic!("expected SourceTooLarge, got {error}");
    };
    assert_eq!(*len, crate::source::MAX_SOURCE_BYTES + 1);
    assert!(path.ends_with("oversized.ts"));
    assert_eq!(error.code(), Some(super::SOURCE_TOO_LARGE));
    assert!(std::error::Error::source(&error).is_none());

    let session = ProgramLoadError::SessionTooLarge {
        path: PathBuf::from("next.ts"),
        total: super::MAX_SESSION_SOURCE_BYTES + 1,
    };
    assert_eq!(session.code(), Some(super::SESSION_TOO_LARGE));
    assert!(session.to_string().contains("next.ts"));
    assert!(std::error::Error::source(&session).is_none());
}

/// Loads one file and returns its checker-facing effective configuration.
fn resolved(main: &str, compiler_options: &str) -> ResolvedProgram {
    let fixture = Fixture::new();
    fixture.write("main.ts", main);
    let config = format!(r#"{{"compilerOptions":{compiler_options}}}"#);
    fixture
        .loader_with_config(&config)
        .load("main.ts")
        .expect("resolved program")
}

#[test]
fn strict_family_options_reach_the_checker_environment() {
    // The suite default (see check_cells.rs build_tsconfig) is strict:true
    // unless a case pragma says otherwise, so strict-on is the wired shape.
    let options = resolved("export const value = 1;", r#"{"strict":true}"#).check_options();
    assert!(options.no_implicit_any());
    assert!(options.strict_null_checks());
    assert!(options.strict_property_initialization());
    assert!(options.always_strict());
    assert!(!options.is_commonjs());
    let off = resolved("export const value = 1;", r#"{"strict":false}"#).check_options();
    assert!(!off.no_implicit_any());
    assert!(!off.strict_null_checks());
    assert!(!off.strict_property_initialization());
    assert!(!off.always_strict());
}

#[test]
fn individual_strict_members_override_the_master_switch() {
    // Upstream optionsStrictPropertyInitializationStrict.ts (sha256
    // 4c5f28823ac849778d69aed835f56cfff163dfb871c3d31496a0d0b46531c749)
    // pairs `strict` with explicit strictPropertyInitialization; the
    // showConfig baselines pin the member names as overridable:
    // noImplicitAny 35227919..., strictNullChecks 385f6fd5...,
    // strictPropertyInitialization b3dadd75...
    let mixed = resolved(
        "export const value = 1;",
        r#"{"strict":true,"noImplicitAny":false,"strictNullChecks":false,
                "strictPropertyInitialization":false,"alwaysStrict":false}"#,
    )
    .check_options();
    assert!(!mixed.no_implicit_any());
    assert!(!mixed.strict_null_checks());
    assert!(!mixed.strict_property_initialization());
    assert!(!mixed.always_strict());
}

#[test]
fn module_and_target_still_select_environment_and_es5() {
    let es5 = resolved(
        "export const value = 1;",
        r#"{"module":"commonjs","target":"es5","alwaysStrict":true}"#,
    )
    .check_options();
    assert!(es5.is_commonjs());
    assert!(es5.es5());
    assert!(es5.always_strict());
}

#[test]
fn check_options_drives_end_to_end_diagnostics() {
    // Upstream abstractClassUnionInstantiation.ts (sha256
    // 012bd00d5213a672086b74643b36cf3f252b4a7e96b5950d2f8121ae725581c5)
    // baseline errors.txt (sha256 20f79cd3...) expects TS2564 rows for
    // abstract properties; with strict-on plumbing they must surface.
    let program = resolved(
        "abstract class A { a: string; }\nnew A();\n",
        r#"{"strict":true}"#,
    );
    let frontend = compile_program_frontend(&program, FrontendMode::Check);
    let strict_on: Vec<_> = frontend
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics().iter())
        .filter(|diagnostic| diagnostic.code().as_str() == "BAMTS-C028")
        .collect();
    assert_eq!(strict_on.len(), 1, "{strict_on:?}");

    let permissive = resolved(
        "abstract class A { a: string; }\nnew A();\n",
        r#"{"strict":false}"#,
    );
    let frontend = compile_program_frontend(&permissive, FrontendMode::Check);
    let permissive_strict_on: Vec<_> = frontend
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics().iter())
        .filter(|diagnostic| diagnostic.code().as_str() == "BAMTS-C028")
        .collect();
    assert!(permissive_strict_on.is_empty(), "{permissive_strict_on:?}");
    // The same program must report the flag through its checker view.
    assert!(permissive.check_options() == ProgramCheckOptions::standard());
}
