//! Key reductions terminate on circular bounds without rejecting finite alias arguments.

use std::{fs, sync::Arc};

use bamts_compiler::{
    checker::{PropertyType, SymbolId, TypeTable, check},
    diagnostic::DiagnosticSeverity,
    parser,
    pipeline::{FrontendMode, compile_program_frontend},
    program::ProgramLoader,
    project::{ProjectConfig, ProjectRoot},
    scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checker_errors(source: &str) -> Vec<&'static str> {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let parsed = parser::parse(scanned);
    let checked = check(&parsed);
    parsed
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect()
}

#[test]
fn circular_index_bounds_report_an_error_and_continue_checking() {
    let source = r#"
class Keys { static x = 1; }
type Row = Record<keyof typeof Keys, number>;
declare function read<K extends L, L extends K>(value: Row[K]): void;
const later: number = "still checked";
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C064", "BAMTS-C004"]);
}

#[test]
fn union_bounds_index_every_member_and_reject_invalid_keys() {
    let source = r#"
class Keys { static x = 1; static y = 1; }
type Row = Record<keyof typeof Keys, boolean>;
function read<K extends "x" | "y">(value: Row[K]) {
    const accepted: boolean = value;
    const rejected: string = value;
}
function heterogeneous<K extends "x" | "y">(value: { x: number; y: string }[K]) {
    const accepted: number | string = value;
    const rejected: number = value;
}
declare function invalid<K extends "x" | "absent">(value: Row[K]): void;
"#;
    assert_eq!(
        checker_errors(source),
        ["BAMTS-C004", "BAMTS-C004", "BAMTS-C064"]
    );
}

#[test]
fn keyof_reads_through_finite_nested_alias_arguments() {
    let source = r#"
type Identity<T> = T;
type Wrapper<T> = Identity<T>;
const nested: keyof Identity<Identity<{ x: number }>> = "x";
const wrapped: keyof Identity<Wrapper<{ x: number }>> = "x";
const rejected: keyof Identity<Wrapper<{ x: number }>> = "absent";
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C004"]);
}

#[test]
fn keyof_reads_aliases_selected_from_an_immutable_input_property() {
    let source = r#"
type Value<T extends { value: object }> = T["value"];
const accepted: keyof Value<{ value: Value<{ value: { x: number } }> }> = "x";
const rejected: keyof Value<{ value: Value<{ value: { x: number } }> }> = "absent";
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C004"]);
}

#[test]
fn keyof_reads_aliases_selected_from_named_and_generic_input_containers() {
    for source in [
        r#"
type Value<T extends { value: object }> = T["value"];
type Box = { value: Value<{ value: { x: number } }> };
const accepted: keyof Value<Box> = "x";
const rejected: keyof Value<Box> = "absent";
"#,
        r#"
type Value<T extends { value: object }> = T["value"];
type Box<T extends object> = { value: Value<{ value: T }> };
const accepted: keyof Value<Box<{ x: number }>> = "x";
const rejected: keyof Value<Box<{ x: number }>> = "absent";
"#,
    ] {
        assert_eq!(checker_errors(source), ["BAMTS-C004"]);
    }
}

#[test]
fn alias_input_projection_survives_late_container_view_materialization() {
    let mut table = TypeTable::new();
    let value = SymbolId::new(1);
    let container = SymbolId::new(2);
    let parameter = SymbolId::new(3);
    table.declare_alias(value, vec![parameter]);
    table.declare_alias(container, vec![]);

    let leaf = table.object_type(vec![PropertyType::new("x", false, table.number())]);
    let input = table.object_type(vec![PropertyType::new("value", false, leaf)]);
    let boxed = table.applied_alias(container, vec![]);
    let outer = table.applied_alias(value, vec![boxed]);
    let inner = table.applied_alias(value, vec![input]);
    assert!(inner > outer);
    let box_view = table.object_type(vec![PropertyType::new("value", false, inner)]);
    table.set_applied_alias_view(boxed, box_view);

    let template_input = table.named(parameter);
    let index = table.string_literal("value");
    let template = table.indexed_access(template_input, index);
    table.publish_alias_template(value, template);

    let expected = table.string_literal("x");
    assert_eq!(table.keyof(outer), expected);
}

#[test]
fn alias_argument_descent_survives_late_view_materialization() {
    let mut table = TypeTable::new();
    let identity = SymbolId::new(1);
    let wrapper = SymbolId::new(2);
    let parameter = SymbolId::new(3);
    let identity_template = table.named(parameter);
    table.declare_alias(identity, vec![parameter]);
    table.publish_alias_template(identity, identity_template);
    table.declare_alias(wrapper, vec![parameter]);

    let object = table.object_type(vec![PropertyType::new("x", false, table.number())]);
    let wrapped = table.applied_alias(wrapper, vec![object]);
    let outer = table.applied_alias(identity, vec![wrapped]);
    let inner = table.applied_alias(identity, vec![object]);
    assert!(inner > outer);
    table.set_applied_alias_view(wrapped, inner);

    let expected = table.string_literal("x");
    assert_eq!(table.keyof(outer), expected);
}

#[test]
fn keyof_reads_through_imported_nested_alias_arguments() {
    let path = std::env::temp_dir().join(format!("bamts-key-reduction-{}", std::process::id()));
    fs::create_dir_all(&path).expect("create test project");
    fs::write(
        path.join("aliases.ts"),
        "export type Identity<T> = T; export type Wrapper<T> = Identity<T>;",
    )
    .expect("write alias module");
    fs::write(
        path.join("main.ts"),
        r#"
import type { Identity, Wrapper } from "./aliases.js";
type Keys = keyof Identity<Wrapper<{ x: number }>>;
const key: Keys = "x";
const rejected: Keys = "absent";
"#,
    )
    .expect("write importing module");
    let root = ProjectRoot::new(fs::canonicalize(&path).expect("canonical project path"))
        .expect("project root");
    let config = ProjectConfig::parse(&root, path.join("tsconfig.json"), "{}")
        .expect("project configuration");
    let loader = ProgramLoader::new(&root, config.options()).expect("project loader");
    let resolved = loader.load("main.ts").expect("load importing module");
    let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
    let codes: Vec<_> = frontend
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    fs::remove_dir_all(path).expect("remove test project");
    assert_eq!(codes, ["BAMTS-C004"]);
}

#[test]
fn keyof_still_rejects_growing_recursive_alias_expansions() {
    for source in [
        r#"
type Expanding<T> = Expanding<T[]>;
type Keys = keyof (Expanding<string> | { x: number });
"#,
        r#"
type First<T> = Second<T[]>;
type Second<T> = First<T[]>;
type Keys = keyof (First<string> | { x: number });
"#,
    ] {
        let codes = checker_errors(source);
        assert!(codes.contains(&"BAMTS-C072"), "{codes:?}\n{source}");
    }
    let branch = r#"
type Expanding<T> = T | Expanding<T[]>;
const rejected: keyof Expanding<{ x: number }> = "x";
"#;
    assert_eq!(checker_errors(branch), ["BAMTS-C004"]);
}

#[test]
fn indexed_access_diagnostics_keep_distinct_sites_and_honor_suppression() {
    let source = r#"
declare function first<K extends "missing">(value: { x: number }[K]): void;
declare function second<K extends "missing">(value: { x: number }[K]): void;
// @ts-expect-error
declare function suppressed<K extends "missing">(value: { x: number }[K]): void;
const later: number = "still checked";
"#;
    assert_eq!(
        checker_errors(source),
        ["BAMTS-C064", "BAMTS-C064", "BAMTS-C004"]
    );
}
