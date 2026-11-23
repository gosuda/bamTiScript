//! Key reductions terminate on circular bounds without rejecting finite alias arguments.

use std::{fs, sync::Arc};

use bamts_compiler::{
    checker::{
        ProgramCheckInput, ProgramCheckOptions, PropertyType, SemanticModel, SymbolId, TypeId,
        TypeTable, check, check_program_with_options,
    },
    diagnostic::DiagnosticSeverity,
    lint::{LintProfile, LintTable},
    parser,
    pipeline::{FrontendMode, compile_program_frontend},
    program::ProgramLoader,
    project::{ProjectConfig, ProjectRoot},
    scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checker_output(source: &str) -> (Vec<&'static str>, SemanticModel) {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let parsed = parser::parse(scanned);
    let checked = check(&parsed);
    let errors = parsed
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    (errors, checked.into_product())
}

fn checker_errors(source: &str) -> Vec<&'static str> {
    checker_output(source).0
}

fn strict_checker_output(source: &str) -> (Vec<&'static str>, SemanticModel) {
    let source_id = SourceId::new(0);
    let files = [parser::parse(scanner::scan(
        source_id,
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    ))];
    let checked = check_program_with_options(
        ProgramCheckInput {
            files: &files,
            edges: &[],
        },
        &LintTable::new(LintProfile::Default),
        ProgramCheckOptions::standard().with_strict_null_checks(true),
    );
    let errors = files[0]
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    let model = checked
        .into_product()
        .remove_file(source_id)
        .expect("checked file");
    (errors, model)
}

fn binding_type(model: &SemanticModel, name: &str) -> TypeId {
    let symbol = model
        .scopes()
        .iter()
        .find_map(|scope| scope.value(name))
        .unwrap_or_else(|| panic!("binding {name} exists"));
    let mut value = model.symbol_type(symbol);
    let mut seen = std::collections::HashSet::new();
    while let Some(view) = model.types().applied_alias_view(value) {
        assert!(seen.insert(value), "cyclic fixture alias for {name}");
        value = view;
    }
    value
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
fn generic_indexed_calls_keep_each_keys_argument_and_return_type() {
    let source = r#"
type Row = { x: number; y: string };
declare function select<K extends "x" | "y">(key: K, value: Row[K]): Row[K];
const inferredX = select("x", 1);
const inferredY = select("y", "accepted");
const explicitX = select<"x">("x", 1);
const explicitY = select<"y">("y", "accepted");
const acceptedX: number = inferredX;
const acceptedY: string = inferredY;
select("x", "wrong");
select("y", 1);
select<"x">("x", "wrong");
select<"y">("y", 1);
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C053"; 4]);
    for name in ["inferredX", "explicitX"] {
        assert_eq!(binding_type(&model, name), model.types().number(), "{name}");
    }
    for name in ["inferredY", "explicitY"] {
        assert_eq!(binding_type(&model, name), model.types().string(), "{name}");
    }
}

#[test]
fn generic_indexed_aliases_keep_each_substituted_keys_value_type() {
    let source = r#"
type Row = { x: number; y: string };
type Value<K extends "x" | "y"> = Row[K];
declare const valueX: Value<"x">;
declare const valueY: Value<"y">;
const acceptedX: number = valueX;
const acceptedY: string = valueY;
const rejectedX: Value<"x"> = "wrong";
const rejectedY: Value<"y"> = 1;
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"; 2]);
    assert_eq!(binding_type(&model, "valueX"), model.types().number());
    assert_eq!(binding_type(&model, "valueY"), model.types().string());
}

#[test]
fn generic_indexed_targets_require_a_value_accepted_by_every_possible_key() {
    let source = r#"
type Uniform = { x: boolean; y: boolean };
function uniform<K extends "x" | "y">(key: K): Uniform[K] {
    const value: Uniform[K] = true;
    return value;
}
type Overlap = { x: number | string; y: string | boolean };
function overlap<K extends "x" | "y">(key: K): Overlap[K] {
    const value: Overlap[K] = "common";
    return value;
}
type Heterogeneous = { x: number; y: string };
function rejected<K extends "x" | "y">(key: K): Heterogeneous[K] {
    const value: Heterogeneous[K] = 1;
    return value;
}
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C004"]);
}

#[test]
fn generic_indexed_targets_keep_fixed_object_union_values_together() {
    let source = r#"
type Row = { x: number; y: string } | { x: string; y: number };
function numberValue<K extends "x" | "y">(): Row[K] { return 1; }
function stringValue<K extends "x" | "y">(): Row[K] { return "accepted"; }
declare const expected: number | string;
const resultX = numberValue<"x">();
const resultY = stringValue<"y">();
function rejected<K extends "x" | "y">() {
    const value: Row[K] = true;
}
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"]);
    let expected = binding_type(&model, "expected");
    assert_eq!(binding_type(&model, "resultX"), expected);
    assert_eq!(binding_type(&model, "resultY"), expected);
}

#[test]
fn generic_indexed_targets_preserve_never_unknown_and_nullish_rules() {
    let source = r#"
type Opaque = { x: unknown; y: unknown };
function opaque<K extends "x" | "y">(source: unknown): Opaque[K] {
    return source;
}
function bottom<T, K extends keyof T>(source: never): T[K] {
    return source;
}
function nullish<T, K extends keyof T>(): T[K] { return undefined; }
type Numeric = { x: number; y: number };
function uninhabited<K extends never>(): Numeric[K] { return undefined; }
const rejected: Numeric[never] = undefined;
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C004"]);
}

#[test]
fn generic_object_bounds_do_not_prove_an_indexed_target_accepts_the_bound() {
    let source = r#"
function fixedKey<T extends { x: number }, K extends "x">(value: T[K]): T[K] {
    const accepted: T[K] = value;
    return accepted;
}
function objectKeys<T extends { x: number }, K extends keyof T>(value: T[K]): T[K] {
    const accepted: T[K] = value;
    const rejected: T[K] = 1;
    return accepted;
}
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C004"]);
}

#[test]
fn indexed_key_alias_bounds_keep_relation_evidence_and_never_stays_uninhabited() {
    let source = r#"
type Keys = "x" | "y";
type Row = { x: number; y: string };
type WrappedRow = Row;
function read<K extends Keys>(value: WrappedRow[K]) {
    const accepted: number | string = value;
    const rejected: boolean = value;
}
function impossible<K extends never>(value: Row[K]) {
    const accepted: Row[K] = value;
    const rejected: Row[K] = 1;
}
declare function invalid<K extends "x" | "absent" | never>(value: Row[K]): void;
"#;
    assert_eq!(
        checker_errors(source),
        ["BAMTS-C004", "BAMTS-C004", "BAMTS-C064"]
    );
}

#[test]
fn numeric_tuple_keys_keep_the_pinned_broad_index_behavior() {
    let source = r#"
type Pair = [number, string];
function broad<K extends number>(): Pair[K] { return 1; }
function read<K extends number>(value: Pair[K]): number | string { return value; }
type Overlap = [number | string, number | boolean];
function overlap<K extends number>(): Overlap[K] { return "accepted"; }
function literal<K extends 0 | 1>(): Pair[K] { return 1; }
type Empty = [];
function empty<K extends number>(): Empty[K] { return 1; }
const first = broad<0>();
const second = broad<1>();
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"; 2]);
    assert_eq!(binding_type(&model, "first"), model.types().number());
    assert_eq!(binding_type(&model, "second"), model.types().string());
}

#[test]
fn generic_indexed_sources_match_their_identity_inside_target_unions() {
    let source = r#"
type Row = { x: number; y: string };
function optional<K extends "x" | "y">(value: Row[K]): Row[K] | undefined { return value; }
function widen<K extends "x" | "y">(value: Row[K]): number | string | undefined { return value; }
declare function accept<K extends "x" | "y">(key: K, value?: Row[K]): void;
function forward<K extends "x" | "y">(key: K, value: Row[K]) { accept<K>(key, value); }
function independent<K extends "x" | "y", P extends "x" | "y">(value: Row[K]): Row[P] | undefined {
    return value;
}
function incomplete<K extends "x" | "y">(value: Row[K]): number | undefined { return value; }
const optionalX = optional<"x">(1);
const optionalY = optional<"y">("accepted");
declare const expectedX: number | undefined;
declare const expectedY: string | undefined;
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"; 2]);
    assert_eq!(
        binding_type(&model, "optionalX"),
        binding_type(&model, "expectedX")
    );
    assert_eq!(
        binding_type(&model, "optionalY"),
        binding_type(&model, "expectedY")
    );
}

#[test]
fn renamed_generic_indexed_signatures_keep_their_parameter_correlations() {
    let source = r#"
type Row = { x: number; y: string };
declare const original: <K extends "x" | "y">(key: K) => Row[K];
const renamed: <P extends "x" | "y">(key: P) => Row[P] = original;
const first = renamed("x");
const second = renamed<"y">("y");
declare const independent: <K extends "x" | "y", P extends "x" | "y">(key: K, other: P) => Row[P];
const paired: <A extends "x" | "y", B extends "x" | "y">(key: A, other: B) => Row[B] = independent;
const wrongKey: <A extends "x" | "y", B extends "x" | "y">(key: A, other: B) => Row[A] = independent;
type Reversed = { x: string; y: number };
const wrongObject: <P extends "x" | "y">(key: P) => Reversed[P] = original;
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"; 2]);
    assert_eq!(binding_type(&model, "first"), model.types().number());
    assert_eq!(binding_type(&model, "second"), model.types().string());
}

#[test]
fn generic_indexed_targets_check_union_source_members_independently() {
    let source = r#"
type Row = { x: number | string; y: number | string };
type Payload = number | string;
function direct<K extends "x" | "y">(value: number | string): Row[K] { return value; }
function alias<K extends "x" | "y">(value: Payload): Row[K] { return value; }
function generic<V extends Payload, K extends "x" | "y">(value: V): Row[K] { return value; }
function rejected<K extends "x" | "y">(value: number | boolean): Row[K] { return value; }
type Overlap = { x: number | string; y: string | boolean };
function common<K extends "x" | "y">(value: string): Overlap[K] { return value; }
function incomplete<K extends "x" | "y">(value: Payload): Overlap[K] { return value; }
function compare<K extends "x" | "y">(comparableSource: number | boolean, comparableTarget: Row[K]) {}
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"; 2]);
    let source = binding_type(&model, "comparableSource");
    let target = binding_type(&model, "comparableTarget");
    assert!(!model.types().assignable_with_strict_null(source, target));
    assert!(model.types().comparable(source, target));
    assert!(!model.types().comparable(model.types().boolean(), target));
}

#[test]
fn generic_tuple_lengths_keep_exact_finite_and_variadic_bounds() {
    let source = r#"
type Pair = [number, string];
function read<K extends "length">(value: Pair[K]): 2 { return value; }
function readNumber<K extends "length">(value: Pair[K]): number { return value; }
function write<K extends "length">(): Pair[K] { return 2; }
function wrongRead<K extends "length">(value: Pair[K]): 3 { return value; }
function wrongWrite<K extends "length">(): Pair[K] { return 3; }
type Optional = [number, string?];
function readOptional<K extends "length">(value: Optional[K]): 1 | 2 { return value; }
function writeOptional<K extends "length">(value: 1 | 2): Optional[K] { return value; }
function wrongOptional<K extends "length">(): Optional[K] { return 3; }
type Variadic = [number, ...string[]];
function readVariadic<K extends "length">(value: Variadic[K]): number { return value; }
function writeVariadic<K extends "length">(value: number): Variadic[K] { return value; }
declare function invalid<K extends "length" | "absent">(value: Pair[K]): void;
declare function select<K extends "length">(key: K): Pair[K];
declare function selectOptional<K extends "length">(key: K): Optional[K];
declare function selectVariadic<K extends "length">(key: K): Variadic[K];
const fixedLength = select("length");
const optionalLength = selectOptional("length");
const variadicLength = selectVariadic("length");
declare const expectedFixed: 2;
declare const expectedOptional: 1 | 2;
"#;
    let (errors, model) = checker_output(source);
    assert_eq!(
        errors,
        ["BAMTS-C004", "BAMTS-C004", "BAMTS-C004", "BAMTS-C064"]
    );
    assert_eq!(
        binding_type(&model, "fixedLength"),
        binding_type(&model, "expectedFixed")
    );
    assert_eq!(
        binding_type(&model, "optionalLength"),
        binding_type(&model, "expectedOptional")
    );
    assert_eq!(
        binding_type(&model, "variadicLength"),
        model.types().number()
    );
}

#[test]
fn intersection_key_bounds_keep_string_map_read_and_write_evidence() {
    let source = r#"
type Key<T> = keyof T & string;
function read<T, K extends Key<T>>(values: { [key: string]: number }, key: K): number {
    return values[key];
}
function write<T, K extends Key<T>>(values: { [key: string]: number }, key: K, value: number) {
    values[key] = value;
    values[key] = "wrong";
}
type Entry<T> = { to: Key<T> };
function save<T extends Record<string, unknown>, K extends Key<T>>(name: K, value: Key<T> | Entry<T>) {
    const output: Record<string, Entry<T>> = {};
    if (typeof value === "string") {
        output[name] = { to: value };
    } else {
        output[name] = value;
    }
}
"#;
    assert_eq!(checker_errors(source), ["BAMTS-C004"]);
}

#[test]
fn indexed_read_iteration_keeps_nullable_and_noniterable_members_rejected() {
    let source = r#"
type Row = { x: number[]; y: string[] };
function iterate<K extends "x" | "y">(value: Row[K]) {
    for (const item of value) {
        const accepted: number | string = item;
        const rejected: boolean = item;
    }
}
type Nullable = { x: number[] | undefined; y: string[] | undefined };
function nullable<K extends "x" | "y">(value: Nullable[K]) {
    for (const item of value) {}
}
type Mixed = { x: number[]; y: number };
function mixed<K extends "x" | "y">(value: Mixed[K]) {
    for (const item of value) {}
}
"#;
    assert_eq!(
        strict_checker_output(source).0,
        ["BAMTS-C004", "BAMTS-C065", "BAMTS-C065"]
    );
}

#[test]
fn indexed_nullable_fallbacks_keep_correlation_and_iterable_read_evidence() {
    let source = r#"
type Row = { x: number[] | undefined; y: string[] | undefined };
function preserve<K extends "x" | "y">(value: Row[K]): Row[K] {
    const disjunction = value || [];
    const coalesced = value ?? [];
    const same: Row[K] = disjunction;
    for (const item of disjunction) { const accepted: number | string = item; }
    for (const item of coalesced) { const accepted: number | string = item; }
    return coalesced;
}
function nestedUnion<K extends "x" | "y">(value: Row[K] | null) {
    const fallback = value || [];
    for (const item of fallback) { const accepted: number | string = item; }
}
function independent<K extends "x" | "y", P extends "x" | "y">(value: Row[K]): Row[P] {
    return value ?? [];
}
const selectedX = preserve<"x">([1]);
const selectedY = preserve<"y">(["accepted"]);
declare const expectedX: number[] | undefined;
declare const expectedY: string[] | undefined;
const wrongX: string[] | undefined = selectedX;
const wrongY: number[] | undefined = selectedY;
"#;
    let (errors, model) = strict_checker_output(source);
    assert_eq!(errors, ["BAMTS-C004"; 3]);
    assert_eq!(
        binding_type(&model, "selectedX"),
        binding_type(&model, "expectedX")
    );
    assert_eq!(
        binding_type(&model, "selectedY"),
        binding_type(&model, "expectedY")
    );
}

#[test]
fn narrowed_indexed_arrays_keep_prototype_members_and_argument_checks() {
    let source = r#"
type Key<T> = keyof T & string;
function append<T, K extends Key<T>>(values: { [key: string]: number[] | undefined }, key: K) {
    const length = values[key]!.push(1);
    const accepted: number = length;
    (values[key] || []).push(1);
    (values[key] ?? []).push(1);
    values[key]!.push("wrong");
    values[key]!.absent();
}
declare const enriched: number[] & { label: string };
const label: string = enriched.label;
enriched.push(1);
"#;
    let (errors, model) = strict_checker_output(source);
    assert_eq!(errors, ["BAMTS-C053", "BAMTS-C057"]);
    assert_eq!(binding_type(&model, "length"), model.types().number());
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
