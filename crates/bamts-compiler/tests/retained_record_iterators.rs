//! Iterator protocols consume current shapes of retained record types.

use std::sync::Arc;

use bamts_compiler::{
    checker::{
        ProgramCheckInput, ProgramCheckOptions, SemanticModel, TypeId, check_program_with_options,
    },
    diagnostic::DiagnosticSeverity,
    lint::{LintProfile, LintTable},
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checked_model(source: &str, expected: &[&str]) -> SemanticModel {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let parsed = [parser::parse(scanned)];
    let checked = check_program_with_options(
        ProgramCheckInput {
            files: &parsed,
            edges: &[],
        },
        &LintTable::new(LintProfile::Default),
        ProgramCheckOptions::standard().with_strict_null_checks(true),
    );
    let codes: Vec<_> = parsed[0]
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert_eq!(codes, expected, "{source}");
    checked
        .into_product()
        .remove_file(SourceId::new(0))
        .expect("checked source model exists")
}

fn binding_type(model: &SemanticModel, name: &str) -> TypeId {
    let symbol = model
        .scopes()
        .iter()
        .find_map(|scope| scope.value(name))
        .unwrap_or_else(|| panic!("binding {name} exists"));
    model.symbol_type(symbol)
}

fn assert_binding_type(model: &SemanticModel, name: &str, expected: TypeId) {
    let actual = binding_type(model, name);
    assert_eq!(
        actual,
        expected,
        "{name}: {:?}, expected {:?}",
        model.types().get(actual),
        model.types().get(expected),
    );
}

#[test]
fn retained_record_iterator_yields_the_next_results_exact_value_type() {
    let model = checked_model(
        r#"
class IteratorKeys { static next = 0; }
declare const values: {
    [Symbol.iterator](): Record<keyof typeof IteratorKeys, () => { value: number; done: false }>;
};
for (const item of values) {
    const accepted: number = item;
    const rejected: string = item;
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", model.types().number());
}

#[test]
fn retained_record_iterator_result_yields_its_exact_value_type() {
    let model = checked_model(
        r#"
class ResultKeys { static value = 0; }
declare const values: {
    [Symbol.iterator](): { next(): Record<keyof typeof ResultKeys, string> };
};
for (const item of values) {
    const accepted: string = item;
    const rejected: number = item;
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", model.types().string());
}

#[test]
fn retained_record_done_results_do_not_contribute_yield_values() {
    let model = checked_model(
        r#"
class ResultKeys { static value = 0; static done = 0; }
declare const values: {
    [Symbol.iterator](): {
        next(): Record<keyof typeof ResultKeys, true> | { value: number; done: false };
    };
};
for (const item of values) {
    const accepted: number = item;
    const rejected: boolean = item;
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", model.types().number());
}

#[test]
fn async_iteration_awaits_next_results_and_preserves_structural_promise_values() {
    let model = checked_model(
        r#"
class IteratorKeys { static next = 0; }
class ResultKeys { static value = 0; }
declare const expected: Promise<number>;
declare const values: {
    [Symbol.asyncIterator](): Record<keyof typeof IteratorKeys,
        () => Promise<Record<keyof typeof ResultKeys, Promise<number>>>>;
};
async function consume() {
    for await (const item of values) {
        const accepted: Promise<number> = item;
        const rejected: number = item;
    }
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", binding_type(&model, "expected"));
}

#[test]
fn generic_iterable_inference_reads_retained_record_iterator_results() {
    let model = checked_model(
        r#"
class ResultKeys { static value = 0; }
declare function first<T>(values: {
    [Symbol.iterator](): { next(): { value: T; done?: boolean } };
}): T;
declare const values: {
    [Symbol.iterator](): { next(): Record<keyof typeof ResultKeys, number> };
};
const inferred = first(values);
const accepted: number = inferred;
const rejected: string = inferred;
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "inferred", model.types().number());
}

#[test]
fn malformed_retained_record_iterator_protocols_are_rejected() {
    for source in [
        r#"
class Keys { static next = 0; }
declare const values: { [Symbol.iterator](): Record<keyof typeof Keys, number> };
for (const item of values) { item; }
"#,
        r#"
class Keys { static other = 0; }
declare const values: {
    [Symbol.iterator](): Record<keyof typeof Keys, () => { value: number; done: false }>;
};
for (const item of values) { item; }
"#,
        r#"
class Keys { static done = 0; }
declare const values: { [Symbol.iterator](): { next(): Record<keyof typeof Keys, boolean> } };
for (const item of values) { item; }
"#,
    ] {
        checked_model(source, &["BAMTS-C065"]);
    }
}

#[test]
fn string_indexes_do_not_supply_missing_iterator_protocol_members() {
    for source in [
        r#"
            declare const values: {
                [Symbol.iterator](): {
                    [name: string]: () => { value: number; done: false };
                };
            };
            for (const item of values) { item; }
        "#,
        r#"
            class IteratorKeys { static other = 0; }
            declare const values: {
                [Symbol.iterator]():
                    Record<keyof typeof IteratorKeys, () => { value: number; done: false }>
                    & { [name: string]: () => { value: number; done: false } };
            };
            for (const item of values) { item; }
        "#,
        r#"
            declare const values: {
                [Symbol.iterator](): { next(): { [name: string]: number } };
            };
            for (const item of values) { item; }
        "#,
        r#"
            class ResultKeys { static other = 0; }
            declare const values: {
                [Symbol.iterator](): {
                    next(): Record<keyof typeof ResultKeys, number>
                        & { [name: string]: number };
                };
            };
            for (const item of values) { item; }
        "#,
    ] {
        checked_model(source, &["BAMTS-C065"]);
    }
}

#[test]
fn named_iterator_members_keep_their_types_beside_string_indexes() {
    let model = checked_model(
        r#"
            class IteratorKeys { static next = 0; }
            class ResultKeys { static value = 0; }
            declare const values: {
                [Symbol.iterator]():
                    Record<keyof typeof IteratorKeys,
                        () => Record<keyof typeof ResultKeys, number>>
                    & { [name: string]: () => { [name: string]: number } };
            };
            for (const item of values) {
                const accepted: number = item;
                const rejected: string = item;
            }
        "#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", model.types().number());
}

#[test]
fn optional_iterator_result_values_include_undefined_under_strict_null_checks() {
    for result in [
        "Partial<Record<keyof typeof ResultKeys, number>>",
        "{ value?: number; done?: false }",
    ] {
        let model = checked_model(
            &format!(
                r#"
                    class ResultKeys {{ static value = 0; }}
                    declare const expected: number | undefined;
                    declare const values: {{
                        [Symbol.iterator](): {{ next(): {result} }};
                    }};
                    for (const item of values) {{
                        const accepted: number | undefined = item;
                        const rejected: number = item;
                    }}
                "#
            ),
            &["BAMTS-C004"],
        );
        assert_binding_type(&model, "item", binding_type(&model, "expected"));
    }
}

#[test]
fn optional_done_does_not_discard_an_optional_yield_value() {
    let model = checked_model(
        r#"
            class ResultKeys { static value = 0; static done = 0; }
            declare const expected: true | undefined;
            declare const values: {
                [Symbol.iterator](): {
                    next(): Partial<Record<keyof typeof ResultKeys, true>>;
                };
            };
            for (const item of values) {
                const accepted: true | undefined = item;
                const rejected: true = item;
            }
        "#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", binding_type(&model, "expected"));
}

#[test]
fn an_optional_next_method_is_not_a_callable_iterator_protocol() {
    let source = r#"
        class IteratorKeys { static next = 0; }
        declare const values: {
            [Symbol.iterator]():
                Partial<Record<keyof typeof IteratorKeys, () => { value: number; done: false }>>;
        };
        for (const item of values) { item; }
    "#;
    checked_model(source, &["BAMTS-C065"]);
}

#[test]
fn generic_iterable_inference_keeps_the_declared_optional_payload() {
    let model = checked_model(
        r#"
            class ResultKeys { static value = 0; }
            declare function first<T>(values: {
                [Symbol.iterator](): { next(): { value?: T; done?: boolean } };
            }): T;
            declare const values: {
                [Symbol.iterator](): {
                    next(): Partial<Record<keyof typeof ResultKeys, number>>;
                };
            };
            const inferred = first(values);
            const accepted: number = inferred;
            const rejected: string = inferred;
        "#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "inferred", model.types().number());
}

#[test]
fn for_await_preserves_each_protocols_value_in_a_union() {
    let model = checked_model(
        r#"
declare const expected: Promise<number> | string;
declare const values: {
    [Symbol.asyncIterator](): { next(): Promise<{ value: Promise<number>; done: false }> };
} | {
    [Symbol.iterator](): { next(): { value: Promise<string>; done: false } };
};
async function consume() {
    for await (const item of values) {
        const accepted: Promise<number> | string = item;
        const rejected: number = item;
    }
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", binding_type(&model, "expected"));
}

#[test]
fn for_await_intersections_preserve_the_selected_async_protocol() {
    let model = checked_model(
        r#"
declare const expected: Promise<number>;
declare const values: {
    [Symbol.asyncIterator](): { next(): Promise<{ value: Promise<number>; done: false }> };
} & {
    [Symbol.iterator](): { next(): { value: string; done: false } };
};
async function consume() {
    for await (const item of values) {
        const accepted: Promise<number> = item;
        const rejected: number = item;
    }
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", binding_type(&model, "expected"));
}

#[test]
fn builtin_async_iterator_identity_survives_aliases_and_generic_instantiation() {
    let model = checked_model(
        r#"
type IteratorOf<T> = AsyncIterator<T, void, undefined>;
interface Stream<T> extends AsyncIterable<T> {}
declare const stream: Stream<Promise<number>>;
declare const direct: IteratorOf<Promise<number>>;
declare const aliased: { [Symbol.asyncIterator](): IteratorOf<Promise<number>> };
async function consume() {
    for await (const builtin of stream) {
        const accepted: number = builtin;
        const rejected: Promise<number> = builtin;
    }
    for await (const aliasValue of aliased) {
        const accepted: number = aliasValue;
        const rejected: Promise<number> = aliasValue;
    }
    const step = await direct.next();
    if (step.done === false) {
        const promised: Promise<number> = step.value;
        const rejected: number = step.value;
    }
}
"#,
        &["BAMTS-C004"; 3],
    );
    assert_binding_type(&model, "builtin", model.types().number());
    assert_binding_type(&model, "aliasValue", model.types().number());
}

#[test]
fn composed_async_iterators_do_not_gain_the_builtin_payload_shortcut() {
    let model = checked_model(
        r#"
interface Derived extends AsyncIterator<Promise<number>, void, undefined> {}
declare const expected: Promise<number>;
declare const derived: { [Symbol.asyncIterator](): Derived };
declare const intersected: {
    [Symbol.asyncIterator](): AsyncIterator<Promise<number>, void, undefined> & { tag: true };
};
async function consume() {
    for await (const derivedValue of derived) {
        const accepted: Promise<number> = derivedValue;
        const rejected: number = derivedValue;
    }
    for await (const intersectionValue of intersected) {
        const accepted: Promise<number> = intersectionValue;
        const rejected: number = intersectionValue;
    }
}
"#,
        &["BAMTS-C004"; 2],
    );
    let expected = binding_type(&model, "expected");
    assert_binding_type(&model, "derivedValue", expected);
    assert_binding_type(&model, "intersectionValue", expected);
}

#[test]
fn async_generator_delegation_awaits_structural_async_payloads() {
    let model = checked_model(
        r#"
declare const values: {
    [Symbol.asyncIterator](): { next(): Promise<{ value: Promise<number>; done: false }> };
};
async function* delegated() {
    yield* values;
}
async function consume() {
    for await (const item of delegated()) {
        const accepted: number = item;
        const rejected: string = item;
    }
}
"#,
        &["BAMTS-C004"],
    );
    assert_binding_type(&model, "item", model.types().number());
}

#[test]
fn async_iteration_awaits_array_and_structural_sync_fallback_payloads() {
    let model = checked_model(
        r#"
declare const array: Promise<number>[];
declare const structural: {
    [Symbol.iterator](): { next(): { value: Promise<number>; done: false } };
};
async function consume() {
    for await (const arrayValue of array) {
        const accepted: number = arrayValue;
        const rejected: Promise<number> = arrayValue;
    }
    for await (const structuralValue of structural) {
        const accepted: number = structuralValue;
        const rejected: Promise<number> = structuralValue;
    }
}
"#,
        &["BAMTS-C004"; 2],
    );
    assert_binding_type(&model, "arrayValue", model.types().number());
    assert_binding_type(&model, "structuralValue", model.types().number());
}

#[test]
fn imported_async_iterator_aliases_keep_builtin_and_structural_values_distinct() {
    use std::fs;

    use bamts_compiler::{
        pipeline::{FrontendMode, compile_program_frontend},
        program::ProgramLoader,
        project::{ProjectConfig, ProjectRoot},
    };

    let path = std::env::temp_dir().join(format!(
        "bamts-async-iterator-import-{}",
        std::process::id()
    ));
    fs::create_dir_all(&path).expect("create import fixture");
    fs::write(
        path.join("iterators.ts"),
        r#"
export type Builtin<T> = AsyncIterator<T, void, undefined>;
export type Structural<T> = { next(): Promise<{ value: T; done: false }> };
"#,
    )
    .expect("write exported iterator aliases");
    fs::write(
        path.join("main.ts"),
        r#"
import type { Builtin, Structural } from "./iterators.js";
declare const builtin: { [Symbol.asyncIterator](): Builtin<Promise<number>> };
declare const structural: { [Symbol.asyncIterator](): Structural<Promise<number>> };
async function consume() {
    for await (const value of builtin) {
        const accepted: number = value;
        const rejected: Promise<number> = value;
    }
    for await (const value of structural) {
        const accepted: Promise<number> = value;
        const rejected: number = value;
    }
}
"#,
    )
    .expect("write importing fixture");
    let root = ProjectRoot::new(fs::canonicalize(&path).expect("canonical import fixture"))
        .expect("project root");
    let config = ProjectConfig::parse(&root, path.join("tsconfig.json"), "{}")
        .expect("project configuration");
    let loader = ProgramLoader::new(&root, config.options()).expect("project loader");
    let program = loader.load("main.ts").expect("load importing source");
    let frontend = compile_program_frontend(&program, FrontendMode::Check);
    let codes: Vec<_> = frontend
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    fs::remove_dir_all(path).expect("remove import fixture");
    assert_eq!(codes, ["BAMTS-C004"; 2]);
}

#[test]
fn neutral_iterator_intersections_preserve_only_one_builtin_identity() {
    for (iterator, builtin) in [
        ("Builtin & {}", true),
        ("Builtin & unknown", true),
        ("Builtin & Builtin", true),
        ("Builtin & Empty", true),
        ("Builtin & Neutral", true),
        ("(Builtin & Empty) & Neutral", true),
        ("Builtin & object", false),
        ("Builtin & { tag: true }", false),
    ] {
        let (expected, rejected) = if builtin {
            ("number", "Promise<number>")
        } else {
            ("Promise<number>", "number")
        };
        let model = checked_model(
            &format!(
                r#"
type Builtin = AsyncIterator<Promise<number>, void, undefined>;
type Empty = {{}};
type Neutral = unknown;
declare const expected: {expected};
declare const values: {{ [Symbol.asyncIterator](): {iterator} }};
async function consume() {{
    for await (const item of values) {{
        const accepted: {expected} = item;
        const rejected: {rejected} = item;
    }}
}}
"#
            ),
            &["BAMTS-C004"],
        );
        assert_binding_type(&model, "item", binding_type(&model, "expected"));
    }
}

#[test]
fn returned_builtin_async_iterators_preserve_iteration_and_direct_next_types() {
    for iterator in ["AsyncIterator", "AsyncIterableIterator", "AsyncGenerator"] {
        let model = checked_model(
            &format!(
                r#"
declare const direct: {iterator}<Promise<number>, void, undefined>;
declare const values: {{
    [Symbol.asyncIterator](): {iterator}<Promise<number>, void, undefined>;
}};
async function consume() {{
    for await (const item of values) {{
        const accepted: number = item;
        const rejected: Promise<number> = item;
    }}
    const step = await direct.next();
    if (step.done === false) {{
        const promised: Promise<number> = step.value;
        const rejected: number = step.value;
    }}
}}
"#
            ),
            &["BAMTS-C004"; 2],
        );
        assert_binding_type(&model, "item", model.types().number());
    }
}
