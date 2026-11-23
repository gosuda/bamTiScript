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
fn async_iteration_awaits_retained_record_next_results_and_values() {
    let model = checked_model(
        r#"
class IteratorKeys { static next = 0; }
class ResultKeys { static value = 0; }
declare const values: {
    [Symbol.asyncIterator](): Record<keyof typeof IteratorKeys,
        () => Promise<Record<keyof typeof ResultKeys, Promise<number>>>>;
};
async function consume() {
    for await (const item of values) {
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
