//! Iterator protocols consume current shapes of retained record types.

use std::sync::Arc;

use bamts_compiler::{
    checker::{SemanticModel, TypeId, check},
    diagnostic::DiagnosticSeverity,
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checked_model(source: &str, expected: &[&str]) -> SemanticModel {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let parsed = parser::parse(scanned);
    let checked = check(&parsed);
    let codes: Vec<_> = parsed
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert_eq!(codes, expected, "{source}");
    checked.into_product()
}

fn assert_binding_type(model: &SemanticModel, name: &str, expected: TypeId) {
    let symbol = model
        .scopes()
        .iter()
        .find_map(|scope| scope.value(name))
        .unwrap_or_else(|| panic!("binding {name} exists"));
    let actual = model.symbol_type(symbol);
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
