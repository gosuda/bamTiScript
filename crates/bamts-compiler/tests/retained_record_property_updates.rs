//! Optional record updates retain defaults and strict-null write semantics.

use std::sync::Arc;

use bamts_compiler::{
    checker::{
        ProgramCheckInput, ProgramCheckOptions, ResolvedModuleEdge, SemanticModel, TypeId,
        check_program_with_options,
    },
    diagnostic::DiagnosticSeverity,
    lint::{LintProfile, LintTable},
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checked_model(source: &str, kind: ScriptKind, expected: &[&str]) -> SemanticModel {
    checked_linked_model(&[(source, kind)], &[], 0, expected)
}

fn checked_linked_model(
    sources: &[(&str, ScriptKind)],
    edges: &[(usize, usize, usize)],
    result: usize,
    expected: &[&str],
) -> SemanticModel {
    let source_id = |index| SourceId::new(u32::try_from(index).expect("fixture index fits"));
    let files: Vec<_> = sources
        .iter()
        .enumerate()
        .map(|(index, (source, kind))| {
            parser::parse(scanner::scan(
                source_id(index),
                *kind,
                Arc::new(SourceText::new(*source).expect("fixture source fits")),
            ))
        })
        .collect();
    let edges: Vec<_> = edges
        .iter()
        .map(|&(from, statement, to)| ResolvedModuleEdge {
            from: source_id(from),
            specifier: files[from].product().statements()[statement].id(),
            to: source_id(to),
        })
        .collect();
    let checked = check_program_with_options(
        ProgramCheckInput {
            files: &files,
            edges: &edges,
        },
        &LintTable::new(LintProfile::Default),
        ProgramCheckOptions::standard().with_strict_null_checks(true),
    );
    let codes: Vec<_> = files
        .iter()
        .flat_map(|file| file.diagnostics())
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert_eq!(codes, expected, "{sources:?}");
    let mut program = checked.into_product();
    program
        .remove_file(source_id(result))
        .expect("fixture semantic model")
}

fn binding_type(model: &SemanticModel, name: &str) -> TypeId {
    let symbol = model
        .scopes()
        .iter()
        .find_map(|scope| scope.value(name))
        .unwrap_or_else(|| panic!("binding {name} exists"));
    model.symbol_type(symbol)
}

#[test]
fn optional_record_spreads_preserve_required_defaults_and_value_unions() {
    let model = checked_model(
        r#"
class Keys { static value = 0; }
declare const optional: Partial<Record<keyof typeof Keys, number>>;
declare const replacement: Record<keyof typeof Keys, string>;
declare const unionExpected: number | string;
const numberDefault = { value: 0, ...optional };
const numberShape: { value: number } = numberDefault;
const numberValue = numberDefault.value;
const mixedDefault = { value: "fallback", ...optional };
const mixedShape: { value: number | string } = mixedDefault;
const mixedValue = mixedDefault.value;
const requiredReplacement = { value: 0, ...replacement };
const stringValue = requiredReplacement.value;
const wrongNumber: string = numberDefault.value;
const wrongUnion: boolean = mixedDefault.value;
const wrongReplacement: number = requiredReplacement.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 3],
    );
    assert_eq!(binding_type(&model, "numberValue"), model.types().number());
    assert_eq!(
        binding_type(&model, "mixedValue"),
        binding_type(&model, "unionExpected"),
    );
    assert_eq!(binding_type(&model, "stringValue"), model.types().string());
}

#[test]
fn optional_record_spreads_preserve_absence_and_explicit_undefined() {
    let model = checked_model(
        r#"
class Keys { static value = 0; }
declare const optional: Partial<Record<keyof typeof Keys, number>>;
declare const explicit: Partial<Record<keyof typeof Keys, number | undefined>>;
declare const expected: number | undefined;
const noDefault = { ...optional };
const missingDefault: { value: number } = noDefault;
const maybeValue = noDefault.value;
const withDefault = { value: 0, ...explicit };
const explicitValue = withDefault.value;
const unsafe: number = withDefault.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 2],
    );
    let expected = binding_type(&model, "expected");
    assert_eq!(binding_type(&model, "maybeValue"), expected);
    assert_eq!(binding_type(&model, "explicitValue"), expected);
}

#[test]
fn jsx_optional_record_spreads_preserve_defaults_without_hiding_overrides() {
    checked_model(
        r#"
namespace JSX {
    interface Element {}
    interface IntrinsicElements {
        div: { value: number };
        span: { value: number | string };
    }
}
class Keys { static value = 0; }
declare const optional: Partial<Record<keyof typeof Keys, number>>;
declare const strings: Partial<Record<keyof typeof Keys, string>>;
declare const required: Record<keyof typeof Keys, number>;
const accepted = <div value={0} {...optional} />;
const mixed = <span value={0} {...strings} />;
const replaced = <div value={"fallback"} {...required} />;
const wrongOverride = <div value={0} {...strings} />;
const missingDefault = <div {...optional} />;
"#,
        ScriptKind::TypeScriptReact,
        &["BAMTS-C022"; 2],
    );
}

#[test]
fn optional_record_writes_admit_undefined_without_erasing_value_checks() {
    checked_model(
        r#"
class Keys { static value = 0; }
type Fields<T> = Partial<Record<keyof typeof Keys, T>>;
declare let optional: Fields<number>;
declare let ordinary: { value?: number };
declare let intersected: Fields<number> & { tag: string };
declare let required: Record<keyof typeof Keys, number>;
declare const unread: Fields<number>;
optional.value = undefined;
optional["value"] = undefined;
ordinary.value = undefined;
intersected.value = undefined;
optional.value = 1;
const safe: number | undefined = unread.value;
required.value = undefined;
optional.value = "wrong";
ordinary.value = "wrong";
const unsafe: number = unread.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 4],
    );
}

#[test]
fn guarded_optional_bigint_updates_keep_read_and_written_numeric_types() {
    for fields in [
        "Partial<Record<keyof typeof Keys, bigint>>",
        "{ value?: bigint }",
    ] {
        let model = checked_model(
            &format!(
                r#"
class Keys {{ static value = 0; }}
declare const value: {fields};
if (value.value !== undefined) {{
    const post = value.value++;
    const afterPost = value.value;
    const prefix = ++value.value;
    const postDecrement = value.value--;
    const prefixDecrement = --value.value;
    const indexed = value["value"]++;
    const afterIndexed = value.value;
    const accepted: bigint = prefixDecrement;
    const rejected: number = post;
    const rejectedAfter: number = afterIndexed;
}}
"#
            ),
            ScriptKind::TypeScript,
            &["BAMTS-C004"; 2],
        );
        for name in [
            "post",
            "afterPost",
            "prefix",
            "postDecrement",
            "prefixDecrement",
            "indexed",
            "afterIndexed",
        ] {
            assert_eq!(binding_type(&model, name), model.types().bigint(), "{name}");
        }
    }
}

#[test]
fn updates_preserve_guarded_roots_numeric_unions_and_literal_widening() {
    let model = checked_model(
        r#"
declare let root: bigint | undefined;
declare const numeric: { value?: number };
declare let mixed: bigint | number;
declare const expected: bigint | number;
declare const literal: { value?: 1n };
if (typeof root === "bigint") {
    const rootPost = root++;
    const rootAfter = root;
    const rejectedRoot: number = rootPost;
}
if (numeric.value !== undefined) {
    const numberPrefix = --numeric.value;
    const numberPost = numeric.value++;
    const numberAfter = numeric.value;
    const rejectedNumber: bigint = numberPrefix;
}
const mixedPost = mixed++;
const mixedAfter = mixed;
const rejectedMixed: number = mixedPost;
if (literal.value !== undefined) {
    const literalPost = literal.value++;
    const literalAfter = literal.value;
    const accepted: bigint = literalAfter;
    const rejectedLiteral: 1n = literalAfter;
}
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 4],
    );
    for name in ["rootPost", "rootAfter", "literalPost", "literalAfter"] {
        assert_eq!(binding_type(&model, name), model.types().bigint(), "{name}");
    }
    for name in ["numberPrefix", "numberPost", "numberAfter"] {
        assert_eq!(binding_type(&model, name), model.types().number(), "{name}");
    }
    for name in ["mixedPost", "mixedAfter"] {
        assert_eq!(
            binding_type(&model, name),
            binding_type(&model, "expected"),
            "{name}"
        );
    }
}

#[test]
fn nullable_updates_report_the_read_without_narrowing_an_unsafe_write() {
    let model = checked_model(
        r#"
declare const optional: { value?: bigint };
declare let nullable: bigint | null | undefined;
declare const guarded: { value?: bigint };
declare const required: { value: bigint };
const unsafePost = optional.value++;
const unsafeAfter: bigint = optional.value;
const unsafePrefix = ++nullable;
const unsafeRootAfter: bigint = nullable;
if (guarded.value !== undefined) {
    guarded["value"] = undefined;
    const invalidated = guarded.value++;
}
optional.value = undefined;
required.value = undefined;
"#,
        ScriptKind::TypeScript,
        &[
            "BAMTS-C062",
            "BAMTS-C004",
            "BAMTS-C062",
            "BAMTS-C004",
            "BAMTS-C062",
            "BAMTS-C004",
        ],
    );
    for name in ["unsafePost", "unsafePrefix"] {
        assert_eq!(binding_type(&model, name), model.types().bigint(), "{name}");
    }
}

#[test]
fn nullable_aliases_and_constraints_keep_unsafe_update_flow() {
    let model = checked_model(
        r#"
type MaybeBigInt = bigint | undefined;
declare let hidden: MaybeBigInt | number;
declare const expected: bigint | number;
const hiddenResult = hidden++;
const hiddenAfter = hidden;
const resultAccepted: bigint | number = hiddenResult;
const afterRejected: bigint | number = hiddenAfter;
function nullableConstraint<T extends MaybeBigInt>(nullable: T): T {
    const constraintPost = nullable++;
    const constraintAfter = nullable;
    const resultAccepted: number = constraintPost;
    const afterRejected: bigint = constraintAfter;
    return nullable;
}
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C062", "BAMTS-C004", "BAMTS-C062", "BAMTS-C004"],
    );
    assert_eq!(
        binding_type(&model, "hiddenResult"),
        binding_type(&model, "expected"),
    );
    for (after, operand) in [("hiddenAfter", "hidden"), ("constraintAfter", "nullable")] {
        assert_eq!(binding_type(&model, after), binding_type(&model, operand));
    }
    assert_eq!(
        binding_type(&model, "constraintPost"),
        model.types().number()
    );
}

#[test]
fn generic_numeric_updates_preserve_written_identity_and_expression_types() {
    let model = checked_model(
        r#"
function updateBigInt<T extends bigint>(big: T): T {
    const bigPost = big++;
    const bigPrefix = --big;
    const bigAfter = big;
    const afterAccepted: bigint = bigAfter;
    const afterRejected: number = bigAfter;
    const resultAccepted: number = bigPrefix;
    const resultRejected: bigint = bigPost;
    return big;
}
function updateNumber<T extends number>(numeric: T): T {
    const numberPost = numeric--;
    const numberPrefix = ++numeric;
    const numberAfter = numeric;
    const afterAccepted: number = numberAfter;
    const afterRejected: bigint = numberAfter;
    const resultAccepted: number = numberPost;
    const resultRejected: bigint = numberPrefix;
    return numeric;
}
function updateConstrained<T extends bigint, U extends T>(constrained: U): U {
    const chainedPost = constrained++;
    const chainedAfter = constrained;
    const afterAccepted: bigint = chainedAfter;
    const afterRejected: number = chainedAfter;
    const resultAccepted: number = chainedPost;
    const resultRejected: bigint = chainedPost;
    return constrained;
}
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 6],
    );
    for name in [
        "bigPost",
        "bigPrefix",
        "numberPost",
        "numberPrefix",
        "chainedPost",
    ] {
        assert_eq!(binding_type(&model, name), model.types().number(), "{name}");
    }
    for (after, operand) in [
        ("bigAfter", "big"),
        ("numberAfter", "numeric"),
        ("chainedAfter", "constrained"),
    ] {
        assert_eq!(binding_type(&model, after), binding_type(&model, operand));
    }
}

#[test]
fn constant_key_writes_invalidate_updated_optional_properties() {
    for key in [
        "declare const key: 'value';",
        "type Key = 'value'; declare const key: Key;",
        "type Id<T> = T; type Key = Id<'value'>; declare const key: Key;",
        "type Id<T> = T; type Other<T> = T; declare const key: Id<'value'> | Other<'value'>;",
        "declare const original: 'value'; declare const key: typeof original;",
        "const key = 'value';",
        "const key: 'value' | 'other' = 'value';",
        "const original: 'value' | 'other' = 'value'; const key = original;",
    ] {
        for fields in [
            "Partial<Record<keyof typeof Keys, bigint>>",
            "{ value?: bigint; other?: bigint }",
        ] {
            let model = checked_model(
                &format!(
                    r#"
class Keys {{ static value = 0; static other = 0; }}
{key}
declare const guarded: {fields};
declare const expected: bigint | undefined;
if (guarded.value !== undefined && guarded.other !== undefined) {{
    guarded.value++;
    guarded.other++;
    guarded[key] = undefined;
    const after = guarded.value;
    const untouched = guarded.other;
    const accepted: bigint = untouched;
    const rejected: bigint = after;
    guarded.value++;
}}
"#
                ),
                ScriptKind::TypeScript,
                &["BAMTS-C004", "BAMTS-C062"],
            );
            assert_eq!(
                binding_type(&model, "after"),
                binding_type(&model, "expected"),
            );
            assert_eq!(binding_type(&model, "untouched"), model.types().bigint());
        }
    }
}

#[test]
fn mutable_and_ambiguous_key_writes_keep_reference_flow_behavior() {
    for key in [
        "let key: 'value' = 'value';",
        "declare const key: 'value' | 'other';",
        "type Key = 'value' | 'other'; declare const key: Key;",
        "declare const key: string;",
    ] {
        let model = checked_model(
            &format!(
                r#"
{key}
declare const guarded: {{ value?: bigint; other?: bigint; [name: string]: bigint | undefined }};
if (guarded.value !== undefined) {{
    guarded.value++;
    guarded[key] = undefined;
    const after = guarded.value;
    const accepted: bigint = after;
}}
"#
            ),
            ScriptKind::TypeScript,
            &[],
        );
        assert_eq!(binding_type(&model, "after"), model.types().bigint());
    }
}

#[test]
fn nested_constant_key_writes_invalidate_the_same_property_path() {
    for target in [
        "nested[\"inner\"].value",
        "nested[key].value",
        "(nested.inner).value",
    ] {
        let model = checked_model(
            &format!(
                r#"
type Key = 'inner';
declare const key: Key;
declare const nested: {{ inner: {{ value?: bigint }} }};
declare const expected: bigint | undefined;
if (nested.inner.value !== undefined) {{
    nested.inner.value++;
    {target} = undefined;
    const after = nested.inner.value;
    const rejected: bigint = after;
    nested.inner.value++;
}}
"#
            ),
            ScriptKind::TypeScript,
            &["BAMTS-C004", "BAMTS-C062"],
        );
        assert_eq!(
            binding_type(&model, "after"),
            binding_type(&model, "expected"),
        );
    }
}

#[test]
fn unsupported_updates_do_not_publish_successful_numeric_flow() {
    checked_model(
        r#"
declare function takesString(value: string): void;
declare let root: string | number;
declare const member: { value: string | number };
type Text = string;
declare let aliased: Text | number;
if (typeof root === 'string') {
    root++;
    takesString(root);
}
if (typeof member.value === 'string') {
    member.value++;
    takesString(member.value);
}
if (typeof aliased === 'string') {
    aliased++;
    takesString(aliased);
}
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C053"; 3],
    );
}

#[test]
fn imported_constant_keys_preserve_origin_and_initializer_evidence() {
    for (exporter, invalidates) in [
        ("declare const key: 'value'; export { key };", true),
        (
            "type Key = 'value'; declare const key: Key; export { key };",
            true,
        ),
        ("export const key: 'value' | 'other' = 'value';", true),
        (
            "declare const key: 'value' | 'other'; export { key };",
            false,
        ),
        ("declare let key: 'value'; export { key };", false),
    ] {
        let main = r#"
import { key } from './keys.js';
declare const guarded: { value?: bigint; other?: bigint; [name: string]: bigint | undefined };
declare const expected: bigint | undefined;
if (guarded.value !== undefined) {
    guarded.value++;
    guarded[key] = undefined;
    const after = guarded.value;
    const rejected: bigint = after;
}
"#;
        let model = checked_linked_model(
            &[
                (exporter, ScriptKind::TypeScript),
                (main, ScriptKind::TypeScript),
            ],
            &[(1, 0, 0)],
            1,
            if invalidates { &["BAMTS-C004"] } else { &[] },
        );
        let expected = if invalidates {
            binding_type(&model, "expected")
        } else {
            model.types().bigint()
        };
        assert_eq!(binding_type(&model, "after"), expected);
    }
}

#[test]
fn copies_of_imported_constants_keep_the_published_union_key_type() {
    let model = checked_linked_model(
        &[
            (
                "export const key: 'value' | 'other' = 'value';",
                ScriptKind::TypeScript,
            ),
            (
                "import { key as original } from './keys.js'; export const key = original;",
                ScriptKind::TypeScript,
            ),
            (
                r#"
import { key } from './copy.js';
declare const guarded: { value?: bigint; other?: bigint };
if (guarded.value !== undefined) {
    guarded.value++;
    guarded[key] = undefined;
    const after = guarded.value;
    const accepted: bigint = after;
}
"#,
                ScriptKind::TypeScript,
            ),
        ],
        &[(1, 0, 0), (2, 0, 1)],
        2,
        &[],
    );
    assert_eq!(binding_type(&model, "after"), model.types().bigint());
}

#[test]
fn branded_numeric_updates_preserve_guarded_roots_and_properties() {
    for (primitive, rejected) in [("number", "bigint"), ("bigint", "number")] {
        let model = checked_model(
            &format!(
                r#"
type Brand = {primitive} & {{ readonly brand: 'numeric' }};
declare let root: Brand | undefined;
declare const property: {{ value?: Brand }};
declare const expected: Brand;
if (root !== undefined) {{
    const rootPost = root++;
    const rootPrefix = --root;
    const rootAfter = root;
    const accepted: Brand = rootAfter;
    const wrong: {rejected} = rootAfter;
}}
if (property.value !== undefined) {{
    const propertyPost = property.value--;
    const propertyPrefix = ++property.value;
    const propertyAfter = property.value;
    const accepted: Brand = propertyAfter;
    const wrong: {rejected} = propertyAfter;
}}
"#
            ),
            ScriptKind::TypeScript,
            &["BAMTS-C004"; 2],
        );
        let primitive_type = if primitive == "number" {
            model.types().number()
        } else {
            model.types().bigint()
        };
        for name in ["rootPost", "rootPrefix", "propertyPost", "propertyPrefix"] {
            assert_eq!(binding_type(&model, name), primitive_type, "{name}");
        }
        for name in ["rootAfter", "propertyAfter"] {
            assert_eq!(
                binding_type(&model, name),
                binding_type(&model, "expected"),
                "{name}"
            );
        }
    }
}

#[test]
fn branded_numeric_updates_keep_literal_identity_and_nullable_rejection() {
    let model = checked_model(
        r#"
type Brand = number & { readonly brand: 'numeric' };
type LiteralBrand = 1 & { readonly brand: 'literal' };
declare let literal: LiteralBrand | undefined;
declare const expected: LiteralBrand;
declare const unsafe: { value?: Brand };
if (literal !== undefined) {
    const post = literal++;
    const after = literal;
    const accepted: 1 = after;
    const branded: LiteralBrand = after;
    const rejected: 1 = post;
}
unsafe.value++;
const rejectedAfter: Brand = unsafe.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004", "BAMTS-C062", "BAMTS-C004"],
    );
    assert_eq!(binding_type(&model, "post"), model.types().number());
    assert_eq!(
        binding_type(&model, "after"),
        binding_type(&model, "expected"),
    );
}

#[test]
fn nonnumeric_intersections_do_not_publish_successful_update_flow() {
    checked_model(
        r#"
type Text = string & { readonly brand: 'text' };
declare let value: Text | undefined;
declare function takesText(value: Text): void;
if (value !== undefined) {
    value++;
    takesText(value);
}
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C053"],
    );
}

#[test]
fn intersection_factors_preserve_only_shared_nullish_members() {
    let model = checked_model(
        r#"
type MaybeNumber = (number | undefined) & ({ readonly brand: 'number' } | undefined);
type MaybeBigInt = (bigint | undefined) & unknown;
type PresentBigInt = (bigint | undefined) & { readonly brand: 'present' };
declare let numeric: MaybeNumber;
declare let bigint: MaybeBigInt;
declare let present: PresentBigInt;
const numericPost = numeric++;
const unsafeNumber: number = numeric;
const bigintPost = bigint++;
const unsafeBigInt: bigint = bigint;
const presentPost = present++;
const accepted: bigint = presentPost;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C062", "BAMTS-C004", "BAMTS-C062", "BAMTS-C004"],
    );
    assert_eq!(binding_type(&model, "numericPost"), model.types().number());
    for name in ["bigintPost", "presentPost"] {
        assert_eq!(binding_type(&model, name), model.types().bigint(), "{name}");
    }
}
