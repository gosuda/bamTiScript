//! Constructor key domains retain declaration visibility and name spelling.

use std::sync::Arc;

use bamts_compiler::{
    checker::{SemanticModel, TypeId, check},
    diagnostic::{Diagnostic, DiagnosticSeverity},
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn analyze_source(source: &str) -> (SemanticModel, Vec<Diagnostic>) {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let parsed = parser::parse(scanned);
    let (model, mut diagnostics) = check(&parsed).into_parts();
    diagnostics.extend_from_slice(parsed.diagnostics());
    (model, diagnostics)
}

fn checker_codes(source: &str) -> Vec<String> {
    analyze_source(source)
        .1
        .iter()
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str().to_owned())
        .collect()
}

fn checked_model(source: &str) -> SemanticModel {
    let (model, diagnostics) = analyze_source(source);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity() != DiagnosticSeverity::Error),
        "{diagnostics:?}\n{source}"
    );
    model
}

fn value_type(model: &SemanticModel, name: &str) -> TypeId {
    let symbol = model
        .scopes()
        .iter()
        .find_map(|scope| scope.value(name))
        .unwrap_or_else(|| panic!("value {name} is bound"));
    model.symbol_type(symbol)
}

fn assert_value_type(model: &SemanticModel, name: &str, expected: TypeId) {
    let mut actual = value_type(model, name);
    let mut visited = std::collections::HashSet::new();
    while let Some(view) = model.types().applied_alias_view(actual) {
        assert!(visited.insert(actual), "cyclic alias for {name}");
        actual = view;
    }
    assert_eq!(
        actual,
        expected,
        "{name}: {:?}, expected {:?}",
        model.types().get(actual),
        model.types().get(expected),
    );
}

fn assert_checks(source: &str) {
    let codes = checker_codes(source);
    assert!(codes.is_empty(), "{codes:?}\n{source}");
}

fn assert_assignment_errors(source: &str, expected: usize) {
    let codes = checker_codes(source);
    assert_eq!(
        codes,
        vec!["BAMTS-C004"; expected],
        "only the deliberate key assignments should fail:\n{source}"
    );
}

#[test]
fn constructor_keys_include_public_statics_and_exclude_non_public_statics() {
    assert_checks(
        r#"
class C {
    static visible = 1;
    private static hidden = 2;
    protected static guarded = 3;
}
class D extends C { static own = 4; }
type K = keyof typeof D;
const visible: K = "visible";
const own: K = "own";
const prototype: K = "prototype";
"#,
    );
    assert_assignment_errors(
        r#"
class C {
    static visible = 1;
    private static hidden = 2;
    protected static guarded = 3;
}
class D extends C {}
const hidden: keyof typeof C = "hidden";
const guarded: keyof typeof C = "guarded";
const inherited: keyof typeof D = "guarded";
"#,
        3,
    );
}

#[test]
fn enum_keys_exclude_reverse_indexes_without_disabling_reverse_reads() {
    assert_checks(
        r#"
enum E { First, Second }
type K = keyof typeof E;
const first: K = "First";
const second: K = "Second";
const reverse: string = E[0];
"#,
    );
    assert_assignment_errors(
        r#"
enum E { First, Second }
const numeric: keyof typeof E = 123;
const reverse: keyof typeof E = "0";
const missing: keyof typeof E = "Missing";
"#,
        3,
    );
}

#[test]
fn heterogeneous_enum_keys_also_exclude_reverse_indexes() {
    assert_checks(
        r#"
enum E { Numeric = 1, Text = "text" }
const numeric: keyof typeof E = "Numeric";
const text: keyof typeof E = "Text";
const reverse: string = E[1];
"#,
    );
    assert_assignment_errors(
        r#"
enum E { Numeric = 1, Text = "text" }
const arbitrary: keyof typeof E = 42;
"#,
        1,
    );
}

#[test]
fn declared_numeric_indexes_still_contribute_number_keys() {
    assert_checks(
        r#"
interface Numbers { [index: number]: string; }
const key: keyof Numbers = 123;
"#,
    );
}

#[test]
fn constructor_keys_distinguish_quoted_and_numeric_declarations() {
    assert_checks(
        r#"
class C {
    static "01" = 1;
    static "1" = 1;
    static 2 = 1;
    static 2.5 = 1;
    static [3] = 1;
    static ["04"] = 1;
    static 5() { return 1; }
    static get 6() { return 1; }
}
class D extends C {}
type K = keyof typeof D;
const leadingZero: K = "01";
const quoted: K = "1";
const numeric: K = 2;
const fractional: K = 2.5;
const computedNumeric: K = 3;
const computedString: K = "04";
const method: K = 5;
const accessor: K = 6;
"#,
    );
    assert_assignment_errors(
        r#"
class C { static "01" = 1; static "1" = 1; static 2 = 1; }
const quotedAsNumber: keyof typeof C = 1;
const numericAsString: keyof typeof C = "2";
"#,
        2,
    );
}

#[test]
fn numeric_key_origin_survives_generic_instantiation() {
    assert_checks(
        r#"
interface Members<T> { "01": T; "1": T; 2: T; 3(): T; }
type K = keyof Members<number>;
const leadingZero: K = "01";
const quoted: K = "1";
const numeric: K = 2;
const method: K = 3;
"#,
    );
    assert_assignment_errors(
        r#"
interface Members<T> { "1": T; 2: T; }
const quotedAsNumber: keyof Members<number> = 1;
const numericAsString: keyof Members<number> = "2";
"#,
        2,
    );
}

#[test]
fn numeric_key_origin_survives_object_spread() {
    assert_checks(
        r#"
const source = { "01": 1, "1": 1, 2: 1, 3() { return 1; } };
const copy = { ...source };
const leadingZero: keyof typeof copy = "01";
const quoted: keyof typeof copy = "1";
const numeric: keyof typeof copy = 2;
const method: keyof typeof copy = 3;
"#,
    );
    assert_assignment_errors(
        r#"
const source = { "1": 1, 2: 1 };
const copy = { ...source };
const quotedAsNumber: keyof typeof copy = 1;
const numericAsString: keyof typeof copy = "2";
"#,
        2,
    );
}

#[test]
fn record_keys_keep_their_literal_kind() {
    assert_checks(
        r#"
type R = Record<"01" | "1" | 2, number>;
const leadingZero: keyof R = "01";
const quoted: keyof R = "1";
const numeric: keyof R = 2;
"#,
    );
}

#[test]
fn captured_constructor_keys_follow_successive_namespace_merges() {
    assert_checks(
        r#"
class C {}
class D extends C {}
type K = keyof typeof D;
const initial: K = "prototype";
namespace C { export const extra = 1; }
const first: K = "extra";
namespace C { export const second = 2; }
const second: K = "second";
const stillFirst: K = "extra";
"#,
    );
}

#[test]
fn a_key_query_before_the_class_body_tracks_constructor_finalization() {
    assert_checks(
        r#"
type K = keyof typeof C;
class C { static own = 1; }
namespace C { export const extra = 2; }
const own: K = "own";
const extra: K = "extra";
"#,
    );
}

#[test]
fn constructor_key_projections_survive_unions_and_intersections() {
    assert_checks(
        r#"
class C {}
class D extends C {}
type Union = keyof typeof D | "separate";
type Intersection = (keyof typeof D) & ("prototype" | "extra");
const initialUnion: Union = "prototype";
const initialIntersection: Intersection = "prototype";
namespace C { export const extra = 1; }
const laterUnion: Union = "extra";
const separate: Union = "separate";
const laterIntersection: Intersection = "extra";
"#,
    );
}

#[test]
fn constructor_key_projections_survive_generic_alias_materialization() {
    assert_checks(
        r#"
class C {}
class D extends C {}
type K = keyof typeof D;
type Box<T> = { key: T };
const before: Box<K> = { key: "prototype" };
namespace C { export const extra = 1; }
const after: Box<K> = { key: "extra" };
const read: K = after.key;
"#,
    );
}

#[test]
fn keyof_a_constructor_union_refreshes_both_dependencies() {
    assert_checks(
        r#"
class C {}
class D extends C {}
type K = keyof (typeof C | typeof D);
const initial: K = "prototype";
namespace C { export const extra = 1; }
const later: K = "extra";
"#,
    );
}

#[test]
fn record_key_domains_keep_live_constructor_projections() {
    assert_checks(
        r#"
class C {}
type Fields = Record<keyof typeof C, number>;
declare const captured: Fields;
namespace C { export const extra = 1; }
const value: number = captured.extra;
type K = keyof Fields;
const extra: K = "extra";
"#,
    );
}

#[test]
fn updating_constructor_keys_does_not_redirect_shared_literal_types() {
    assert_assignment_errors(
        r#"
class C {}
class Other {}
type Changed = keyof typeof C;
type Untouched = keyof typeof Other;
type Literal = "prototype";
namespace C { export const extra = 1; }
const changed: Changed = "extra";
const unrelated: Untouched = "extra";
const literal: Literal = "extra";
"#,
        2,
    );
}

#[test]
fn record_keys_preserve_numeric_and_string_kinds_for_the_same_name() {
    for domain in [r#""1" | 1"#, r#"1 | "1""#] {
        assert_checks(&format!(
            r#"
type R = Record<{domain}, boolean>;
type Identity<T> = T;
type K = keyof Identity<R>;
const stringKey: K = "1";
const numberKey: K = 1;
declare const source: R;
const copy = {{ ...source }};
const copiedString: keyof typeof copy = "1";
const copiedNumber: keyof typeof copy = 1;
"#
        ));
        assert_assignment_errors(
            &format!(
                r#"
type R = Record<{domain}, boolean>;
const otherString: keyof R = "2";
const otherNumber: keyof R = 2;
"#
            ),
            2,
        );
    }
}

#[test]
fn distinct_quoted_record_keys_do_not_gain_numeric_spellings() {
    assert_checks(
        r#"
type R = Record<"01" | 1, boolean>;
const quoted: keyof R = "01";
const numeric: keyof R = 1;
"#,
    );
    assert_assignment_errors(
        r#"
type R = Record<"01" | 1, boolean>;
const absentString: keyof R = "1";
const absentNumber: keyof R = 0;
"#,
        2,
    );
}

#[test]
fn inherited_numeric_keys_keep_the_overriding_declarations_kind() {
    assert_checks(
        r#"
class Quoted { static "1" = true; }
class Numeric extends Quoted { static 1 = true; }
class NumberBase { static 1 = true; }
class StringDerived extends NumberBase { static "1" = true; }
const quoted: keyof typeof Quoted = "1";
const numeric: keyof typeof Numeric = 1;
const derivedString: keyof typeof StringDerived = "1";
"#,
    );
    assert_assignment_errors(
        r#"
class Quoted { static "1" = true; }
class Numeric extends Quoted { static 1 = true; }
class NumberBase { static 1 = true; }
class StringDerived extends NumberBase { static "1" = true; }
const wrongString: keyof typeof Numeric = "1";
const wrongNumber: keyof typeof StringDerived = 1;
"#,
        2,
    );
}

#[test]
fn object_spread_uses_the_last_propertys_key_kind() {
    assert_checks(
        r#"
const numeric = { 1: true };
const quoted = { "1": true };
const stringLast = { ...numeric, ...quoted };
const numberLast = { ...quoted, ...numeric };
const stringKey: keyof typeof stringLast = "1";
const numberKey: keyof typeof numberLast = 1;
"#,
    );
    assert_assignment_errors(
        r#"
const numeric = { 1: true };
const quoted = { "1": true };
const stringLast = { ...numeric, ...quoted };
const numberLast = { ...quoted, ...numeric };
const wrongNumber: keyof typeof stringLast = 1;
const wrongString: keyof typeof numberLast = "1";
"#,
        2,
    );
}

#[test]
fn a_named_numeric_enum_member_remains_a_key_beside_its_reverse_lookup() {
    assert_checks(
        r#"
enum E { One = 1 }
const named: keyof typeof E = "One";
const reverse: string = E[1];
"#,
    );
    assert_assignment_errors(
        r#"
enum E { One = 1 }
const reverseNumber: keyof typeof E = 1;
const reverseString: keyof typeof E = "1";
"#,
        2,
    );
}

#[test]
fn numeric_constructor_keys_accept_equivalent_literal_spellings() {
    assert_checks(
        r#"
class C { static 2.5 = true; static 16 = true; static 1000 = true; }
type K = keyof typeof C;
const fractional: K = 2.50;
const exponent: K = 25e-1;
const hexadecimal: K = 0x10;
const decimal: K = 16;
const separated: K = 1_000;
const plain: K = 1000;
"#,
    );
}

#[test]
fn numeric_literal_aliases_compare_values_in_both_directions() {
    assert_checks(
        r#"
type Short = 2.5;
type Long = 2.50;
const short: Short = 2.50;
const long: Long = 2.5;
"#,
    );
}

#[test]
fn numeric_key_value_comparison_rejects_other_values_and_string_keys() {
    assert_assignment_errors(
        r#"
class Numeric { static 2.5 = true; }
class Quoted { static "2.5" = true; }
const different: keyof typeof Numeric = 2.51;
const wrongString: keyof typeof Numeric = "2.5";
const wrongNumber: keyof typeof Quoted = 2.50;
"#,
        3,
    );
}

#[test]
fn growing_generic_aliases_do_not_recurse_through_unbounded_keyof_views() {
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
        let codes = checker_codes(source);
        assert!(codes.iter().any(|code| code == "BAMTS-C072"), "{codes:?}");
    }
}

#[test]
fn alias_recursion_guards_allow_object_recursion_and_repeated_siblings() {
    assert_checks(
        r#"
type Tree<T> = { next: Tree<T[]> };
type Box<T> = { value: T };
const recursive: keyof Tree<string> = "next";
const siblings: keyof (Box<string> | Box<number>) = "value";
"#,
    );
}

#[test]
fn unresolved_record_keyof_keeps_the_original_generic_key_domain() {
    assert_checks(
        r#"
function f<T>(r: Record<keyof T, number>, k: keyof T) {
    const j: keyof typeof r = k;
    const original: keyof T = j;
}
"#,
    );
    assert_assignment_errors(
        r#"
function f<T>(r: Record<keyof T, number>) {
    const missing: keyof typeof r = "missing";
}
"#,
        1,
    );
}

#[test]
fn live_records_relate_to_structural_objects_before_and_after_namespace_merges() {
    assert_checks(
        r#"
class C {}
declare const fields: Record<keyof typeof C, number>;
const before: { prototype: number } = fields;
namespace C { export const extra = 1; }
const after: { prototype: number; extra: number } = fields;
interface Fields { prototype: number; extra: number; }
const named: Fields = fields;
const intersection: { prototype: number } & { extra: number } = fields;
const fromObject: typeof fields = { prototype: 1, extra: 2 };
"#,
    );
}

#[test]
fn live_record_relations_reject_missing_optional_and_incompatible_members() {
    assert_assignment_errors(
        r#"
class C {}
declare const fields: Record<keyof typeof C, number>;
namespace C { export const extra = 1; }
const missing: typeof fields = { prototype: 1 };
declare const optional: { prototype: number; extra?: number };
const required: typeof fields = optional;
const wrongValue: { extra: string } = fields;
const absent: { missing: number } = fields;
"#,
        4,
    );
}

#[test]
fn numeric_record_names_and_index_types_use_number_values() {
    assert_checks(
        r#"
type R = Record<2.50 | 0x10, boolean>;
declare const record: R;
const decimal: boolean = record[2.5];
const hexadecimal: boolean = record[16];
const originalSpelling: boolean = record[2.50];
type Indexed = R[0x10];
const indexed: Indexed = true;
type Quoted = Record<"2.50" | "0x10", boolean>;
declare const quoted: Quoted;
const quotedDecimal: boolean = quoted["2.50"];
const quotedHexadecimal: boolean = quoted["0x10"];
"#,
    );
    assert_assignment_errors(
        r#"
type R = Record<2.50 | 0x10, boolean>;
const quotedDecimal: keyof R = "2.50";
const quotedHexadecimal: keyof R = "0x10";
type Quoted = Record<"2.50" | "0x10", boolean>;
const decimal: keyof Quoted = 2.5;
const hexadecimal: keyof Quoted = 16;
"#,
        4,
    );
    let codes = checker_codes(
        r#"
type WrongSpelling = Record<2.50, boolean>["2.50"];
"#,
    );
    assert_eq!(codes, ["BAMTS-C064"], "quoted keys keep their spelling");
}

#[test]
fn record_key_intersections_preserve_each_literal_kind() {
    assert_checks(
        r#"
type Strings = Record<(1 | "1") & string, boolean>;
type Numbers = Record<(1 | "1") & number, boolean>;
type Both = Record<(1 | "1") & (string | number), boolean>;
const stringKey: keyof Strings = "1";
const numberKey: keyof Numbers = 1;
const bothString: keyof Both = "1";
const bothNumber: keyof Both = 1;
"#,
    );
    assert_assignment_errors(
        r#"
type Strings = Record<(1 | "1") & string, boolean>;
type Numbers = Record<(1 | "1") & number, boolean>;
type Empty = Record<1 & "1", boolean>;
const numericInString: keyof Strings = 1;
const stringInNumber: keyof Numbers = "1";
const empty: keyof Empty = 1;
"#,
        3,
    );
}

#[test]
fn destructuring_live_records_infers_exact_current_property_types() {
    let model = checked_model(
        r#"
class C {}
declare const fields: Record<keyof typeof C, number>;
const { prototype } = fields;
namespace C { export const extra = 1; }
const { extra } = fields;
"#,
    );
    for name in ["prototype", "extra"] {
        assert_value_type(&model, name, model.types().number());
    }
    assert_eq!(
        checker_codes(
            "class C {} declare const fields: Record<keyof typeof C, number>; const { absent } = fields;"
        ),
        ["BAMTS-C057"],
    );
}

#[test]
fn partial_live_records_keep_optional_members_through_instantiation_and_updates() {
    let model = checked_model(
        r#"
class C {}
type Fields<T> = Partial<Record<keyof typeof C, T>>;
const before: Fields<number> = {};
declare const fields: Fields<number>;
declare const expected: number | undefined;
const { prototype } = fields;
namespace C { export const extra = 1; }
const after: Fields<number> = {};
const { extra } = fields;
type Indexed = Fields<number>["extra"];
declare const indexed: Indexed;
type BroadFields<T> = Partial<Record<keyof typeof C | number, T>>;
type Broad = BroadFields<number>[number];
declare const broad: Broad;
"#,
    );
    let expected = value_type(&model, "expected");
    for name in ["prototype", "extra", "indexed", "broad"] {
        assert_value_type(&model, name, expected);
    }
    assert_assignment_errors(
        r#"
class C {}
declare const partial: Partial<Record<keyof typeof C, number>>;
const required: Record<keyof typeof C, number> = partial;
const wrongValue: Partial<Record<keyof typeof C, number>> = { prototype: "wrong" };
"#,
        2,
    );
}

#[test]
fn optional_record_relations_allow_missing_keys_without_losing_value_checks() {
    assert_checks(
        r#"
class Narrow {}
class Wide { static extra = 1; }
declare const source: Record<keyof typeof Narrow, number>;
const target: Partial<Record<keyof typeof Wide, number>> = source;
"#,
    );
    assert_assignment_errors(
        r#"
class Narrow {}
class Wide { static extra = 1; }
declare const source: Record<keyof typeof Narrow, string>;
const target: Partial<Record<keyof typeof Wide, number>> = source;
"#,
        1,
    );
}

#[test]
fn concrete_record_relations_keep_the_generic_key_subset_rule() {
    assert_checks(
        r#"
class C {}
declare const all: Record<keyof typeof C, number>;
function select<K extends keyof typeof C>(key: K) {
    const selected: Record<K, number> = all;
}
"#,
    );
    assert_assignment_errors(
        r#"
class C {}
declare const all: Record<keyof typeof C, string>;
function select<K extends keyof typeof C>(key: K) {
    const selected: Record<K, number> = all;
}
"#,
        1,
    );
}

#[test]
fn indexed_access_constraints_read_live_record_properties_and_index_domains() {
    assert_checks(
        r#"
class C { static x = 1; static 2.5 = 1; }
type R = Record<keyof typeof C, number>;
function named<T extends R>(value: T["x"]): number { return value; }
function numeric<T extends R>(value: T[2.50]): number { return value; }
type Indexed = Record<keyof typeof C | number, number>;
function broad<T extends Indexed>(value: T[number]): number { return value; }
type Optional = Partial<R>;
function optional<T extends Optional>(value: T["x"]): number | undefined { return value; }
"#,
    );
    assert_assignment_errors(
        r#"
class C { static x = 1; }
type R = Record<keyof typeof C, number>;
function wrong<T extends R>(value: T["x"]) {
    const result: string = value;
}
type Indexed = Record<keyof typeof C | number, number>;
function wrongIndex<T extends Indexed>(value: T[number]) {
    const result: string = value;
}
"#,
        2,
    );
}

#[test]
fn live_numeric_record_indexes_accept_cooked_names_and_keep_exact_value_types() {
    let model = checked_model(
        r#"
class C { static 1 = true; }
type R = Record<keyof typeof C, boolean>;
declare const record: R;
type Numeric = R[1];
type StringForm = R["1"];
declare const numeric: Numeric;
declare const stringForm: StringForm;
const expression = record["1"];
"#,
    );
    for name in ["numeric", "stringForm", "expression"] {
        assert_value_type(&model, name, model.types().boolean());
    }
    assert_eq!(
        checker_codes(
            "class C { static 1 = true; } type Wrong = Record<keyof typeof C, boolean>[\"01\"];"
        ),
        ["BAMTS-C064"],
    );
}

#[test]
fn disjoint_symbol_indexes_do_not_block_numeric_live_record_assignments() {
    assert_checks(
        r#"
class C {}
declare const source: { prototype: boolean; [key: symbol]: boolean };
const target: Record<keyof typeof C | number, boolean> = source;
"#,
    );
    assert_assignment_errors(
        r#"
class C {}
declare const overlapping: { prototype: boolean; [key: number]: string };
const target: Record<keyof typeof C | number, boolean> = overlapping;
declare const missing: { [key: symbol]: boolean };
const required: Record<keyof typeof C | number, boolean> = missing;
"#,
        2,
    );
}

#[test]
fn live_records_participate_in_structural_inference_without_erasing_naked_identity() {
    let model = checked_model(
        r#"
class C { static x = 1; }
declare function fromObject<T>(value: { x: T }): T;
declare function fromRecord<T>(value: Record<keyof typeof C, T>): T;
declare function identity<T>(value: T): T;
declare const fields: Record<keyof typeof C, number>;
declare const object: { x: number; prototype: number };
const first = fromObject(fields);
const second = fromRecord(object);
const preserved = identity(fields);
namespace C { export const extra = 1; }
const { extra } = preserved;
"#,
    );
    for name in ["first", "second", "extra"] {
        assert_value_type(&model, name, model.types().number());
    }
    assert_eq!(
        value_type(&model, "preserved"),
        value_type(&model, "fields")
    );
}

#[test]
fn live_record_intersections_aggregate_members_and_keep_excess_property_checks() {
    assert_checks(
        r#"
class C { static x = 1; }
declare const parts: { x: number } & { prototype: number };
const combined: Record<keyof typeof C, number> = parts;
declare const fields: Record<keyof typeof C, number> & { extra: string };
const shape: { x: number; prototype: number; extra: string } = fields;
"#,
    );
    assert_eq!(
        checker_codes(
            "class C {} const fields: Record<keyof typeof C, number> = { prototype: 1, extra: 2 };"
        ),
        ["BAMTS-C067"],
    );
}

#[test]
fn live_record_spread_and_interface_heritage_use_current_object_members() {
    let model = checked_model(
        r#"
class C { static x = 1; }
interface Fields extends Record<keyof typeof C, number> {}
declare const inherited: Fields;
const inheritedValue = inherited.x;
declare const fields: Record<keyof typeof C, number>;
const copied = { ...fields };
const copyValue = copied.x;
namespace C { export const extra = 1; }
const later = { ...fields };
const laterValue = later.extra;
"#,
    );
    for name in ["inheritedValue", "copyValue", "laterValue"] {
        assert_value_type(&model, name, model.types().number());
    }
}
