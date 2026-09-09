//! A namespace merged into a class contributes statics, and those statics
//! reach every descendant. When more than one ancestor contributes the same
//! name, the nearest one wins, and a descendant's own static or own namespace
//! append outranks any of them. These cases guard that precedence, which is
//! observable through the type a member access reads.

use std::sync::Arc;

use bamts_compiler::{
    checker::check,
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

/// Checker diagnostics for one TypeScript source, lint codes excluded.
fn checker_codes(source: &str) -> Vec<String> {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let checked = check(&parser::parse(scanned));
    checked
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str().to_owned())
        .filter(|code| code.starts_with("BAMTS-C"))
        .collect()
}

/// Asserts the source checks clean. A literal-typed annotation is the probe:
/// it fails only when the access reads a wider or different type.
fn assert_reads_clean(source: &str, what: &str) {
    let codes = checker_codes(source);
    assert!(codes.is_empty(), "{what}: {codes:?}");
}

#[test]
fn a_descendants_own_static_shadows_a_base_namespace_export() {
    assert_reads_clean(
        "class C {}\nnamespace C { export const x: number = 1; }\n\
         class D extends C { static x: 2 = 2; }\nconst n: 2 = D.x;\n",
        "an own static keeps its own type",
    );
}

#[test]
fn a_nearer_ancestor_outranks_a_farther_one() {
    // B overrides C's static, so a later export from C must not reach past B
    // into D.
    assert_reads_clean(
        "class C { static x: 1 = 1; }\nnamespace C { export const y = 1; }\n\
         class B extends C { static x: 2 = 2; }\nclass D extends B {}\n\
         namespace C { export const z = 1; }\nconst n: 2 = D.x;\n",
        "a nearer own static outranks a farther export",
    );
}

#[test]
fn a_nearer_namespace_export_outranks_a_farther_one() {
    // The nearer value arrives through a namespace, so it carries no
    // declaring class and the inheritance chain is its only provenance.
    assert_reads_clean(
        "class C {}\nclass B extends C {}\nnamespace B { export const x = 2; }\n\
         class D extends B {}\n\
         namespace C { export const x: number = 1; }\nconst n: 2 = D.x;\n",
        "a nearer namespace export outranks a farther one",
    );
}

#[test]
fn a_descendant_declared_late_keeps_its_nearer_origin() {
    // D is prepared in a nested statement list after B's augmentation has
    // finished, which is the case that has no propagation record at all.
    assert_reads_clean(
        "class C {}\nclass B extends C {}\nnamespace B { export const x = 2; }\n\
         namespace N { export class D extends B {} }\n\
         namespace C { export const x: number = 1; }\n\
         namespace N { export const n: 2 = D.x; }\n",
        "a late descendant keeps its nearer origin",
    );
}

#[test]
fn a_base_export_still_refreshes_an_inherited_snapshot() {
    // Precedence must not freeze the chain: an export from the same ancestor
    // that supplied the value still reaches the descendant.
    assert_reads_clean(
        "class C {}\nclass D extends C {}\n\
         namespace C { export const x: 1 = 1; }\nconst n: 1 = D.x;\n",
        "a base export reaches the descendant",
    );
}

#[test]
fn an_early_constructor_alias_sees_later_namespace_exports() {
    assert_reads_clean(
        "class C {}\nclass D extends C {}\nconst alias = D;\n\
         namespace C { export const x = 1; }\nconst n: 1 = alias.x;\n",
        "an alias shares the constructor's later namespace exports",
    );
}

#[test]
fn an_own_static_colliding_with_its_own_namespace_is_a_duplicate() {
    // The precedence rules must not silence a genuine collision on one class.
    assert!(
        !checker_codes("class C { static x: 1 = 1; }\nnamespace C { export const x = 2; }\n")
            .is_empty(),
        "a class static colliding with its own namespace export is a duplicate"
    );
}

#[test]
fn an_early_constructor_alias_sees_later_namespace_exports_by_index() {
    assert_reads_clean(
        "class C {}\nclass D extends C {}\nconst alias = D;\n\
         namespace C { export const x: 1 = 1; }\nconst n: 1 = alias[\"x\"];\n",
        "an alias shares the constructor's later namespace exports by index",
    );
}

#[test]
fn an_early_constructor_alias_assigns_to_required_structural_type() {
    assert_reads_clean(
        "class C {}\nclass D extends C {}\nconst alias = D;\n\
         namespace C { export const x: 1 = 1; }\nconst obj: { x: 1 } = alias;\n",
        "an alias is assignable to a structural type requiring a namespace export",
    );
}

#[test]
#[ignore = "type-state forward does not cover typeof-alias resolved before merge; tracks with representation fix"]
fn a_type_alias_captured_before_merge_sees_later_exports() {
    assert_reads_clean(
        "class C {}\nclass D extends C {}\ntype A = typeof D;\nconst force: A = D;\n\
         namespace C { export const x: 1 = 1; }\nconst probe: A = D;\nconst v: 1 = probe.x;\n",
        "a type alias resolved before the merge shares later namespace exports",
    );
}

// Pre-existing gap, not stale-alias specific: `keyof typeof D` fails even
// without an alias, so `keyof` on constructors needs its own fix.
#[test]
#[ignore = "keyof on constructors is unreduced even direct; tracks separately"]
fn an_early_constructor_alias_keyof_includes_later_namespace_exports() {
    assert_reads_clean(
        "class C {}\nclass D extends C {}\nconst alias = D;\n\
         namespace C { export const x: 1 = 1; }\ntype K = keyof typeof alias;\nconst k: K = \"x\";\n",
        "an alias's keyof includes the constructor's later namespace exports",
    );
}

// Pre-existing gap, not stale-alias specific: `new D<number>(1)` fails even
// without an alias, so generic construct through a namespace-augmented base
// needs its own fix.
#[test]
#[ignore = "generic construct with namespace augmentation fails direct; tracks separately"]
fn a_generic_constructor_alias_keeps_construct_signatures_and_additions() {
    assert_reads_clean(
        "class C<T> { constructor(public value: T) {} }\n\
         class D<U> extends C<U> {}\nconst alias = D;\n\
         namespace C { export const x: 1 = 1; }\n\
         const v: 1 = alias.x;\n\
         const n: number = new D<number>(1).value;\n",
        "a generic constructor alias keeps construct signatures and namespace exports",
    );
}

#[test]
fn an_explicitly_structural_alias_does_not_gain_namespace_exports() {
    assert!(
        !checker_codes(
            "class C {}\nclass D extends C {}\nconst alias: { prototype: C } = D;\n\
             namespace C { export const x: 1 = 1; }\nconst n: 1 = alias.x;\n"
        )
        .is_empty(),
        "a structural alias must not gain namespace exports"
    );
}
