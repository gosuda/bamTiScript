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
fn an_own_static_colliding_with_its_own_namespace_is_a_duplicate() {
    // The precedence rules must not silence a genuine collision on one class.
    assert!(
        !checker_codes("class C { static x: 1 = 1; }\nnamespace C { export const x = 2; }\n")
            .is_empty(),
        "a class static colliding with its own namespace export is a duplicate"
    );
}
