//! A numeric enum carries a reverse-mapping index signature at runtime and a
//! string enum does not, so `E[0]` is valid for one and not the other. The
//! binder must settle that classification before member accesses are typed:
//! the enum plan reconciles later, and a late correction cannot retract an
//! accepted access. These cases guard the classification, not its plumbing.

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

fn rejects_numeric_lookup(source: &str) -> bool {
    !checker_codes(source).is_empty()
}

#[test]
fn string_members_reject_a_numeric_lookup() {
    for source in [
        // A bare literal, and the wrappers that leave it a string.
        "enum E { A = \"a\" }\nconst v = E[0];\n",
        "enum E { A = `a` }\nconst v = E[0];\n",
        "enum E { A = (\"a\") }\nconst v = E[0];\n",
        "enum E { A = \"a\" as string }\nconst v = E[0];\n",
        // A reference to an earlier member, bare and qualified.
        "enum E { A = \"a\", B = A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = E.A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = E[\"A\"] }\nconst v = E[0];\n",
        // A member of another enum, which resolves by symbol, whether it
        // is named directly or through a namespace.
        "enum F { A = \"a\" }\nenum E { B = F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = \"a\" } }\nenum E { B = N.F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = \"a\" } }\nenum E { B = N[\"F\"].A }\nconst v = E[0];\n",
        "enum E { A = \"a\" }\nenum E { B = A }\nconst v = E[0];\n",
        // Concatenation is a string when either side is.
        "enum E { A = \"a\", B = A + A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = A + 1 }\nconst v = E[0];\n",
    ] {
        assert!(
            rejects_numeric_lookup(source),
            "a string enum has no reverse mapping: {source}"
        );
    }
}

#[test]
fn numeric_members_keep_their_reverse_mapping() {
    for source in [
        // Auto-numbered, literal, and computed members are all numeric.
        "enum E { A }\nconst v = E[0];\n",
        "enum E { A = 1 }\nconst v = E[0];\n",
        "enum E { A = Math.random() }\nconst v = E[0];\n",
        "enum E { A = 1 << 2 }\nconst v = E[0];\n",
        // A reference resolving to a numeric member stays numeric, whether
        // it names this enum or another one.
        "enum E { A = 1, B = A + A }\nconst v = E[0];\n",
        "enum F { A = 1 }\nenum E { B = F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = 1 } }\nenum E { B = N.F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = 1 } }\nenum E { B = N[\"F\"].A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = 1 }\nconst v = E[0];\n",
    ] {
        assert!(
            checker_codes(source).is_empty(),
            "a numeric enum keeps its reverse mapping: {source}"
        );
    }
}

#[test]
fn an_unresolvable_reference_stays_numeric() {
    // The classification has to be right before the plan runs, so a
    // reference the binder cannot settle keeps the index signature rather
    // than reporting a member that may well exist.
    assert!(
        checker_codes("enum E { A = Unknown.member }\nconst v = E[0];\n")
            .iter()
            .all(|code| code != "BAMTS-C057"),
        "an unsettled reference must not claim the enum is string-valued"
    );
}
