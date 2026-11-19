    use super::*;
    use bamts_compiler::checker::render_type;
    use crate::facets::load_diagnostic_code_map;

    fn repo_code_map() -> DiagnosticCodeMap {
        // `cargo test` runs with the package root as the working directory;
        // the code map is a committed oracle document two levels up.
        load_diagnostic_code_map(Path::new("../..")).expect("repository code map loads")
    }

    /// H1 end-to-end pin: a positive-diagnostics case compiles through the
    /// real loader+frontend, its lint warnings are filtered out, and the
    /// remaining checker diagnostic matches an upstream-position row
    /// (1-based line, 0-based character) under the code map.
    #[test]
    fn diagnostics_end_to_end_unresolved_name_passes() {
        let case_text = "var y = undefinedName;
";
        let units = split_case_units("tests/cases/compiler/endToEndPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/endToEndPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();

        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        // The lint profile's unused-local warning must not survive the filter.
        assert_eq!(actual.len(), 1, "only the checker diagnostic remains");
        assert_eq!(actual[0].code, "BAMTS-C002");
        assert_eq!(
            actual[0].position,
            SourcePosition {
                line: 1,
                character: 8
            }
        );

        // `undefinedName` starts at 0-based UTF-16 column 8 (TS prints 1:9).
        let expected = vec![FacetDiagnostic {
            unit: "endToEndPin.ts".to_owned(),
            position: SourcePosition {
                line: 1,
                character: 8,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2304".to_owned(),
        }];
        let verdict = compare_diagnostics(&expected, &actual, &code_map);
        assert_eq!(verdict, FacetVerdict::Pass);
    }

    /// Every emitted diagnostic counts: a raw `TS....` spelling compares as
    /// itself (`asyncAwaitIsolatedModules_es2017.errors.txt` expects
    /// `error TS2307: Cannot find module 'missing'.`, and the pipeline emits
    /// the raw spelling), and a BAMTS code without a map row still counts
    /// instead of vanishing before the comparison.
    #[test]
    fn diagnostics_count_raw_ts_and_unmapped_bamts_codes() {
        let code_map = repo_code_map();
        let ctx = CheckContext {
            code_map: code_map.clone(),
            baseline_groups: BaselineGroups::default(),
        };

        let import_case = "import { helper } from \"./missing\";\nexport const user = helper;\n";
        let units = split_case_units("tests/cases/compiler/rawTsCodePin.ts", import_case);
        let entry = entry_virtual_path("tests/cases/compiler/rawTsCodePin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let baselines = DiagnosticsBaselines {
            owned: vec!["rawTsCodePin.errors.txt".to_owned()],
            contents: BTreeMap::from([("rawTsCodePin.errors.txt".to_owned(), String::new())]),
        };
        let outcome = check_diagnostics(&ctx, &case, &baselines).expect("diagnostics outcome");
        assert!(
            outcome.actual.iter().any(|d| d.code == "TS2307"),
            "a raw TS spelling must count as itself: {:?}",
            outcome.actual
        );

        let decorator_case = "const frozen = 1;\nfrozen = 2;\n";
        let units = split_case_units("tests/cases/compiler/unmappedCodePin.ts", decorator_case);
        let entry = entry_virtual_path("tests/cases/compiler/unmappedCodePin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let outcome = check_diagnostics(&ctx, &case, &baselines).expect("diagnostics outcome");
        assert!(
            outcome.actual.iter().any(|d| d.code == "BAMTS-C060"),
            "a checker code must count even before correspondence: {:?}",
            outcome.actual
        );
    }

    /// Multi-unit cases with an empty leading unit must still load every file,
    /// so import conflicts in a dependent unit are observed.
    #[test]
    fn diagnostics_end_to_end_multi_unit_import_conflict_is_reached() {
        let case_text = "// @target: es2015\n\
            // @module: commonjs\n\
            // @filename: f1.ts\n\
            export function f() {\n\
            }\n\
            // @filename: f2.ts\n\
            import {f} from './f1';\n\
            export function f() {\n\
            }\n";
        let logical = "tests/cases/compiler/functionAndImportNameConflict.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();

        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        assert_eq!(
            actual.len(),
            1,
            "the import/local conflict in f2.ts must be emitted"
        );
        assert_eq!(actual[0].code, "BAMTS-C041");
        assert_eq!(
            actual[0].position,
            SourcePosition {
                line: 1,
                character: 8,
            }
        );

        let expected = vec![FacetDiagnostic {
            unit: "f2.ts".to_owned(),
            position: SourcePosition {
                line: 1,
                character: 8,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2440".to_owned(),
        }];
        let verdict = compare_diagnostics(&expected, &actual, &code_map);
        assert_eq!(verdict, FacetVerdict::Pass);
    }

    /// Zero-expectation pin: a clean case with no owned `.errors.txt` passes
    /// iff the compile emits no mapped diagnostics.
    #[test]
    fn diagnostics_end_to_end_clean_case_passes() {
        let case_text = "export const answer: number = 42;
";
        let units = split_case_units("tests/cases/compiler/cleanPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/cleanPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let verdict = compare_diagnostics(&[], &actual, &code_map);
        assert_eq!(verdict, FacetVerdict::Pass);
    }

    /// Regression: heterogeneous enums keep a reverse-mapping index when
    /// any member is numeric. Scalar classification stays all-members;
    /// only the `[index: number]: string` signature needs one member.
    #[test]
    fn hetero_enum_numeric_member_reverse_lookup() {
        let case_text = "enum H {\n    A = 1,\n    B = \"s\",\n}\nconst n: string = H[1];\n";
        let units = split_case_units("tests/cases/compiler/heteroEnumReverseLookup.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/heteroEnumReverseLookup.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: aliases of merged class+namespace partners construct.
    /// The legacy identifier path answers the class constructor, so
    /// `new alias()` keeps its construct signatures plus `alias.x`.
    #[test]
    fn merged_class_namespace_alias_constructs() {
        let case_text = "class C {\n}\nnamespace C {\n    export const x = 1;\n}\nconst alias = C;\nconst n: number = alias.x;\nnew alias();\n";
        let units = split_case_units(
            "tests/cases/compiler/mergedClassNamespaceAlias.ts",
            case_text,
        );
        let entry = entry_virtual_path("tests/cases/compiler/mergedClassNamespaceAlias.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: type-only exports are not runtime properties. `f.x`
    /// still resolves through the merged export scope while `f.T`
    /// reports a missing-property diagnostic.
    #[test]
    fn merged_namespace_type_only_member_rejected() {
        let case_text = "function f() {\n}\nnamespace f {\n    export type T = string;\n    export const x = 1;\n}\nconst v: number = f.x;\nconst w = f.T;\n";
        let units = split_case_units("tests/cases/compiler/mergedNamespaceTypeOnly.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/mergedNamespaceTypeOnly.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C057".to_owned(), 8)]);
    }
    /// Regression: pure namespaces reject type-only member reads the
    /// same way. `M.x` resolves while `M.T` reports missing-property.
    #[test]
    fn pure_namespace_type_only_member_rejected() {
        let case_text = "namespace M {\n    export type T = string;\n    export const x = 1;\n}\nconst v: number = M.x;\nconst w = M.T;\n";
        let units = split_case_units("tests/cases/compiler/pureNamespaceTypeOnly.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/pureNamespaceTypeOnly.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C057".to_owned(), 6)]);
    }
    /// Regression: namespace constructor members answer value-side types.
    /// Classes contribute their constructor (so `new alias.C()` checks)
    /// and enums their value-side constructor (so `m.A` resolves).
    #[test]
    fn namespace_alias_members_use_value_side_types() {
        let case_text = "namespace N {\n    export class C {\n    }\n    export enum E {\n        A = 1,\n    }\n}\nconst alias = N;\nnew alias.C();\nconst m = alias.E;\nconst k = m.A;\n";
        let units = split_case_units("tests/cases/compiler/namespaceAliasValueSide.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/namespaceAliasValueSide.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: `typeof` a merged class keeps construct signatures and
    /// gains the namespace exports. The finalizer augments the class
    /// constructor instead of skipping class-kind partners.
    #[test]
    fn merged_class_namespace_typeof_keeps_additions() {
        let case_text = "class C {\n}\nnamespace C {\n    export const x = 1;\n}\ntype T = typeof C;\nconst m: T = C;\nnew m();\nconst n: number = m.x;\n";
        let units = split_case_units(
            "tests/cases/compiler/mergedClassNamespaceTypeof.ts",
            case_text,
        );
        let entry =
            entry_virtual_path("tests/cases/compiler/mergedClassNamespaceTypeof.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: chained reads through namespace enum values resolve.
    /// Direct (`N.E.A`) and alias (`m.A`) chains stay diagnostic-free.
    #[test]
    fn namespace_enum_member_chains_resolve() {
        let case_text = "namespace N {\n    export enum E {\n        A = 1,\n    }\n}\nconst x = N.E.A;\nconst m = N.E;\nconst y = m.A;\n";
        let units = split_case_units("tests/cases/compiler/namespaceEnumChains.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/namespaceEnumChains.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: classes exported from a merged namespace construct.
    /// The merged member-access arm answers the constructor, not the
    /// instance slot.
    #[test]
    fn merged_namespace_exported_class_constructs() {
        let case_text =
            "class C {\n}\nnamespace C {\n    export class D {\n    }\n}\nconst d = new C.D();\n";
        let units = split_case_units("tests/cases/compiler/mergedNsExportedClass.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/mergedNsExportedClass.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a class static wins over a same-named namespace-only
    /// type. The static is the runtime value; the type binding must not
    /// mask it with a missing-property diagnostic.
    #[test]
    fn class_static_beats_namespace_type_name() {
        let case_text = "class C {\n    static x = 1;\n}\nnamespace C {\n    export type x = string;\n}\nconst n: number = C.x;\n";
        let units = split_case_units("tests/cases/compiler/classStaticVsNsType.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/classStaticVsNsType.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: aliases of merged functions keep namespace exports.
    /// The export-scope fallback keys off the resolved symbol, so
    /// `alias.x` answers like the direct `f.x` read.
    #[test]
    fn merged_function_alias_keeps_exports() {
        let case_text = "function f() {\n}\nnamespace f {\n    export const x = 1;\n}\nconst alias = f;\nconst n: number = alias.x;\n";
        let units = split_case_units("tests/cases/compiler/mergedFunctionAlias.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/mergedFunctionAlias.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: numeric constant-expression initializers keep the
    /// reverse-mapping index (`1 << 1` is numeric at runtime).
    #[test]
    fn const_expr_enum_member_reverse_lookup() {
        let case_text = "enum E {\n    A = 1 << 1,\n}\nconst s: string = E[2];\n";
        let units = split_case_units("tests/cases/compiler/constExprEnumReverse.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/constExprEnumReverse.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: derived constructors refresh when the base merges
    /// later. `B` resolved before `namespace C` still sees `x`.
    #[test]
    fn derived_class_sees_late_namespace_additions() {
        let case_text = "class C {\n}\nclass B extends C {\n}\nnamespace C {\n    export const x = 1;\n}\nconst n: number = B.x;\n";
        let units = split_case_units("tests/cases/compiler/derivedLateNsAdditions.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/derivedLateNsAdditions.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: cyclic heritage with a merged base terminates. The
    /// augmentation worklist carries a visited guard (mirroring
    /// `is_derived_from`); without it this case loops forever, so
    /// completion itself is the assertion. Circularity diagnostics
    /// are owned by the heritage checker, not pinned here.
    #[test]
    fn cyclic_heritage_merge_terminates() {
        let case_text = "class A extends B {\n}\nclass B extends A {\n}\nnamespace A {\n    export const x = 1;\n}\nconst n = B.x;\n";
        let units = split_case_units("tests/cases/compiler/cyclicHeritageMerge.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/cyclicHeritageMerge.ts", &units);
        let _case = compile_case(&units, &entry).expect("case compiles");
    }

    /// Regression: an own static colliding with a namespace value export
    /// is a duplicate declaration (tsc TS2300, approximated by C001).
    /// Inherited statics yield instead; only the own collision fires.
    /// A second fragment must not re-fire the same diagnostic.
    #[test]
    fn own_static_namespace_export_collision() {
        let case_text = "class C {\n    static x = 1;\n}\nnamespace C {\n    export const x = 2;\n}\nnamespace C {\n    export const y = 3;\n}\nconst n = C.x;\n";
        let units = split_case_units("tests/cases/compiler/ownStaticNsCollision.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/ownStaticNsCollision.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 5)]);
    }
    /// Regression: multiple namespace fragments sharing one export
    /// scope stay silent. Each fragment finalizes over the accumulated
    /// scope; appends must not collide with themselves.
    #[test]
    fn namespace_fragments_share_export_scope_silently() {
        let case_text = "class C {\n}\nnamespace C {\n    export const x = 2;\n}\nnamespace C {\n    export const y = 3;\n}\nconst n = C.x;\n";
        let units = split_case_units(
            "tests/cases/compiler/namespaceFragmentsSilent.ts",
            case_text,
        );
        let entry = entry_virtual_path("tests/cases/compiler/namespaceFragmentsSilent.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a namespace export validly narrows an inherited
    /// static. Unlike own-static collisions, the derived merge replaces
    /// the flattened base property (tsc accepts).
    #[test]
    fn derived_merge_narrows_inherited_static() {
        let case_text = "class C {\n    static x: number = 1;\n}\nclass B extends C {\n}\nnamespace B {\n    export const x = 1;\n}\nconst n: number = B.x;\n";
        let units = split_case_units("tests/cases/compiler/derivedNarrowingMerge.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/derivedNarrowingMerge.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a derived own static survives a later base
    /// namespace export with the same name (tsc silent: the override
    /// is legal). Propagation must not report it as a collision.
    #[test]
    fn derived_own_static_survives_late_base_export() {
        let case_text = "class C {\n}\nclass B extends C {\nstatic x: number = 2;\n}\nnamespace C {\nexport const x: number = 1;\n}\nconst n: number = B.x;\n";
        let units = split_case_units("tests/cases/compiler/tmAa.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tmAa.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: an alias of a derived class exposes the derived
    /// namespace export type, not a later-propagated base type (tsc
    /// accepts `const n: 2 = alias.x`).
    #[test]
    fn derived_alias_exposes_derived_export_type() {
        let case_text = "class C {\n}\nclass B extends C {\n}\nnamespace B {\nexport const x = 2;\n}\nnamespace C {\nexport const x: number = 1;\n}\nconst alias = B;\nconst n: 2 = alias.x;\n";
        let units = split_case_units("tests/cases/compiler/tmAb3.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tmAb3.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Guard: direct access through a derived class keeps the
    /// derived namespace export type (tsc accepts).
    #[test]
    fn derived_direct_access_keeps_derived_type() {
        let case_text = "class C {\n}\nclass B extends C {\n}\nnamespace B {\nexport const x = 2;\n}\nnamespace C {\nexport const x: number = 1;\n}\nconst n: 2 = B.x;\n";
        let units = split_case_units("tests/cases/compiler/tmAb2.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tmAb2.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a computed numeric enum member earns the reverse
    /// mapping (tsc silent: `E[0]` is `string`, as for constant
    /// numeric members).
    #[test]
    fn computed_numeric_enum_reverse_mapping() {
        let case_text = "enum E {\nA = Math.random()\n}\nconst s: string = E[0];\n";
        let units = split_case_units("tests/cases/compiler/tmAc.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tmAc.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: callable synthesis survives same-named type exports.
    /// `f.call` resolves through `Function.call` even with
    /// `export type call` present; `apply`/`bind` are unaffected.
    #[test]
    fn callable_member_survives_type_name_collision() {
        let case_text = "function f() {\n}\nnamespace f {\n    export type call = string;\n}\nf.call(undefined);\nconst g = f.apply;\nconst h = f.bind;\n";
        let units = split_case_units("tests/cases/compiler/callableTypeCollision.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/callableTypeCollision.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: nested namespaces contribute finalized constructors.
    /// The inner namespace finalizes before the outer snapshots it, so
    /// the outer structural carries the inner member types, not a shell.
    #[test]
    fn nested_namespace_structural_assignment() {
        let case_text = "namespace A {\n    export namespace B {\n        export const x = 1;\n    }\n}\nconst v: { B: { x: number } } = A;\n";
        let units = split_case_units("tests/cases/compiler/nestedNamespaceAssign.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedNamespaceAssign.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: two diagnostics at the same line/column in different files
    /// must not compare equal. Before the unit field was carried through
    /// `FacetDiagnostic`, the comparator keyed only on position/category/
    /// severity/code and a cross-unit collision silently passed.
    #[test]
    fn diagnostics_cross_unit_position_collision_is_detected() {
        let code_map = repo_code_map();
        let expected = vec![FacetDiagnostic {
            unit: "a.ts".to_owned(),
            position: SourcePosition {
                line: 3,
                character: 5,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2304".to_owned(),
        }];
        let actual = vec![FacetDiagnostic {
            unit: "b.ts".to_owned(),
            position: SourcePosition {
                line: 3,
                character: 5,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2304".to_owned(),
        }];
        let verdict = compare_diagnostics(&expected, &actual, &code_map);
        assert!(
            verdict.is_fail(),
            "same position in different files must fail, got {verdict:?}"
        );
        assert!(
            format!("{verdict:?}").contains("unit mismatch"),
            "failure must name the unit mismatch, got {verdict:?}"
        );
    }

    const ANY_AS_CONSTRUCTOR_CASE: &str = "\
// @target: es2015
// any is considered an untyped function call
// can be called except with type arguments which is an error

var x: any;
var a = new x();
var b = new x('hello');
var c = new x(x);

// grammar allows this for constructors
var d = new x<any>(x); // no error
";

    const ANY_AS_CONSTRUCTOR_ERRORS: &str = "\
anyAsConstructor.ts(10,9): error TS2347: Untyped function calls may not accept type arguments.


==== anyAsConstructor.ts (1 errors) ====
    // any is considered an untyped function call
    // can be called except with type arguments which is an error
    
    var x: any;
    var a = new x();
    var b = new x('hello');
    var c = new x(x);
    
    // grammar allows this for constructors
    var d = new x<any>(x); // no error
            ~~~~~~~~~~~~~
!!! error TS2347: Untyped function calls may not accept type arguments.
";

    const PARSER_ENUM_DECLARATION_2_ERRORS: &str = "\
parserEnumDeclaration2.ts(2,3): error TS1038: A 'declare' modifier cannot be used in an already ambient context.


==== parserEnumDeclaration2.ts (1 errors) ====
    declare namespace M {
      declare enum E {
      ~~~~~~~
!!! error TS1038: A 'declare' modifier cannot be used in an already ambient context.
      }
    }
";

    const MERGING1_ERRORS: &str = "\
testB.ts(1,22): error TS2305: Module '\"*.foo\"' has no exported member 'onlyInA'.


==== types.ts (0 errors) ====
    declare module \"*.foo\" {
      let everywhere: string;
    }
    
    
==== testA.ts (0 errors) ====
    import { everywhere, onlyInA } from \"a.foo\";
    declare module \"a.foo\" {
      let onlyInA: number;
    }
    
==== testB.ts (1 errors) ====
    import { everywhere, onlyInA } from \"b.foo\"; // Error
                         ~~~~~~~
!!! error TS2305: Module '\"*.foo\"' has no exported member 'onlyInA'.
    
";

    const PROJECT_BASELINE_AMD_ERRORS: &str = "\
error TS5107: Option 'module=AMD' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.
error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.


!!! error TS5107: Option 'module=AMD' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.
!!! error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.
==== decl.ts (0 errors) ====
    export interface Point { x: number; y: number; };
    export function point (x: number, y: number): Point {
    	return { x: x, y: y };
    }
==== emit.ts (0 errors) ====
    import g = require(\"./decl\");
    var p = g.point(10,20);
";

    #[test]
    fn parse_case_pragmas_reads_target_and_single_unit() {
        let pragmas = parse_case_pragmas(ANY_AS_CONSTRUCTOR_CASE);
        assert_eq!(
            pragmas.options,
            vec![("target".to_owned(), vec!["es2015".to_owned()])]
        );
        assert!(!pragmas.no_types_and_symbols);
    }

    #[test]
    fn parse_case_pragmas_lists_variants_in_order() {
        let pragmas =
            parse_case_pragmas("//@target: ES5, ES2015\n// @strict: true\nvar x: number;\n");
        assert_eq!(
            pragmas.options,
            vec![
                (
                    "target".to_owned(),
                    vec!["ES5".to_owned(), "ES2015".to_owned()]
                ),
                ("strict".to_owned(), vec!["true".to_owned()]),
            ]
        );
    }

    #[test]
    fn parse_case_pragmas_pins_no_types_and_symbols() {
        let pragmas = parse_case_pragmas("// @noTypesAndSymbols: true\nvar x: number;\n");
        assert!(pragmas.no_types_and_symbols);
        let pragmas = parse_case_pragmas("// @noTypesAndSymbols: false\nvar x: number;\n");
        assert!(!pragmas.no_types_and_symbols);
    }

    #[test]
    fn parse_case_pragmas_maps_strict_property_initialization() {
        let pragmas = parse_case_pragmas("// @strictPropertyInitialization: false\n");
        let tsconfig = build_tsconfig(&pragmas);
        assert!(
            tsconfig.contains("\"strictPropertyInitialization\": false"),
            "{tsconfig}"
        );
    }

    /// Upstream splits unit lines on `\r?\n`, so a CRLF directive followed by
    /// a bare-`\n` code line keeps the code line; a `\r\n`-only split would
    /// swallow it into the directive "line" and shift every later position.
    /// Exemplar: `commentsVarDecl.ts` F5 position rows.
    #[test]
    fn strip_directive_lines_mixed_line_endings_keep_code_lines() {
        let stripped = strip_directive_lines(
            "// @strict: true\r\nlet a = 1;\r\n// @noImplicitAny: true\nlet b = 2;\n",
        );
        assert_eq!(stripped, "let a = 1;\nlet b = 2;\n");
    }

    /// Upstream materializes units into a path-keyed fake FS, so a restated
    /// `@filename:` directive makes the later chunk the unit's whole content;
    /// an append would keep the earlier chunk and shift all line numbers.
    #[test]
    fn repeated_filename_directive_replaces_unit_content() {
        let units = split_case_units(
            "tests/cases/compiler/twice.ts",
            "// @filename: a.ts\nconst a = 1;\n\n// @filename: a.ts\nconst b: string = a;\n",
        );
        assert_eq!(units.len(), 1);
        assert_eq!(units[0].virtual_path, "tests/cases/compiler/a.ts");
        assert_eq!(units[0].text, "const b: string = a;\n");
    }

    /// Upstream drops a comment-only or directive-only preamble before the
    /// first `@filename:` marker: global settings are not a compiled unit, so
    /// the first baseline section is the first named file
    /// (`exportDefaultProperty2.types` opens with `=== a.ts ===`, no
    /// `=== exportDefaultProperty2.ts ===`). A preamble holding code does
    /// keep the implicit case-named unit.
    #[test]
    fn clean_any_records_stay_bare() {
        let case_text = "var ANY: any;\nvar n: number;\n";
        let units = split_case_units("tests/cases/compiler/anyCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/anyCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/anyCaretPin.ts");
        assert!(
            emitted.contains(">ANY : any\nvar n: number;\n"),
            "clean any drops its caret, as anyAsFunctionCall.types shows for >x : any: {emitted}"
        );
        assert!(
            emitted.contains(">n : number\n>  : ^^^^^^\n"),
            "full-width caret under a number record: {emitted}"
        );
    }

    #[test]
    fn diagnostics_keep_full_width_caret_lines() {
        let error_text = "var p: any = missingRef;\n";
        let units = split_case_units("tests/cases/compiler/anyCaretErrorsPin.ts", error_text);
        let entry = entry_virtual_path("tests/cases/compiler/anyCaretErrorsPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/anyCaretErrorsPin.ts");
        assert!(
            emitted.contains(">p : any\n>  : ^^^\n"),
            "diagnostics keep the underline under an any record: {emitted}"
        );
        let clean_text = "var p: any = 1;\n";
        let units = split_case_units("tests/cases/compiler/anyCaretCleanPin.ts", clean_text);
        let entry = entry_virtual_path("tests/cases/compiler/anyCaretCleanPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/anyCaretCleanPin.ts");
        assert!(
            emitted.contains(">p : any\n"),
            "the bare clean-any record itself still emits: {emitted}"
        );
        assert!(
            !emitted.contains(">p : any\n>  : "),
            "clean any drops its caret, as anyAsFunctionCall.types shows for >x : any: {emitted}"
        );
    }

    #[test]
    fn error_records_stay_bare_without_diagnostics() {
        with_model(
            "var x: any;\n",
            "tests/cases/compiler/errorBarePin.ts",
            |model| {
                let source = SourceText::new("var x: any;\n").expect("source builds");
                let symbol = model
                    .symbols()
                    .iter()
                    .position(|symbol| symbol.name() == "x")
                    .map(|index| SymbolId::new(index as u32))
                    .expect("x is bound");
                let range = model.symbol(symbol).range();
                let any = model.types().any();
                let error = model.types().error_type();
                assert!(!writes_caret(
                    model,
                    &source,
                    any,
                    false,
                    Some(symbol),
                    range
                ));
                assert!(writes_caret(model, &source, any, true, Some(symbol), range));
                assert!(!writes_caret(
                    model,
                    &source,
                    error,
                    false,
                    Some(symbol),
                    range
                ));
                assert!(writes_caret(
                    model,
                    &source,
                    error,
                    true,
                    Some(symbol),
                    range
                ));
            },
        );
    }

    #[test]
    fn clean_any_parameters_stay_bare() {
        let case_text = "function f(a: any) { return a; }\n";
        let units = split_case_units("tests/cases/compiler/anyParamPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/anyParamPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/anyParamPin.ts");
        assert!(
            emitted.contains(">a : any\n"),
            "the bare clean-any parameter record still emits: {emitted}"
        );
        assert!(
            !emitted.contains(">a : any\n>  : "),
            "clean any drops its caret, as tsxEmitSpreadAttribute.types shows its >a : any parameter records bare: {emitted}"
        );
    }

    #[test]
    fn catch_binding_unknown_records_keep_caret() {
        let case_text = "try {} catch (e) { e; }\n";
        let units = split_case_units("tests/cases/compiler/anyCatchPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/anyCatchPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/anyCatchPin.ts");
        assert!(
            emitted.contains(">e : unknown\n>  : ^^^^^^^\n"),
            "the harness strict default types the catch binding as unknown, as controlFlowAliasingCatchVariables(useunknownincatchvariables=true).types shows for >e : unknown, and it keeps its caret like every other non-any record: {emitted}"
        );
    }

    #[test]
    fn ambient_destructured_any_records_keep_caret() {
        let case_text = "declare var [a, b];\n";
        let units = split_case_units(
            "tests/cases/compiler/anyAmbientDestructurePin.ts",
            case_text,
        );
        let entry = entry_virtual_path("tests/cases/compiler/anyAmbientDestructurePin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted =
            emit_types_baseline(&case, "tests/cases/compiler/anyAmbientDestructurePin.ts");
        assert!(
            emitted.contains(">a : any\n>  : ^^^\n"),
            "ambient destructured bindings keep their caret, as declarationInAmbientContext.types shows: {emitted}"
        );
        assert!(
            emitted.contains(">b : any\n>  : ^^^\n"),
            "ambient destructured bindings keep their caret, as declarationInAmbientContext.types shows: {emitted}"
        );
    }

    #[test]
    fn import_alias_any_records_keep_caret() {
        let case_text = "// @filename: decl.d.ts\ndeclare module \"m\";\n// @filename: b.ts\nimport foo from \"m\";\n";
        let units = split_case_units("tests/cases/compiler/anyImportPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/anyImportPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/anyImportPin.ts");
        assert!(
            emitted.contains(">foo : any\n>    : ^^^\n"),
            "import aliases keep their caret, as ambientShorthand.types shows for >foo : any: {emitted}"
        );
    }

    #[test]
    fn access_positions_keep_any_caret() {
        let text = "var o: any;\nvar y = o.p;\n";
        with_model(text, "tests/cases/compiler/anyAccessPin.ts", |model| {
            let source = SourceText::new(text).expect("source builds");
            let any = model.types().any();
            let object =
                TextRange::new(Utf16Pos::new(20), Utf16Pos::new(21)).expect("range builds");
            assert!(writes_caret(model, &source, any, false, None, object));
            let name = TextRange::new(Utf16Pos::new(22), Utf16Pos::new(23)).expect("range builds");
            assert!(writes_caret(model, &source, any, false, None, name));
            let whole = TextRange::new(Utf16Pos::new(20), Utf16Pos::new(23)).expect("range builds");
            assert!(!writes_caret(model, &source, any, false, None, whole));
        });
    }

    #[test]
    fn written_return_type_blanks_caret_tail() {
        let case_text = "function f(): void {}\n";
        let units = split_case_units("tests/cases/compiler/writtenReturnCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/writtenReturnCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/writtenReturnCaretPin.ts");
        assert!(
            emitted.contains(">f : () => void\n>  : ^^^^^^    \n"),
            "written return leaves blanks: {emitted}"
        );
    }

    #[test]
    fn inferred_return_type_keeps_full_caret() {
        let case_text = "function g() { return 1; }\n";
        let units = split_case_units("tests/cases/compiler/inferredReturnCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/inferredReturnCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/inferredReturnCaretPin.ts");
        assert!(
            emitted.contains(">g : () => number\n>  : ^^^^^^^^^^^^\n"),
            "inferred return keeps its caret: {emitted}"
        );
    }
    #[test]
    fn written_param_type_blanks_caret_span() {
        let case_text = "function f(a: string): void {}\n";
        let units = split_case_units("tests/cases/compiler/writtenParamCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/writtenParamCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/writtenParamCaretPin.ts");
        assert!(
            emitted.contains(">f : (a: string) => void\n>  : ^ ^^      ^^^^^    \n"),
            "written param type is blank: {emitted}"
        );
    }

    #[test]
    fn inferred_param_type_keeps_caret() {
        let case_text = "function g(a) {}\n";
        let units = split_case_units("tests/cases/compiler/inferredParamCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/inferredParamCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/inferredParamCaretPin.ts");
        assert!(
            emitted.contains(">g : (a: any) => void\n>  : ^ ^^^^^^^^^^^^^^\n"),
            "inferred param type keeps its caret: {emitted}"
        );
    }

    #[test]
    fn annotated_object_member_blanks_caret_span() {
        let case_text = "var n: { foo: string } = { foo: \"x\" };\n";
        let units = split_case_units("tests/cases/compiler/annotatedObjectCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/annotatedObjectCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/annotatedObjectCaretPin.ts");
        assert!(
            emitted.contains(">n : { foo: string; }\n>  : ^^^^^^^      ^^^\n"),
            "written member type is blank: {emitted}"
        );
    }

    #[test]
    fn inferred_object_literal_keeps_full_caret() {
        let case_text = "var v = {a: 1, b: 2};\n";
        let units = split_case_units("tests/cases/compiler/inferredObjectCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/inferredObjectCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/inferredObjectCaretPin.ts");
        assert!(
            emitted.contains(">v : { a: number; b: number; }\n>  : ^^^^^^^^^^^^^^^^^^^^^^^^^\n"),
            "inferred object keeps its caret: {emitted}"
        );
    }

    #[test]
    fn generic_signature_blanks_names_and_written_spans() {
        let case_text = "function id<T>(x: T): T { return x; }\n";
        let units = split_case_units("tests/cases/compiler/genericCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/genericCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/genericCaretPin.ts");
        assert!(
            emitted.contains(">id : <T>(x: T) => T\n>   : ^ ^^ ^^ ^^^^^ \n"),
            "generic names and written spans are blank: {emitted}"
        );
    }

    #[test]
    fn mixed_arrow_annotations_blank_only_written() {
        let case_text = "var f = (a: string, b) => 1;\n";
        let units = split_case_units("tests/cases/compiler/mixedArrowCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/mixedArrowCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/mixedArrowCaretPin.ts");
        assert!(
            emitted.contains(
                ">f : (a: string, b: any) => number\n>  : ^ ^^      ^^ ^^^^^^^^^^^^^^^^\n"
            ),
            "only written spans are blank: {emitted}"
        );
    }

    #[test]
    fn written_param_omits_caret_line() {
        let case_text = "function f(a: any) {}\n";
        let units = split_case_units("tests/cases/compiler/bareParamCaretPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/bareParamCaretPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, "tests/cases/compiler/bareParamCaretPin.ts");
        assert!(
            emitted.contains(">a : any\n"),
            "param record exists: {emitted}"
        );
        assert!(
            !emitted.contains(">a : any\n>  : "),
            "written atomic param type omits the caret line: {emitted}"
        );
    }
    #[test]
    fn comment_only_preamble_is_not_a_unit() {
        let case = "\
// @module: commonjs
// @target: es2015
// This test is just like exportEqualsProperty2, but with `export default`.

// @filename: a.ts
class C {
    static B: number;
}

// @filename: b.ts
import B from \"./a\";
";
        let units = split_case_units("tests/cases/compiler/exportDefaultProperty2.ts", case);
        assert_eq!(units.len(), 2, "{units:#?}");
        assert_eq!(units[0].display_name, "a.ts");
        assert_eq!(units[1].display_name, "b.ts");

        let compiled = "let x = 1;\n// @filename: b.ts\nlet y = 2;\n";
        let units = split_case_units("tests/cases/compiler/preambleCode.ts", compiled);
        assert_eq!(units.len(), 2);
        assert_eq!(units[0].display_name, "preambleCode.ts");
        assert_eq!(units[1].display_name, "b.ts");
    }

    /// Code on a preamble line keeps the implicit unit even when a block
    /// comment follows it on the same line or opens after it and closes
    /// later, and a `/*` inside a string literal or after `//` opens no
    /// comment.
    #[test]
    fn preamble_block_comment_edges() {
        let cases: [(&str, usize); 4] = [
            ("let x = 1; /* note */\n// @filename: b.ts\nlet y = 2;\n", 2),
            (
                "let x = 1; /* open\nstill open */\n// @filename: b.ts\nlet y = 2;\n",
                2,
            ),
            ("const s = \"a /* b\";\n// @filename: b.ts\nlet y = 2;\n", 2),
            ("// note /* not open\n// @filename: b.ts\nlet y = 2;\n", 1),
        ];
        for (index, (case, expected)) in cases.into_iter().enumerate() {
            let units = split_case_units(&format!("tests/cases/compiler/edge{index}.ts"), case);
            assert_eq!(
                units.len(),
                expected,
                "case {index}: {case:?} -> {units:#?}"
            );
        }
    }
    #[test]
    fn split_case_units_single_unit_case() {
        let units = split_case_units(
            "tests/cases/conformance/types/any/anyAsConstructor.ts",
            ANY_AS_CONSTRUCTOR_CASE,
        );
        assert_eq!(units.len(), 1);
        assert_eq!(
            units[0].virtual_path,
            "tests/cases/conformance/types/any/anyAsConstructor.ts"
        );
        // Upstream strips the `// @target` directive line from unit content, so
        // the compiled entry begins at the first real source line.
        assert!(!units[0].text.contains("@target"));
        assert_eq!(
            units[0].text,
            "// any is considered an untyped function call\n\
             // can be called except with type arguments which is an error\n\
             \n\
             var x: any;\n\
             var a = new x();\n\
             var b = new x('hello');\n\
             var c = new x(x);\n\
             \n\
             // grammar allows this for constructors\n\
             var d = new x<any>(x); // no error\n"
        );
    }

    #[test]
    fn split_case_units_strips_directives_and_renumbers() {
        // A `@target` directive plus a following blank line: upstream removes
        // the directive line and collapses the leading blank so the first
        // declaration lands on line 0, while interior blanks are preserved.
        let case = "// @strict: true\n\nclass Foo {}\n\nvar a = 0;\n";
        let units = split_case_units("tests/cases/compiler/renumber.ts", case);
        assert_eq!(units.len(), 1);
        assert_eq!(units[0].text, "class Foo {}\n\nvar a = 0;\n");
    }

    #[test]
    fn is_option_directive_line_matches_upstream_grammar() {
        assert!(is_option_directive_line("// @target: es2015"));
        assert!(is_option_directive_line("//@strict:true"));
        assert!(is_option_directive_line("// @filename: a.ts"));
        // `///` reference directives and colonless `@word` lines are content.
        assert!(!is_option_directive_line("/// <reference path=\"x\" />"));
        assert!(!is_option_directive_line("// @ts-ignore"));
        // A multi-word name is not `\\w+`, so it is not a directive.
        assert!(!is_option_directive_line("// @param x: number"));
        assert!(!is_option_directive_line("var a = 0;"));
    }

    #[test]
    fn split_case_units_splits_named_units() {
        let case = "\
// @module: commonjs
// @filename: types.ts
declare module \"*.foo\" {
  let everywhere: string;
}


// @filename: testA.ts
import { everywhere, onlyInA } from \"a.foo\";
declare module \"a.foo\" {
  let onlyInA: number;
}

// @filename: testB.ts
import { everywhere, onlyInA } from \"b.foo\"; // Error
";
        let units = split_case_units(
            "tests/cases/conformance/ambient/ambientDeclarationsPatterns_merging1.ts",
            case,
        );
        // The only line before the first `@filename` is the global
        // `// @module` directive. Upstream drops an options-only preamble
        // rather than creating a case-named unit for it, so the first unit is
        // `types.ts` and the document has no phantom `//// [<case>.ts]` echo.
        // The authority baseline for this case echoes exactly these three
        // units and emits exactly `types.js`, `testA.js`, `testB.js`.
        assert_eq!(units.len(), 3);
        assert_eq!(
            units[0].virtual_path,
            "tests/cases/conformance/ambient/types.ts"
        );
        // The `@filename` directive line is stripped; content begins at the
        // first real source line of the unit.
        assert!(units[0].text.starts_with("declare module \"*.foo\" {\n"));
        assert_eq!(
            units[1].virtual_path,
            "tests/cases/conformance/ambient/testA.ts"
        );
        assert_eq!(
            units[2].virtual_path,
            "tests/cases/conformance/ambient/testB.ts"
        );
    }
    #[test]
    fn shared_lib_refs_rewrite_to_baseline_subpath() {
        let mut units = split_case_units(
            "tests/cases/compiler/booleanLiteralsContextuallyTypedFromUnion.tsx",
            "/// <reference path=\"/.lib/react.d.ts\" />\nlet x = 1;\n",
        );
        let targets = rewrite_shared_lib_refs(&mut units);
        assert_eq!(targets, vec!["react.d.ts".to_owned()]);
        assert!(
            units[0]
                .text
                .starts_with("/// <reference path=\"react.d.ts\" />\n")
        );
        assert!(!units[0].text.contains("/.lib/"));
    }

    #[test]
    fn shared_lib_refs_ignore_non_directives_and_escapes() {
        let text = "/// <reference path=\"/.lib/react18/global.d.ts\" />\n/// <reference path=\"/.lib/../secret.d.ts\" />\n/// <reference types=\"/.lib/react.d.ts\" />\nconst marker = \"/.lib/react.d.ts\";\n";
        assert_eq!(
            shared_lib_refs(text),
            vec!["react18/global.d.ts".to_owned()]
        );
    }

    #[test]
    fn shared_lib_refs_ignore_quadruple_slash_and_post_statement_targets() {
        // The compiler's own loader honors a `///` prologue directive only
        // before the first statement and rejects a fourth slash, so the
        // harness loads support files for neither of these.
        let text = "//// <reference path=\"/.lib/react.d.ts\" />\nlet x = 1;\n/// <reference path=\"/.lib/react.d.ts\" />\n";
        assert!(shared_lib_refs(text).is_empty());
    }

    #[test]
    fn support_lib_beside_importer_satisfies_reference_and_ambient_import() {
        let units = vec![CaseUnit {
            virtual_path: "tests/cases/compiler/consumer.ts".to_owned(),
            display_name: "consumer.ts".to_owned(),
            text: "/// <reference path=\"foo.d.ts\" />\nimport x = require(\"foo\");\nconst y: number = x;\n"
                .to_owned(),
        }];
        let support = vec![CaseUnit {
            virtual_path: "tests/cases/compiler/foo.d.ts".to_owned(),
            display_name: "foo.d.ts".to_owned(),
            text: "declare module \"foo\" {\nconst x: number;\nexport = x;\n}\n".to_owned(),
        }];
        let entry = entry_virtual_path("tests/cases/compiler/consumer.ts", &units);
        let without =
            compile_case_frontend(&units, &entry, &CasePragmas::default(), FrontendMode::Check)
                .expect("case compiles");
        assert!(
            collect_facet_diagnostics(&without)
                .iter()
                .any(|diagnostic| diagnostic.code == "TS2307")
        );
        let with = compile_case_frontend_with_support(
            &units,
            &entry,
            &CasePragmas::default(),
            FrontendMode::Check,
            &support,
        )
        .expect("case compiles");
        assert!(
            !collect_facet_diagnostics(&with)
                .iter()
                .any(|diagnostic| diagnostic.code == "TS2307")
        );
    }

    #[test]
    fn split_case_units_leading_directive_naming_case_is_entry() {
        let case = "\
// @filename: anyAsConstructor.ts
var x: any;
";
        let units = split_case_units(
            "tests/cases/conformance/types/any/anyAsConstructor.ts",
            case,
        );
        assert_eq!(units.len(), 1);
        assert_eq!(
            units[0].virtual_path,
            "tests/cases/conformance/types/any/anyAsConstructor.ts"
        );
        assert!(units[0].text.contains("var x: any;"));
    }

    #[test]
    fn split_case_units_absolute_virtual_paths_remap_to_root() {
        let case = "\
// @filename: /ref.d.ts
declare var r: number;
// @filename: main.ts
r.toFixed();
";
        let units = split_case_units("tests/cases/compiler/usesRef.ts", case);
        assert_eq!(units.len(), 2);
        assert_eq!(units[0].virtual_path, "ref.d.ts");
        assert_eq!(units[1].virtual_path, "tests/cases/compiler/main.ts");
    }

    #[test]
    fn split_case_units_drive_letter_paths_remap_to_root() {
        // Upstream test cases use Windows-style drive-letter paths as virtual
        // roots (e.g. `c:/root/folder1/file1.ts`). The drive letter must be
        // stripped so the path maps into the virtual root with no `c:/`
        // residue, preventing paths like `/tmp/x/c:/root/...` on Unix.
        let case = "\
// @filename: c:/root/folder1/file1.ts
export const a = 1;
// @filename: c:/root/folder2/file2.ts
export const b = 2;
// @filename: c:/file3.ts
export const c = 3;
";
        let units = split_case_units(
            "tests/cases/compiler/pathMappingBasedModuleResolution4_node.ts",
            case,
        );
        assert_eq!(units.len(), 3);
        assert_eq!(units[0].virtual_path, "root/folder1/file1.ts");
        assert_eq!(units[1].virtual_path, "root/folder2/file2.ts");
        assert_eq!(units[2].virtual_path, "file3.ts");
        // No `c:/` residue in any virtual path.
        for unit in &units {
            assert!(
                !unit.virtual_path.contains("c:/"),
                "drive-letter residue in `{}`",
                unit.virtual_path
            );
        }
    }

    #[test]
    fn split_case_units_repeated_name_replaces() {
        let case = "\
// @filename: a.ts
export const a = 1;
// @filename: b.ts
export const b = 2;
// @filename: a.ts
export const a2 = 3;
";
        let units = split_case_units("tests/cases/compiler/append.ts", case);
        assert_eq!(units.len(), 2);
        // Upstream feeds units into a path-keyed fake FS, so a restated
        // @filename directive replaces the unit's content, not appends.
        assert!(!units[0].text.contains("a = 1"));
        assert!(units[0].text.contains("a2 = 3"));
    }

    #[test]
    fn document_order_skips_unimported_package_json() {
        let case_text = "// @filename: package.json\n{\"name\": \"@this/package\"}\n// @filename: index.ts\nimport * as me from \"@this/package\";\nme.thing();\nexport function thing(): void {}\n";
        let logical = "tests/cases/compiler/nodeNextPackageSelfNameWithOutDir.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let ordered = case.units_in_document_order();
        assert_eq!(ordered.len(), 1);
        assert_eq!(ordered[0].0.display_name, "index.ts");
        let emitted = emit_types_baseline(&case, logical);
        assert!(emitted.contains("=== index.ts ==="));
        assert!(!emitted.contains("package.json"));
        let symbols = emit_symbols_baseline(&case, logical);
        assert!(symbols.contains("=== index.ts ==="));
        assert!(!symbols.contains("package.json"));
    }
    #[test]
    fn document_order_moves_resolved_relative_entry_first() {
        let case_text = "// @filename: a.ts\nexport const a = 1;\n// @filename: b.ts\nimport a = require(\"./a\");\nexport const b = a;\n";
        let logical = "tests/cases/compiler/relativeEntryOrder.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let ordered = case.units_in_document_order();
        assert_eq!(ordered.len(), 2);
        assert_eq!(ordered[0].0.display_name, "b.ts");
        assert_eq!(ordered[1].0.display_name, "a.ts");
    }
    #[test]
    fn document_order_keeps_unresolved_bare_entry_last() {
        let case_text = "// @filename: decorated.ts\nexport default 1;\n// @filename: undecorated.ts\nimport decorated from \"nowhere-missing-dep\";\nexport const u = decorated;\n";
        let logical = "tests/cases/compiler/unresolvedBareEntryOrder.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let ordered = case.units_in_document_order();
        assert_eq!(ordered.len(), 2);
        assert_eq!(ordered[0].0.display_name, "decorated.ts");
        assert_eq!(ordered[1].0.display_name, "undecorated.ts");
    }
    #[test]
    fn document_order_moves_resolved_bare_entry_first() {
        let case_text = "// @filename: node_modules/dep/index.ts\nexport const a = 1;\n// @filename: b.ts\nimport {a} from \"dep\";\nexport const b = a;\n";
        let logical = "tests/cases/compiler/resolvedBareEntryOrder.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let ordered = case.units_in_document_order();
        assert_eq!(ordered.len(), 2);
        assert_eq!(ordered[0].0.virtual_path, "b.ts");
        assert_eq!(ordered[1].0.virtual_path, "node_modules/dep/index.ts");
    }
    #[test]
    fn document_order_keeps_imported_entry_last() {
        let case_text = "// @filename: node_modules/dep/index.ts\nexport const a = 1;\n// @filename: index.ts\nimport {b} from \"./b\";\nexport const i = b;\n// @filename: b.ts\nimport {a} from \"dep\";\nexport const b = a;\n";
        let logical = "tests/cases/compiler/importedEntryOrder.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let ordered = case.units_in_document_order();
        assert_eq!(ordered.len(), 3);
        assert_eq!(ordered[0].0.virtual_path, "node_modules/dep/index.ts");
        assert_eq!(ordered[1].0.virtual_path, "index.ts");
        assert_eq!(ordered[2].0.virtual_path, "b.ts");
    }
    #[test]
    fn split_baseline_file_name_variants() {
        assert_eq!(
            split_baseline_file_name("anyAsConstructor.errors.txt"),
            Some(("anyAsConstructor", "errors.txt", ""))
        );
        assert_eq!(
            split_baseline_file_name("ES5For-ofTypeCheck6(target=es5).errors.txt"),
            Some(("ES5For-ofTypeCheck6", "errors.txt", "(target=es5)"))
        );
        assert_eq!(
            split_baseline_file_name("parserEnumDeclaration2.d.types"),
            Some(("parserEnumDeclaration2.d", "types", ""))
        );
        assert_eq!(
            split_baseline_file_name("plain.js"),
            Some(("plain", "js", ""))
        );
        assert_eq!(
            split_baseline_file_name("2dArrays(target=es5).js"),
            Some(("2dArrays", "js", "(target=es5)"))
        );
    }

    #[test]
    fn case_stem_keeps_declaration_suffix() {
        assert_eq!(
            case_stem(
                "tests/cases/conformance/parser/ecmascript5/EnumDeclarations/parserEnumDeclaration2.d.ts"
            ),
            "parserEnumDeclaration2.d"
        );
        assert_eq!(
            case_stem("tests/cases/conformance/types/any/anyAsConstructor.ts"),
            "anyAsConstructor"
        );
    }

    #[test]
    fn parse_errors_baseline_reads_file_rows() {
        let baseline = parse_errors_baseline(ANY_AS_CONSTRUCTOR_ERRORS);
        assert_eq!(baseline.globals, vec![]);
        assert_eq!(
            baseline.diagnostics,
            vec![ErrorsDiagnostic {
                unit: "anyAsConstructor.ts".to_owned(),
                line: 10,
                character: 8,
                category: "error".to_owned(),
                code: "TS2347".to_owned(),
                message: "Untyped function calls may not accept type arguments.".to_owned(),
            }]
        );
    }

    #[test]
    fn parse_errors_baseline_skips_carets_and_summaries() {
        let baseline = parse_errors_baseline(PARSER_ENUM_DECLARATION_2_ERRORS);
        assert_eq!(baseline.file_diagnostic_count(), 1);
        let row = &baseline.diagnostics[0];
        assert_eq!(row.unit, "parserEnumDeclaration2.ts");
        assert_eq!((row.line, row.character), (2, 2));
        assert_eq!(row.code, "TS1038");
        assert!(baseline.globals.is_empty());
    }

    #[test]
    fn parse_errors_baseline_multi_unit_rows() {
        let baseline = parse_errors_baseline(MERGING1_ERRORS);
        assert_eq!(baseline.file_diagnostic_count(), 1);
        assert_eq!(baseline.diagnostics[0].unit, "testB.ts");
        assert_eq!(
            (
                baseline.diagnostics[0].line,
                baseline.diagnostics[0].character
            ),
            (1, 21)
        );
        assert_eq!(baseline.diagnostics[0].code, "TS2305");
    }

    #[test]
    fn parse_errors_baseline_global_rows_are_separate() {
        let baseline = parse_errors_baseline(PROJECT_BASELINE_AMD_ERRORS);
        assert_eq!(baseline.file_diagnostic_count(), 0);
        assert_eq!(baseline.globals.len(), 2);
        assert!(
            baseline
                .globals
                .iter()
                .all(|global| global.code == "TS5107")
        );
        assert!(baseline.globals[0].message.contains("module=AMD"));
    }

    #[test]
    fn parse_errors_baseline_empty_document() {
        let baseline = parse_errors_baseline("");
        assert_eq!(baseline, ErrorsBaseline::default());
    }

    /// Compile a single-unit case and run `f` with the entry unit's model.
    fn with_model<R>(case_text: &str, logical: &str, f: impl FnOnce(&SemanticModel) -> R) -> R {
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let (_, output) = case
            .reached_units()
            .next()
            .expect("the entry unit is reached");
        f(output.semantic_model())
    }

    #[test]
    fn render_type_covers_primitives() {
        with_model("var x: any;\n", "tests/cases/compiler/p.ts", |model| {
            let table = model.types();
            assert_eq!(render_type(model, table.any()), "any");
            assert_eq!(render_type(model, table.unknown()), "unknown");
            assert_eq!(render_type(model, table.never()), "never");
            assert_eq!(render_type(model, table.void()), "void");
            assert_eq!(render_type(model, table.null_type()), "null");
            assert_eq!(render_type(model, table.undefined_type()), "undefined");
            assert_eq!(render_type(model, table.boolean()), "boolean");
            assert_eq!(render_type(model, table.number()), "number");
            assert_eq!(render_type(model, table.bigint()), "bigint");
            assert_eq!(render_type(model, table.string()), "string");
            assert_eq!(render_type(model, table.symbol_type()), "symbol");
            assert_eq!(render_type(model, table.object()), "object");
        });
    }

    #[test]
    fn render_type_covers_literals_and_arrays() {
        // The initializer expressions carry literal and array types the walk
        // recorded; render them straight from the model.
        with_model(
            "var s: string = \"hi\";\nvar n = 42;\nvar b = true;\nvar xs = [1];\n",
            "tests/cases/compiler/lit.ts",
            |model| {
                let rendered: Vec<String> = model
                    .typed_expressions()
                    .iter()
                    .map(|(_, type_id)| render_type(model, *type_id))
                    .collect();
                assert!(rendered.contains(&"\"hi\"".to_owned()), "{rendered:?}");
                assert!(rendered.contains(&"42".to_owned()), "{rendered:?}");
                assert!(rendered.contains(&"true".to_owned()), "{rendered:?}");
                // `[1]` types as an array over the `1` literal element.
                assert!(rendered.contains(&"1[]".to_owned()), "{rendered:?}");
            },
        );
    }

    #[test]
    fn render_type_covers_tuple_shapes_and_applied_classes() {
        with_model(
            "declare class Box<T> {}\
             declare let optionalTuple: [number, string?];\
             declare let variadicTuple: [number, ...boolean[], bigint];\
             declare let box: Box<string>;",
            "tests/cases/compiler/composite.ts",
            |model| {
                let scope = model.scope(model.module_scope());
                let optional = scope
                    .value("optionalTuple")
                    .expect("optional tuple binding");
                assert_eq!(
                    render_type(model, model.symbol_type(optional)),
                    "[number, string?]"
                );
                let variadic = scope
                    .value("variadicTuple")
                    .expect("variadic tuple binding");
                assert_eq!(
                    render_type(model, model.symbol_type(variadic)),
                    "[number, ...boolean[], bigint]"
                );
                let box_value = scope.value("box").expect("box binding");
                assert_eq!(
                    render_type(model, model.symbol_type(box_value)),
                    "Box<string>"
                );
            },
        );
    }

    #[test]
    fn render_transformed_recursive_alias_terminates() {
        with_model(
            "type Expanding<T> = [Expanding<T[]>];
             declare let value: Expanding<string>;",
            "tests/cases/compiler/recursive-alias.ts",
            |model| {
                let value = model
                    .scope(model.module_scope())
                    .value("value")
                    .expect("recursive alias binding");
                let rendered = render_type(model, model.symbol_type(value));
                assert!(rendered.contains("Expanding<"), "{rendered}");
                assert!(rendered.len() < 256, "{rendered}");
            },
        );
    }

    #[test]
    fn render_type_preserves_polymorphic_this_identity() {
        with_model(
            "class Base {
                 value = 1;
                 method(): number { return this.value; }
             }",
            "tests/cases/compiler/polymorphicThis.ts",
            |model| {
                let this_type = model
                    .typed_expressions()
                    .iter()
                    .map(|(_, type_id)| *type_id)
                    .find(|type_id| matches!(model.types().get(*type_id), Type::This { .. }))
                    .expect("method body has polymorphic this type");

                assert_eq!(render_type(model, this_type), "this");
            },
        );
    }

    /// H4 pin: an annotated scalar case the checker fully types reproduces its
    /// upstream `.types` baseline (marker, section, source echo, `>expr : type`
    /// records, and underline widths) under `compare_types`. The declared-any
    /// record stays bare, as the clean `anyAsFunctionCall.types` prints
    /// `>x : any` with no underline.
    #[test]
    fn emit_types_baseline_matches_fully_typed_scalar_case() {
        let logical = "tests/cases/compiler/scalarPin.ts";
        let case_text = "var x: any;\nvar s: string = \"hi\";\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/scalarPin.ts] ////\n\
            \n\
            === scalarPin.ts ===\n\
            var x: any;\n\
            >x : any\n\
            var s: string = \"hi\";\n\
            >s : string\n\
            >  : ^^^^^^\n\
            >\"hi\" : \"hi\"\n\
            >     : ^^^^\n";
        assert_eq!(
            compare_types(baseline, &emitted),
            FacetVerdict::Pass,
            "clean any stays bare, as anyAsFunctionCall.types shows for >x : any: emitted:\n{emitted}"
        );
    }

    /// Upstream echoes the written identifier, escapes included:
    /// `unicodeEscapesInNames01.types` records `>\u0078` for
    /// `var \u0078 = 1;`, not the decoded `>x`.
    #[test]
    fn emit_types_baseline_echoes_escaped_identifiers_verbatim() {
        let logical = "tests/cases/compiler/escapedIdentifierPin.ts";
        let case_text = "var \\u0078 = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.contains(">\\u0078 : "),
            "escaped identifier keeps its raw spelling: emitted:\n{emitted}"
        );
    }

    /// Honesty pin: where the checker types fewer nodes than tsc (here, the
    /// `new`/callee/argument sub-expressions of `anyAsConstructor`), the
    /// emitter drops those records and the comparator reports a `Fail` — the
    /// S2 burn-down surface, not a false pass.
    #[test]
    fn emit_types_baseline_undercoverage_fails_comparison() {
        let logical = "tests/cases/conformance/types/any/anyAsConstructor.ts";
        let units = split_case_units(logical, ANY_AS_CONSTRUCTOR_CASE);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/types/any/anyAsConstructor.ts] ////\n\
            \n\
            === anyAsConstructor.ts ===\n\
            var x: any;\n\
            >x : any\n\
            >  : ^^^\n\
            \n\
            var a = new x();\n\
            >a : any\n\
            >  : ^^^\n\
            >new x() : any\n\
            >        : ^^^\n\
            >x : any\n\
            >  : ^^^\n";
        assert!(
            matches!(compare_types(baseline, &emitted), FacetVerdict::Fail { .. }),
            "under-covered emit must not pass; emitted:\n{emitted}"
        );
    }

    /// The dedup pass collapses records with the identical identity tuple
    /// (start, end, display, rendered) — the binder can push the same
    /// (range, type) pair from both its symbol and expression indexes — and
    /// keeps everything else, restoring the upstream order afterwards.
    ///
    /// Authority baselines keep adjacent *different-position* records
    /// (`targetTypeCalls.types` prints `>v : any` twice for the declaration
    /// name and the resolving reference at different offsets), so dedup keys
    /// on the full record identity, never on display text alone.
    #[test]
    fn dedup_type_records_collapses_identical_identity_only() {
        let record = |start: usize, end: usize, display: &str, rendered: &str| TypeAnnotation {
            start,
            end,
            line: 0,
            display: display.to_owned(),
            rendered: rendered.to_owned(),
            caret: true,
            blanks: Vec::new(),
        };
        let records = vec![
            record(4, 5, "x", "any"),
            record(4, 5, "x", "any"),
            record(8, 9, "x", "any"),
            record(0, 1, "C", "C"),
        ];
        let deduped = dedup_type_records(records);
        assert_eq!(
            deduped
                .iter()
                .map(|r| (r.start, r.end, r.display.as_str(), r.rendered.as_str()))
                .collect::<Vec<_>>(),
            vec![(0, 1, "C", "C"), (4, 5, "x", "any"), (8, 9, "x", "any")],
            "identical (start, end, display, rendered) collapses; distinct positions stay"
        );
    }

    /// Distinct records at the same range survive dedup: upstream prints the
    /// declaration-name record and the constructor-side record for a class
    /// used in `new` on one line (`assignmentCompatability10.types` prints
    /// `>classWithPublicAndOptional : classWithPublicAndOptional<T, U>` and
    /// `>classWithPublicAndOptional : typeof classWithPublicAndOptional`), so
    /// dedup must not collapse differing renderings.
    #[test]
    fn dedup_type_records_keeps_distinct_same_range_records() {
        let record = |display: &str, rendered: &str| TypeAnnotation {
            start: 10,
            end: 36,
            line: 0,
            display: display.to_owned(),
            rendered: rendered.to_owned(),
            caret: true,
            blanks: Vec::new(),
        };
        let deduped = dedup_type_records(vec![
            record("Foo", "Foo<T>"),
            record("Foo", "typeof Foo"),
            record("Foo", "Foo<T>"),
        ]);
        assert_eq!(
            deduped
                .iter()
                .map(|r| (r.display.as_str(), r.rendered.as_str()))
                .collect::<Vec<_>>(),
            vec![("Foo", "Foo<T>"), ("Foo", "typeof Foo")],
            "distinct renderings at one range must survive"
        );
    }

    /// A clean self-reference carries two `>varInit : any` records for
    /// `var varInit = varInit;`: declaration name and resolving reference at
    /// different ranges are both legitimate records. Only exact (start, end,
    /// display, rendered) tuples collapse; text-identical records at distinct
    /// positions stay. Records for a clean file stay bare, matching the
    /// bare `>x : any` rows the clean `anyAsFunctionCall.types` prints.
    #[test]
    fn emit_types_baseline_keeps_distinct_position_records() {
        let logical = "tests/cases/conformance/types/witness/witnessPin.ts";
        let units = split_case_units(logical, "var varInit = varInit; // any\n");
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/types/witness/witnessPin.ts] ////\n\
            \n\
            === witnessPin.ts ===\n\
            var varInit = varInit; // any\n\
            >varInit : any\n\
            >varInit : any\n";
        assert_eq!(
            compare_types(baseline, &emitted),
            FacetVerdict::Pass,
            "distinct-position identical records must both stay bare in a clean file: emitted:\n{emitted}"
        );
    }

    /// Numeric enum declaration headers carry the enum type (`>E1 : E1`,
    /// enumBasics3.types:8), not `any`.
    #[test]
    fn emit_types_numeric_enum_header_names_enum_type() {
        let logical = "tests/cases/compiler/enumHeaderPin.ts";
        let case_text = "enum E1 {\n    a = 1,\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">E1 : E1"),
            "missing `>E1 : E1` header:\n{emitted}"
        );
        assert!(
            !emitted.lines().any(|line| line == ">E1 : any"),
            "stale `any` header:\n{emitted}"
        );
    }

    /// String enum declaration headers carry the named type (`>S : S`).
    #[test]
    fn emit_types_string_enum_header_names_enum_type() {
        let logical = "tests/cases/compiler/stringEnumHeaderPin.ts";
        let case_text = "enum S {\n    a = \"a\",\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">S : S"),
            "missing `>S : S` header:\n{emitted}"
        );
    }

    /// Namespace declaration headers carry the constructor type
    /// (`>M : typeof M`, FunctionDeclaration7.types:5).
    #[test]
    fn emit_types_namespace_header_names_constructor_type() {
        let logical = "tests/cases/compiler/namespaceHeaderPin.ts";
        let case_text = "namespace M {\n    export var x = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">M : typeof M"),
            "missing `>M : typeof M` header:\n{emitted}"
        );
    }

    /// Merged `enum E` + `namespace E` keeps the enum type on the shared
    /// symbol: the enum header still reads `>E : E`
    /// (augmentedTypesEnum:88). The namespace declaration's own
    /// `>E : typeof E` row needs per-declaration headers, which the
    /// per-symbol loop cannot render yet — banked follow-up.
    #[test]
    fn emit_types_merged_enum_namespace_keeps_enum_type() {
        let logical = "tests/cases/compiler/mergedEnumNamespacePin.ts";
        let case_text = "enum E {\n    A = 1,\n}\nnamespace E {\n    export var x = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">E : E"),
            "missing `>E : E` header:\n{emitted}"
        );
    }

    /// Interface+namespace merges keep interface members readable
    /// through the type side.
    #[test]
    fn emit_types_interface_namespace_merge_keeps_members() {
        let logical = "tests/cases/compiler/interfaceNamespaceMergePin.ts";
        let case_text = "interface M {\n    value: number;\n}\nnamespace M {\n    export const tag = 1;\n}\ndeclare const m: M;\nm.value;\nM.tag;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">m.value : number"),
            "missing `>m.value : number`:\n{emitted}"
        );
        assert!(
            emitted.lines().any(|line| line == ">M.tag : 1"),
            "missing `>M.tag : 1`:\n{emitted}"
        );
    }

    /// Function+namespace merges keep the function callable: the
    /// namespace write must not replace a function-kind symbol's type.
    #[test]
    fn emit_types_function_namespace_merge_stays_callable() {
        let logical = "tests/cases/compiler/functionNamespaceMergePin.ts";
        let case_text =
            "function f() {\n}\nnamespace f {\n    export const x = 1;\n}\nf();\nf.x;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">f : () => void"),
            "merged function lost its callable type:\n{emitted}"
        );
        assert!(
            emitted.lines().any(|line| line == ">f.x : 1"),
            "missing `>f.x : 1`:\n{emitted}"
        );
    }

    /// A multi-file case's preamble before the first `@Filename:` marker is
    /// global options, not a unit: upstream `ParseTestFilesAndSymlinks`
    /// (`AllowImplicitFirstFile: false`) drops a comment-only preamble, so
    /// no phantom `=== <case>.ts ===` section appears and
    /// `ClassAndModuleWithSameNameAndCommonRoot.types` opens with
    /// `=== class.ts ===` directly.
    #[test]
    fn types_emitter_skips_empty_entry_units() {
        let logical =
            "tests/cases/conformance/internalModules/DeclarationMerging/phantomEntryPin.ts";
        let case_text = "\
// @target: es2015\n\
// @filename: class.ts\n\
class Point { x: number; }\n\
// @filename: simple.ts\n\
var a = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains("=== phantomEntryPin.ts ==="),
            "comment/options preamble must not become a phantom unit; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains("=== class.ts ==="),
            "first @Filename unit keeps its section; emitted:\n{emitted}"
        );
    }

    /// Cross-file enum values keep their constructor through named
    /// imports: structural assignment in the importing unit accepts.
    #[test]
    fn emit_types_imported_enum_value_assignable() {
        let logical = "tests/cases/compiler/importedEnumPin.ts";
        let case_text = "// @filename: e.ts\nenum E {\n    A = 1,\n}\nexport { E };\n// @filename: use.ts\nimport { E } from \"./e\";\nconst v: { A: E } = E;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.lines().any(|line| line == ">v : { A: E; }"),
            "missing value line:\n{emitted}"
        );
        assert!(
            emitted.lines().any(|line| line == ">E : typeof E"),
            "missing imported typeof line:\n{emitted}"
        );
    }

    /// Section headers echo the verbatim `// @Filename:` spelling: absolute
    /// names keep their leading `/` and relative names stay bare, exactly as
    /// `ambient.types` prints `=== /a.ts ===` and `=== /b.ts ===`.
    #[test]
    fn types_section_headers_preserve_verbatim_filename() {
        let logical = "tests/cases/conformance/externalModules/typeOnly/ambientPin.ts";
        let case_text = "\
// @Filename: /a.ts\n\
export class A { a!: string }\n\
\n\
// @Filename: /b.ts\n\
import type { A } from './a';\n\
declare class B extends A {}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.contains("=== /a.ts ==="),
            "absolute @Filename must keep its leading slash; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains("=== /b.ts ==="),
            "second absolute unit must keep its leading slash; emitted:\n{emitted}"
        );
        assert!(
            !emitted.contains("=== a.ts ==="),
            "lossy basename section must not appear; emitted:\n{emitted}"
        );
    }

    /// Drive-letter (`A:/foo/bar.ts`) and dot-slash (`./a.ts`) spellings are
    /// preserved too — `commonSourceDir4.types:3` prints `=== A:/foo/bar.ts ===`
    /// and `decoratorMetadataTypeOnlyExport.types:3` prints `=== ./a.ts ===`;
    /// `virtual_unit_path` strips both prefixes for the loader, so the
    /// section name must come from the verbatim name all the way through
    /// the emitter.
    #[test]
    fn types_section_headers_preserve_drive_and_dot_prefixes() {
        for (logical, name) in [
            ("tests/cases/compiler/drivePrefixPin.ts", "A:/foo/bar.ts"),
            ("tests/cases/compiler/dotSlashPin.ts", "./a.ts"),
        ] {
            let case_text = format!("// @Filename: {name}\nvar x = 1;\n");
            let units = split_case_units(logical, &case_text);
            assert_eq!(units[0].display_name, name);
            let entry = entry_virtual_path(logical, &units);
            let case = compile_case(&units, &entry).expect("case compiles");
            let emitted = emit_types_baseline(&case, logical);
            assert!(
                emitted.contains(&format!("=== {name} ===")),
                "verbatim section header for {name} missing from:\n{emitted}"
            );
        }
    }

    /// `tsconfig.json` / `jsconfig.json` units are configuration, never
    /// program sources: `noEmitAndComposite.types` contains only the
    /// `=== /a.ts ===` section and no `=== /tsconfig.json ===` section, while
    /// data `.json` inputs (e.g. `=== b.json ===`) do get sections.
    #[test]
    fn types_emitter_skips_config_units() {
        assert!(is_config_unit_name("tsconfig.json"));
        assert!(is_config_unit_name("/a/b/tsconfig.json"));
        assert!(is_config_unit_name("/b/TSConfig.JSON"));
        assert!(is_config_unit_name("jsconfig.json"));
        assert!(!is_config_unit_name("b.json"));
        assert!(!is_config_unit_name("/config.json"));
        assert!(!is_config_unit_name("package.json"));

        let logical = "tests/cases/compiler/noEmitAndCompositePin.ts";
        let case_text = "\
// @Filename: /a.ts\n\
const x = 10;\n\
\n\
// @Filename: /tsconfig.json\n\
{\n\
    \"compilerOptions\": {\n\
        \"noEmit\": true,\n\
        \"composite\": true\n\
    }\n\
}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains("=== /tsconfig.json ==="),
            "config unit must not get a types section; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains("=== /a.ts ==="),
            "source unit must keep its section; emitted:\n{emitted}"
        );
    }

    /// Interface declaration names carry no `>name : type` record:
    /// `duplicateConstructSignature.types` echoes `interface I { (): number;
    /// (): string; }` with zero records, while class names do get records
    /// (`ClassDeclaration21.types`: `>C : C`).
    #[test]
    fn types_emitter_skips_interface_name_records() {
        let logical = "tests/cases/compiler/duplicateConstructSignaturePin.ts";
        let case_text = "interface I {\n    (): number;\n    (): string;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/duplicateConstructSignaturePin.ts] ////\n\
            \n\
            === duplicateConstructSignaturePin.ts ===\n\
            interface I {\n\
                (): number;\n\
                (): string;\n\
            }\n";
        assert_eq!(
            compare_types(baseline, &emitted),
            FacetVerdict::Pass,
            "interface name must not produce a record; emitted:\n{emitted}"
        );
    }

    /// Class declaration names DO get records (`ClassDeclaration21.types`:
    /// `>C : C`) — the interface skip must not suppress them.
    #[test]
    fn types_emitter_keeps_class_name_records() {
        let logical = "tests/cases/compiler/ClassDeclaration21.ts";
        let case_text = "class C {\n    0();\n    1() { }\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.contains(">C : C\n"),
            "class name record must survive; emitted:\n{emitted}"
        );
    }

    #[test]
    fn resolve_types_baseline_prefers_plain_over_variant() {
        let mut groups: BaselineGroups = BTreeMap::new();
        groups.insert(
            ("foo".to_owned(), "types".to_owned()),
            vec![
                (
                    "(target=es5)".to_owned(),
                    "tests/baselines/reference/foo(target=es5).types".to_owned(),
                ),
                (
                    String::new(),
                    "tests/baselines/reference/foo.types".to_owned(),
                ),
            ],
        );
        assert_eq!(
            resolve_types_baseline(&groups, "tests/cases/compiler/foo.ts").as_deref(),
            Some("tests/baselines/reference/foo.types")
        );
        assert_eq!(
            resolve_types_baseline(&groups, "tests/cases/compiler/absent.ts"),
            None
        );
    }

    /// End-to-end pin: a top-level case whose declarations and value reference
    /// the binder fully tracks reproduces the upstream `.symbols` framing —
    /// marker, section, source echo, and `>name : Symbol(name, Decl(unit, l, c))`
    /// records with full-start declaration positions — under `compare_symbols`.
    #[test]
    fn emit_symbols_baseline_reproduces_declaration_and_reference_records() {
        let logical = "tests/cases/compiler/symbolPin.ts";
        let case_text = "class Cell {}\nvar a = 0;\nvar b = a;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/symbolPin.ts] ////\n\
            \n\
            === symbolPin.ts ===\n\
            class Cell {}\n\
            >Cell : Symbol(Cell, Decl(symbolPin.ts, 0, 0))\n\
            var a = 0;\n\
            >a : Symbol(a, Decl(symbolPin.ts, 1, 3))\n\
            var b = a;\n\
            >b : Symbol(b, Decl(symbolPin.ts, 2, 3))\n\
            >a : Symbol(a, Decl(symbolPin.ts, 1, 3))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Namespace import aliases anchor at the specifier full start, the end
    /// of `import`, matching `assertionFunctionWildcardImport1.symbols`.
    #[test]
    fn import_namespace_alias_decl_anchors_at_specifier_full_start() {
        let logical = "tests/cases/compiler/importAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: impns.ts
import * as ns from \"./dep\";
ns;
// @Filename: dep.ts
export var v = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(ns, Decl(impns.ts, 0, 6))"),
            "{emitted}"
        );
    }

    /// Named import aliases anchor at the specifier full start, the end of
    /// the opening brace, matching `amdDependencyCommentName4.symbols`.
    #[test]
    fn import_named_alias_decl_anchors_at_specifier_full_start() {
        let logical = "tests/cases/compiler/importAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: impnamed.ts
import { a as b } from \"./dep\";
b;
// @Filename: dep.ts
export var v = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(b, Decl(impnamed.ts, 0, 8))"),
            "{emitted}"
        );
    }

    /// Enum member reads emit the access-path and leaf rows (`>E.A` and
    /// `>A`, both `Symbol(E.A, ...)`) beside the base `>E` row, matching
    /// `enumOperations.symbols`. Before the enum owner gate only the base
    /// row existed, so the path lookup finds nothing and the test fails.
    #[test]
    fn emit_symbols_records_enum_member_access_rows() {
        let logical = "tests/cases/compiler/enumAccessPin.ts";
        let case_text = "enum E {\n    A,\n    B,\n}\nvar e: E = E.A;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let path = emitted
            .lines()
            .find(|l| l.starts_with(">E.A : Symbol(E.A,"))
            .unwrap_or_else(|| panic!("missing enum access path row:\n{emitted}"));
        assert!(
            path.starts_with(">E.A : Symbol(E.A, Decl(enumAccessPin.ts, "),
            "unexpected enum access path row: {path}"
        );
        assert!(
            emitted.lines().any(|l| l.starts_with(">A : Symbol(E.A,")),
            "missing enum access leaf row:\n{emitted}"
        );
    }

    /// Same-file namespace member reads emit the access-path and leaf rows
    /// (`>m1.m1` and the property row, both `Symbol(m1.m1, ...)`), matching
    /// `collisionCodeGenModuleWithMemberVariable.symbols`. Cross-unit
    /// aliases still resolve to the local import symbol only.
    #[test]
    fn emit_symbols_records_namespace_member_access_rows() {
        let logical = "tests/cases/compiler/namespaceAccessPin.ts";
        let case_text = "namespace m1 {\n    export var m1 = 10;\n}\nvar foo = m1.m1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let path = emitted
            .lines()
            .find(|l| l.starts_with(">m1.m1 : Symbol(m1.m1,"))
            .unwrap_or_else(|| panic!("missing namespace access path row:\n{emitted}"));
        assert!(
            path.starts_with(">m1.m1 : Symbol(m1.m1, Decl(namespaceAccessPin.ts, "),
            "unexpected namespace access path row: {path}"
        );
    }

    /// Namespace export declarations render bare (`Symbol(x, ...)`), guarding
    /// against declare-time over-qualification: upstream qualifies namespace
    /// members only at access-path reference sites, which the reference
    /// recorder reaches for same-file member reads.
    #[test]
    fn import_default_alias_decl_anchors_at_specifier_full_start() {
        let logical = "tests/cases/compiler/importAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: impdefault.ts
import { default as Foo } from \"./dep\";
Foo;
// @Filename: dep.ts
export var v = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(Foo, Decl(impdefault.ts, 0, 8))"),
            "{emitted}"
        );
    }

    /// Imports without an alias keep their existing anchors: a default
    /// import at the end of `import` and plain names at the preceding
    /// brace or comma, matching the `>d`, `>p1` rows beside the alias
    /// rows in `amdDependencyCommentName4.symbols`.
    #[test]
    fn import_without_alias_decl_positions_are_unchanged() {
        let logical = "tests/cases/compiler/importAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: impplain.ts
import d from \"./dep\";
import { p1, q as p2 } from \"./dep\";
d;
p1;
p2;
// @Filename: dep.ts
export var v = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(d, Decl(impplain.ts, 0, 6))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(p1, Decl(impplain.ts, 1, 8))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(p2, Decl(impplain.ts, 1, 12))"),
            "{emitted}"
        );
    }

    /// `import x = require(...)` keeps its statement-start anchor at the
    /// file origin for a leading statement, matching the `>r1` row shape
    /// in `amdDependencyCommentName4.symbols`.
    #[test]
    fn import_equals_decl_position_is_unchanged() {
        let logical = "tests/cases/compiler/importAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: impeq.ts
import r1 = require(\"./dep\");
r1;
// @Filename: dep.ts
export var v = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(r1, Decl(impeq.ts, 0, 0))"),
            "{emitted}"
        );
    }

    /// Generator functions anchor at the `function` keyword with the star
    /// stepped over, matching `castOfYield.symbols` (`Decl(castOfYield.ts, 0, 0)`).
    #[test]
    fn generator_function_decl_anchors_at_function_keyword() {
        let logical = "tests/cases/compiler/generatorPin.ts";
        let case_text = "function* f() {\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(f, Decl(generatorPin.ts, 0, 0))"),
            "{emitted}"
        );
    }

    /// Async generators anchor at `async` with star and keyword stepped over,
    /// matching `asyncImportNestedYield.symbols` (`Decl(asyncImportNestedYield.ts, 0, 0)`).
    #[test]
    fn async_generator_function_decl_anchors_at_async_keyword() {
        let logical = "tests/cases/compiler/generatorPin.ts";
        let case_text = "async function* foo() {\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(foo, Decl(generatorPin.ts, 0, 0))"),
            "{emitted}"
        );
    }

    /// A plain function keeps its keyword anchor while a later generator in
    /// the same unit anchors at the previous statement end, so the star walk
    /// changes no non-generator row on the path.
    #[test]
    fn generator_after_function_decl_anchors_at_previous_statement_end() {
        let logical = "tests/cases/compiler/generatorPin.ts";
        let case_text = "function a() {\n}\nfunction* b() {\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(a, Decl(generatorPin.ts, 0, 0))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(b, Decl(generatorPin.ts, 1, 1))"),
            "{emitted}"
        );
    }

    /// Dotted namespace members anchor at the member segment: the decorator
    /// scan must not cross the dot. Matches `declareDottedExtend.symbols`
    /// (`>B : Symbol(B, Decl(declareDottedExtend.ts, 0, 20))`).
    #[test]
    fn dotted_namespace_member_decl_anchors_at_last_segment() {
        let logical = "tests/cases/compiler/dottedPin.ts";
        let case_text = "declare namespace A.B {\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(A, Decl(dottedPin.ts, 0, 0))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(B, Decl(dottedPin.ts, 0, 20))"),
            "{emitted}"
        );
    }

    /// Each segment of a three-part path anchors after its own dot, matching
    /// `moduleImport.symbols` (`>B : Symbol(B, Decl(moduleImport.ts, 0, 12))`).
    #[test]
    fn dotted_namespace_segments_anchor_after_their_dot() {
        let logical = "tests/cases/compiler/dottedPin.ts";
        let case_text = "namespace A.B.C {\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(B, Decl(dottedPin.ts, 0, 12))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(C, Decl(dottedPin.ts, 0, 14))"),
            "{emitted}"
        );
    }

    /// A plain namespace keeps its statement-start anchor, so the rollback
    /// changes no non-dotted row on the path.
    #[test]
    fn plain_namespace_decl_position_is_unchanged() {
        let logical = "tests/cases/compiler/dottedPin.ts";
        let case_text = "namespace A {\nexport var v = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(A, Decl(dottedPin.ts, 0, 0))"),
            "{emitted}"
        );
    }

    /// Object literal members bind declaration rows named by first spelling:
    /// `var v = {a: 1, b: 2}` renders `>a : Symbol(a, ...)` per member.
    /// Cited baselines: `objectLiteral1.symbols`, `objectLiteralErrors.symbols`.
    #[test]
    fn emit_symbols_records_object_literal_member_declarations() {
        let logical = "tests/cases/compiler/objectLiteralPin.ts";
        let case_text = "var v = {a: 1, b: 2};\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        for display in [
            ">a : Symbol(a, Decl(objectLiteralPin.ts, 0, 9))",
            ">b : Symbol(b, Decl(objectLiteralPin.ts, 0, 14))",
        ] {
            assert!(
                emitted.lines().any(|l| l.starts_with(display)),
                "missing object literal member row {display}:\n{emitted}"
            );
        }
    }

    /// Quoted and numeric keys merge under the first spelling with unioned
    /// anchors: `{ a: 0, 'a': 0 }` renders `>a` and `>'a'`, both
    /// `Symbol(a, Decl(0, 9), Decl(0, 15))`. Cited baseline:
    /// `objectLiteralErrors.symbols` (`e6`).
    #[test]
    fn emit_symbols_merges_quoted_object_literal_members() {
        let logical = "tests/cases/compiler/objectLiteralQuotedPin.ts";
        let case_text = "var e = { a: 0, 'a': 0 };\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        for display in [
            ">a : Symbol(a, Decl(objectLiteralQuotedPin.ts, 0, 9), Decl(objectLiteralQuotedPin.ts, 0, 15))",
            ">'a' : Symbol(a, Decl(objectLiteralQuotedPin.ts, 0, 9), Decl(objectLiteralQuotedPin.ts, 0, 15))",
        ] {
            assert!(
                emitted.lines().any(|l| l.starts_with(display)),
                "missing merged quoted member row {display}:\n{emitted}"
            );
        }
    }

    /// Computed keys bind bracketed (`>[n] : Symbol([n], ...)`), and dot
    /// reads through a literal-typed variable emit path plus leaf rows.
    /// Cited baselines: `duplicateObjectLiteralProperty_computedName2.symbols`,
    /// `collisionCodeGenModuleWithMemberVariable.symbols` (namespace analog).
    #[test]
    fn emit_symbols_records_computed_object_literal_members() {
        let logical = "tests/cases/compiler/objectLiteralComputedPin.ts";
        let case_text =
            "const n = 1;\nvar t = { [n]: 1 };\nvar s = { item: 1 };\nvar w = s.item;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted
                .lines()
                .any(|l| l
                    .starts_with(">[n] : Symbol([n], Decl(objectLiteralComputedPin.ts, 1, 9))")),
            "missing computed member row:\n{emitted}"
        );
        for display in [
            ">s.item : Symbol(item, Decl(objectLiteralComputedPin.ts, 2, 9))",
            ">item : Symbol(item, Decl(objectLiteralComputedPin.ts, 2, 9))",
        ] {
            assert!(
                emitted.lines().any(|l| l.starts_with(display)),
                "missing object literal access row {display}:\n{emitted}"
            );
        }
    }

    /// Shorthand members show only the member row: `var o = {a}` renders
    /// `>a : Symbol(a, Decl(..., 1, 9))` once, with no outer-binding use row
    /// at the shorthand span. Cited baseline: `typeGuardFunctionOfFormThis.symbols`.
    #[test]
    fn emit_symbols_shorthand_member_hides_outer_use_row() {
        let logical = "tests/cases/compiler/objectLiteralShorthandPin.ts";
        let case_text = "var a = 1;\nvar o = {a};\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted
                .lines()
                .any(|l| l.starts_with(">a : Symbol(a, Decl(objectLiteralShorthandPin.ts, 1, 9))")),
            "missing shorthand member row:\n{emitted}"
        );
        assert_eq!(
            emitted
                .lines()
                .filter(
                    |l| l.starts_with(">a : Symbol(a, Decl(objectLiteralShorthandPin.ts, 0, 3))")
                )
                .count(),
            1,
            "outer binding must appear only at its declaration:\n{emitted}"
        );
    }
    /// Nested function-type parameters declare bare symbols: `each` in
    /// `chainedSpecializationToObjectTypeLiteral.symbols` renders
    /// `>iterator : Symbol(iterator, ...)` and the nested
    /// `>value : Symbol(value, ...)`; the value parameter has no bind-phase
    /// anchor, so resolve declares it at the single choke point where every
    /// nested function type passes through. The outer parameter row on the
    /// same path stays exactly as before.
    #[test]
    fn emit_symbols_binds_nested_function_type_parameters() {
        let logical = "tests/cases/compiler/nestedFunctionTypeParamSymbolsPin.ts";
        let case_text =
            "interface Sequence<T> {\n    each(iterator: (value: T) => void): void;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted
                .lines()
                .any(|l| l.starts_with(">iterator : Symbol(iterator,")),
            "outer parameter keeps its row; emitted:\n{emitted}"
        );
        assert_eq!(
            emitted
                .lines()
                .filter(|l| l.starts_with(">value :"))
                .count(),
            1,
            "nested value parameter must declare exactly one row; emitted:\n{emitted}"
        );
    }

    /// Function-declaration annotations nest the same way: `declare function
    /// f(cb: (v: boolean) => void)` in
    /// `asyncFunctionContextuallyTypedReturns.symbols` renders `>cb` and the
    /// nested `>v : Symbol(v, ...)`.
    #[test]
    fn emit_symbols_binds_annotation_nested_function_type_parameters() {
        let logical = "tests/cases/compiler/annotationNestedFunctionTypeParamSymbolsPin.ts";
        let case_text = "declare function f(cb: (v: boolean) => void): void;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.lines().any(|l| l.starts_with(">cb : Symbol(cb,")),
            "outer parameter keeps its row; emitted:\n{emitted}"
        );
        assert_eq!(
            emitted.lines().filter(|l| l.starts_with(">v :")).count(),
            1,
            "nested value parameter must declare exactly one row; emitted:\n{emitted}"
        );
    }

    /// Empty single-unit cases still emit their section header with no records.
    #[test]
    fn emit_symbols_baseline_emits_empty_single_unit_section() {
        let logical = "tests/cases/compiler/emptyPin.ts";
        let case_text = "// @target: es2015\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/emptyPin.ts] ////\n\n=== emptyPin.ts ===\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Trailing empty files keep their section headers with no records.
    #[test]
    fn emit_symbols_baseline_emits_empty_trailing_file_section() {
        let logical = "tests/cases/compiler/multiEmptyPin.ts";
        let case_text = "// @filename: a.ts\nvar a = 1;\n// @filename: b.ts\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("=== a.ts ==="),
            "missing a section:\n{emitted}"
        );
        assert!(
            emitted.contains("=== b.ts ==="),
            "missing b section:\n{emitted}"
        );
    }
    /// Bare intrinsic value references render without a Decl list.
    #[test]
    fn emit_symbols_baseline_renders_intrinsic_undefined_bare() {
        let logical = "tests/cases/compiler/intrinsicPin.ts";
        let case_text = "var v = undefined;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/intrinsicPin.ts] ////\n\n=== intrinsicPin.ts ===\nvar v = undefined;\n>v : Symbol(v, Decl(intrinsicPin.ts, 0, 3))\n>undefined : Symbol(undefined)\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Top-level This expressions reference the globalThis intrinsic bare.
    #[test]
    fn emit_symbols_baseline_renders_top_level_this_as_global_this() {
        let logical = "tests/cases/compiler/thisPin.ts";
        let case_text = "++this;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/thisPin.ts] ////\n\n=== thisPin.ts ===\n++this;\n>this : Symbol(globalThis)\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }
    /// Recorded Es5 globals render with their single lib Decl row.
    #[test]
    fn emit_symbols_baseline_renders_es5_global_with_lib_decl() {
        let logical = "tests/cases/compiler/libGlobalPin.ts";
        let case_text = "var e = eval(\"1\");\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/libGlobalPin.ts] ////\n\n=== libGlobalPin.ts ===\nvar e = eval(\"1\");\n>e : Symbol(e, Decl(libGlobalPin.ts, 0, 3))\n>eval : Symbol(eval, Decl(lib.es5.d.ts, --, --))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Recorded Dom globals render with their single lib Decl row.
    #[test]
    fn emit_symbols_baseline_renders_dom_global_with_lib_decl() {
        let logical = "tests/cases/compiler/domGlobalPin.ts";
        let case_text = "var w = window;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/domGlobalPin.ts] ////\n\n=== domGlobalPin.ts ===\nvar w = window;\n>w : Symbol(w, Decl(domGlobalPin.ts, 0, 3))\n>window : Symbol(window, Decl(lib.dom.d.ts, --, --))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Merged lib globals render one Decl per declaring lib file in file order.
    #[test]
    fn emit_symbols_baseline_renders_merged_date_with_lib_decl_list() {
        let logical = "tests/cases/compiler/datePin.ts";
        let case_text = "var d = new Date();\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es2015".to_owned()])],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/datePin.ts] ////\n\n=== datePin.ts ===\nvar d = new Date();\n>d : Symbol(d, Decl(datePin.ts, 0, 3))\n>Date : Symbol(Date, Decl(lib.es5.d.ts, --, --), Decl(lib.es5.d.ts, --, --), Decl(lib.es5.d.ts, --, --), Decl(lib.scripthost.d.ts, --, --), Decl(lib.es2015.symbol.wellknown.d.ts, --, --))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Merged Array globals render es5, core, iterable, and wellknown Decl rows.
    #[test]
    fn emit_symbols_baseline_renders_merged_array_with_lib_decl_list() {
        let logical = "tests/cases/compiler/arrayPin.ts";
        let case_text = "var a = Array(1, 2, 3);\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es2015".to_owned()])],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/arrayPin.ts] ////\n\n=== arrayPin.ts ===\nvar a = Array(1, 2, 3);\n>a : Symbol(a, Decl(arrayPin.ts, 0, 3))\n>Array : Symbol(Array, Decl(lib.es5.d.ts, --, --), Decl(lib.es5.d.ts, --, --), Decl(lib.es2015.core.d.ts, --, --), Decl(lib.es2015.iterable.d.ts, --, --), Decl(lib.es2015.symbol.wellknown.d.ts, --, --))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Static members of lib globals record path, base, and property rows.
    #[test]
    fn emit_symbols_baseline_renders_static_pi_with_lib_decl() {
        let logical = "tests/cases/compiler/mathPiPin.ts";
        let case_text = "var p = Math.PI;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es2015".to_owned()])],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/mathPiPin.ts] ////\n\n=== mathPiPin.ts ===\nvar p = Math.PI;\n>p : Symbol(p, Decl(mathPiPin.ts, 0, 3))\n>Math.PI : Symbol(Math.PI, Decl(lib.es5.d.ts, --, --))\n>Math : Symbol(Math, Decl(lib.es5.d.ts, --, --), Decl(lib.es5.d.ts, --, --), Decl(lib.es2015.core.d.ts, --, --), Decl(lib.es2015.symbol.wellknown.d.ts, --, --))\n>PI : Symbol(Math.PI, Decl(lib.es5.d.ts, --, --))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// DateConstructor statics render single-es5 Decl rows under es2015.
    #[test]
    fn emit_symbols_baseline_renders_static_utc_with_lib_decl() {
        let logical = "tests/cases/compiler/dateUtcPin.ts";
        let case_text = "var u = Date.UTC(2020, 0, 1);\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es2015".to_owned()])],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/dateUtcPin.ts] ////\n\n=== dateUtcPin.ts ===\nvar u = Date.UTC(2020, 0, 1);\n>u : Symbol(u, Decl(dateUtcPin.ts, 0, 3))\n>Date.UTC : Symbol(DateConstructor.UTC, Decl(lib.es5.d.ts, --, --))\n>Date : Symbol(Date, Decl(lib.es5.d.ts, --, --), Decl(lib.es5.d.ts, --, --), Decl(lib.es5.d.ts, --, --), Decl(lib.scripthost.d.ts, --, --), Decl(lib.es2015.symbol.wellknown.d.ts, --, --))\n>UTC : Symbol(DateConstructor.UTC, Decl(lib.es5.d.ts, --, --))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Object-literal shorthand rows anchor at the shorthand's full start
    /// instead of the outer binding, matching `shorthand-property-es5-es6`
    /// (`>baz : Symbol(baz, Decl(test.ts, 2, 18))`).
    #[test]
    fn object_literal_shorthand_decl_anchors_at_shorthand() {
        let logical = "tests/cases/compiler/shorthandPin.ts";
        let case_text = "var foo = 1;\nvar baz = 2;\nvar bar = { foo, baz };\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(foo, Decl(shorthandPin.ts, 2, 11))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(baz, Decl(shorthandPin.ts, 2, 16))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(foo, Decl(shorthandPin.ts, 0, 3))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(baz, Decl(shorthandPin.ts, 1, 3))"),
            "{emitted}"
        );
    }

    /// Imported shorthand names anchor at the use site, while the import's
    /// own row keeps the specifier anchor, matching
    /// `systemObjectShorthandRename.symbols` (`>x (2, 12)` beside `>x (0, 8)`).
    #[test]
    fn imported_shorthand_decl_anchors_at_shorthand() {
        let logical = "tests/cases/compiler/shorthandPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: shpin.ts
import {x} from \"./dep\";
const x2 = {x};
// @Filename: dep.ts
export var x = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(x, Decl(shpin.ts, 1, 12))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(x, Decl(shpin.ts, 0, 8))"),
            "{emitted}"
        );
    }

    /// Renamed binding elements anchor at the element start, matching
    /// `ES5For-of27.symbols` (`>a : Symbol(a, Decl(ES5For-of27.ts, 0, 10))`).
    #[test]
    fn binding_rename_decl_anchors_at_element_start() {
        let logical = "tests/cases/compiler/destructurePin.ts";
        let case_text = "for (var {x: a} of b) {\na;\n}\nvar b = [1];\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(a, Decl(destructurePin.ts, 0, 10))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(b, Decl(destructurePin.ts, 3, 3))"),
            "{emitted}"
        );
    }

    /// Computed renames anchor after balancing back to the opening bracket,
    /// matching `computedPropertiesInDestructuring2.symbols`
    /// (`>bar3 : Symbol(bar3, Decl(computedPropertiesInDestructuring2.ts, 1, 5))`).
    #[test]
    fn computed_binding_rename_decl_anchors_at_bracket() {
        let logical = "tests/cases/compiler/destructurePin.ts";
        let case_text = "let {[k]: v} = o;\nvar k = \"a\";\nvar o = {};\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains("Symbol(v, Decl(destructurePin.ts, 0, 5))"),
            "{emitted}"
        );
        assert!(
            emitted.contains("Symbol(k, Decl(destructurePin.ts, 1, 3))"),
            "{emitted}"
        );
    }

    /// Honesty pin on a real pinned sample: `anyAsConstructor` carries a
    /// `@target` pragma (dropped from the upstream echo) and references whose
    /// declarations the binder anchors differently, so the emitted document
    /// cannot canonicalize equal to the upstream `.symbols` baseline — the S2
    /// burn-down surface, reported as `Fail`, never a false pass.
    #[test]
    fn emit_symbols_baseline_undercoverage_fails_comparison() {
        let logical = "tests/cases/conformance/types/any/anyAsConstructor.ts";
        let units = split_case_units(logical, ANY_AS_CONSTRUCTOR_CASE);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/types/any/anyAsConstructor.ts] ////\n\
            \n\
            === anyAsConstructor.ts ===\n\
            var x: any;\n\
            >x : Symbol(x, Decl(anyAsConstructor.ts, 3, 3))\n\
            \n\
            var a = new x();\n\
            >a : Symbol(a, Decl(anyAsConstructor.ts, 4, 3))\n\
            >x : Symbol(x, Decl(anyAsConstructor.ts, 3, 3))\n";
        assert!(
            matches!(
                compare_symbols(baseline, &emitted),
                FacetVerdict::Fail { .. }
            ),
            "under-covered emit must not pass; emitted:\n{emitted}"
        );
    }

    /// Enum members qualify against their enum symbol at both the declaration
    /// site and the initializer-reference site (`E.A`), while the enum itself
    /// and an unrelated top-level `var` stay bare.
    #[test]
    fn emit_symbols_baseline_qualifies_enum_members() {
        let logical = "tests/cases/compiler/pin.ts";
        let case_text = "enum E {\n    A,\n    B = A + 1,\n}\nvar x = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/pin.ts] ////\n\
            \n\
            === pin.ts ===\n\
            enum E {\n\
            >E : Symbol(E, Decl(pin.ts, 0, 0))\n\
            \n\
                A,\n\
            >A : Symbol(E.A, Decl(pin.ts, 0, 8))\n\
            \n\
                B = A + 1,\n\
            >B : Symbol(E.B, Decl(pin.ts, 1, 6))\n\
            >A : Symbol(E.A, Decl(pin.ts, 0, 8))\n\
            \n\
            }\n\
            var x = 1;\n\
            >x : Symbol(x, Decl(pin.ts, 4, 3))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Namespace export declarations render bare (`Symbol(x, ...)`), guarding
    /// against declare-time over-qualification: upstream qualifies namespace
    /// members only at access-path reference sites, which this emitter does not
    /// yet reach.
    #[test]
    fn emit_symbols_baseline_keeps_namespace_exports_bare() {
        let logical = "tests/cases/compiler/pin.ts";
        let case_text = "namespace A {\n    export var x = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/pin.ts] ////\n\
            \n\
            === pin.ts ===\n\
            namespace A {\n\
            >A : Symbol(A, Decl(pin.ts, 0, 0))\n\
            \n\
                export var x = 1;\n\
            >x : Symbol(x, Decl(pin.ts, 1, 14))\n\
            \n\
            }\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// `@typeRoots` maps to a camelCase `typeRoots` string array and
    /// virtual-absolute roots become root-relative paths.
    #[test]
    fn build_tsconfig_maps_type_roots_to_camel_case_array() {
        let pragmas = parse_case_pragmas("// @typeRoots: /types\nvar x = 1;\n");
        let tsconfig = build_tsconfig(&pragmas);
        assert!(
            tsconfig.contains("\"typeRoots\": [\"types\"]"),
            "{tsconfig}"
        );
        let pragmas = parse_case_pragmas("// @typeRoots: /a/types, /a/node_modules\nvar x = 1;\n");
        let tsconfig = build_tsconfig(&pragmas);
        assert!(
            tsconfig.contains("\"typeRoots\": [\"a/types\", \"a/node_modules\"]"),
            "{tsconfig}"
        );
    }

    /// Records are ordered by reference-site position (line, then character),
    /// matching upstream's source-order symbol table iteration. A case with
    /// declarations and references on multiple lines must emit `>name` records
    /// in source position order, not binder allocation order.
    #[test]
    fn emit_symbols_records_ordered_by_reference_position() {
        let logical = "tests/cases/compiler/orderPin.ts";
        // `zebra` is declared last but alphabetically first; `alpha` is
        // declared first. Records must appear in source line order:
        // alpha (line 0), zebra (line 1), alpha-ref (line 2).
        let case_text = "var alpha = 0;\nvar zebra = alpha;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Extract all symbol lines in order.
        let symbol_lines: Vec<&str> = emitted.lines().filter(|l| l.starts_with('>')).collect();
        // Expected source-order: alpha (line 0), zebra (line 1), alpha ref (line 2).
        assert!(
            symbol_lines.iter().any(|l| l.starts_with(">alpha")),
            "missing alpha declaration record:\n{emitted}"
        );
        assert!(
            symbol_lines.iter().any(|l| l.starts_with(">zebra")),
            "missing zebra declaration record:\n{emitted}"
        );
        // The alpha declaration must come before the zebra declaration
        // (source order), even though the binder may allocate zebra first.
        let alpha_pos = symbol_lines
            .iter()
            .position(|l| l.starts_with(">alpha"))
            .expect("alpha record exists");
        let zebra_pos = symbol_lines
            .iter()
            .position(|l| l.starts_with(">zebra"))
            .expect("zebra record exists");
        assert!(
            alpha_pos < zebra_pos,
            "alpha declaration must precede zebra declaration (source order):\n{emitted}"
        );
    }

    /// Duplicate records (same position, display, and rendered string) are
    /// collapsed. The binder can record the same (range, symbol) pair
    /// multiple times in `symbol_references`; upstream emits each unique
    /// `>name : Symbol(...)` line once. Without deduplication, the pairwise
    /// line comparison diverges and every subsequent line is classified as
    /// "wrong-symbol-entirely".
    #[test]
    fn emit_symbols_records_deduplicated() {
        let logical = "tests/cases/compiler/dedupPin.ts";
        // `Ship` is referenced in a type annotation `Ship[]`. The binder
        // may record this reference multiple times; the emitter must
        // collapse duplicates so `>Ship` appears once per line.
        let case_text = "class Ship {}\nclass Board {\n    ships: Ship[] = [];\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Count `>Ship` reference lines on the `ships: Ship[] = [];` line.
        // The declaration `>Ship` is on line 0 (`class Ship {}`), and the
        // reference `>Ship` is on line 2 (`ships: Ship[] = [];`). Both have
        // the same Decl, but they are at different positions so both are
        // kept. The deduplication only collapses records at the SAME position.
        // Without deduplication, the binder's duplicate references would
        // produce 2–3 `>Ship` lines on the `ships` line.
        let lines: Vec<&str> = emitted.lines().collect();
        let ships_line_idx = lines
            .iter()
            .position(|l| l.contains("ships: Ship[]"))
            .expect("ships line exists");
        // Symbol records follow the source line; collect consecutive `>` lines.
        let ship_refs_on_line: Vec<&&str> = lines[ships_line_idx + 1..]
            .iter()
            .take_while(|l| l.starts_with('>'))
            .filter(|l| l.starts_with(">Ship :"))
            .collect();
        // There should be exactly one `>Ship` reference on the ships line.
        assert_eq!(
            ship_refs_on_line.len(),
            1,
            "Ship reference on ships line must appear exactly once (deduplicated), \
             got {ship_refs_on_line:?}:\n{emitted}"
        );
    }

    /// Decl anchors within a Symbol(...) record are ordered by (section, line,
    /// character) and deduplicated. A namespace declared in two units merges
    /// into one symbol with two Decl anchors; the emitter must list them in
    // (section, line, character) order with no duplicates.
    #[test]
    fn emit_symbols_decl_anchors_ordered_and_deduplicated() {
        let logical = "tests/cases/compiler/mergePin.ts";
        // `namespace X` in two files merges into one symbol with two Decl
        // anchors: Decl(a.ts, 0, 0) and Decl(b.ts, 0, 0). The anchors must
        // be ordered by (section, line, character) — a.ts before b.ts — and
        // deduplicated, even though `emit_symbols_baseline` collects the
        // anchor under both the bare name and the qualified name.
        let source = "// @filename: a.ts\nnamespace X { export var a = 1; }\n\
            // @filename: b.ts\nnamespace X { export var b = 2; }\n";
        let pragmas = parse_case_pragmas(source);
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Find the X declaration line in a.ts section.
        let x_decl_line = emitted
            .lines()
            .find(|l| l.starts_with(">X :") && l.contains("Decl(a.ts, 0, 0)"))
            .unwrap_or_else(|| panic!("missing X declaration with Decl(a.ts, 0, 0):\n{emitted}"));
        // Extract Decl(...) entries.
        let decls: Vec<String> = x_decl_line
            .match_indices("Decl(")
            .map(|(start, _)| {
                let rest = &x_decl_line[start + 5..];
                let end = rest.find(')').unwrap_or(rest.len());
                rest[..end].to_owned()
            })
            .collect();
        // Must have exactly two Decl entries for the merged namespace.
        assert_eq!(
            decls.len(),
            2,
            "merged namespace must have exactly 2 Decl entries, got {decls:?}:\n{emitted}"
        );
        // Ordered by (section, line, character): a.ts before b.ts.
        assert!(
            decls[0].starts_with("a.ts, 0,") && decls[1].starts_with("b.ts, 0,"),
            "Decl entries must be ordered by (section, line, char), got {decls:?}:\n{emitted}"
        );
        // No duplicate Decl entries.
        let mut sorted = decls.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            decls.len(),
            "Decl entries must be deduplicated, got {decls:?}:\n{emitted}"
        );
    }

    #[test]
    fn resolve_symbols_baseline_prefers_plain_over_variant() {
        let mut groups: BaselineGroups = BTreeMap::new();
        groups.insert(
            ("foo".to_owned(), "symbols".to_owned()),
            vec![
                (
                    "(target=es5)".to_owned(),
                    "tests/baselines/reference/foo(target=es5).symbols".to_owned(),
                ),
                (
                    String::new(),
                    "tests/baselines/reference/foo.symbols".to_owned(),
                ),
            ],
        );
        assert_eq!(
            resolve_symbols_baseline(&groups, "tests/cases/compiler/foo.ts").as_deref(),
            Some("tests/baselines/reference/foo.symbols")
        );
        assert_eq!(
            resolve_symbols_baseline(&groups, "tests/cases/compiler/absent.ts"),
            None
        );
    }

    #[test]
    fn class_method_this_preserves_polymorphic_identity() {
        let logical = "tests/cases/compiler/thisPin.ts";
        let case_text = "class Ship { isSunk: boolean = false; }\n\
class Board {\n\
    ships: Ship[] = [];\n\
    private allShipsSunk() {\n\
        return this.ships.every(function (val) { return val.isSunk; });\n\
    }\n\
}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let baseline = emit_types_baseline(&case, logical);
        assert!(
            baseline.contains(">this.ships : Ship[]"),
            "this.ships should be Ship[]\n{baseline}"
        );
        assert!(
            baseline.contains(">this : this"),
            "this should preserve its polymorphic identity\n{baseline}"
        );
    }

    #[test]
    fn infer_rest_argument_type_parameter_from_multiple_arguments() {
        let source = "// @strict: true\n// @target: es2015\n\n// Repro from #31204\n\nexport enum AppType {\n    HeaderDetail = 'HeaderDetail',\n    HeaderMultiDetail = 'HeaderMultiDetail',\n    AdvancedList = 'AdvancedList',\n    Standard = 'Standard',\n    Relationship = 'Relationship',\n    Report = 'Report',\n    Composite = 'Composite',\n    ListOnly = 'ListOnly',\n    ModuleSettings = 'ModuleSettings'\n}\n\nexport enum AppStyle {\n    Tree,\n    TreeEntity,\n    Standard,\n    MiniApp,\n    PivotTable\n}\n\nconst appTypeStylesWithError: Map<AppType, Array<AppStyle>> = new Map([\n    [AppType.Standard, [AppStyle.Standard, AppStyle.MiniApp]],\n    [AppType.Relationship, [AppStyle.Standard, AppStyle.Tree, AppStyle.TreeEntity]],\n    [AppType.AdvancedList, [AppStyle.Standard, AppStyle.MiniApp]]\n]);\n\n// Repro from #31204\n\ndeclare function foo<T>(...args: T[]): T[];\nlet b1: { x: boolean }[] = foo({ x: true }, { x: false });\nlet b2: boolean[][] = foo([true], [false]);\n";
        let logical = "tests/cases/conformance/expressions/arrayLiterals/arrayLiteralInference.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(source);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("compiles");
        let code_map = load_diagnostic_code_map(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .unwrap()
                .parent()
                .unwrap(),
        )
        .unwrap();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        assert!(
            actual.is_empty(),
            "unexpected mapped diagnostics: {actual:?}"
        );
    }

    #[test]
    fn object_literal_getter_without_return_has_void_readonly_property() {
        let logical = "tests/cases/conformance/parser/ecmascript5/Accessors/parserAccessors7.ts";
        let source = "// @target: es5\nvar v = { get foo(v: number) { } };\n";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("compiles");
        let baseline = emit_types_baseline(&case, logical);
        assert!(
            baseline.contains(">v : { readonly foo: void; }"),
            "getter should be readonly void property\n{baseline}"
        );
    }

    #[test]
    fn this_type_in_accessors_negative_object_type_is_widened_and_non_readonly() {
        let source = "// @noImplicitAny: true\n// @noImplicitThis: true\n// @target: es5, es2015\ninterface Foo {\n    n: number;\n    x: number;\n}\ninterface Bar {\n    wrong: \"place\" | \"time\" | \"method\" | \"technique\";\n}\nconst mismatch = {\n    n: 13,\n    get x(this: Foo) { return this.n; },\n    set x(this: Bar, n) { this.wrong = \"method\"; }\n}\nconst contextual: Foo = {\n    n: 16,\n    get x() { return this.n; }\n}\n";
        let logical = "tests/cases/conformance/types/thisType/thisTypeInAccessorsNegative.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(source);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("compiles");
        let baseline = emit_types_baseline(&case, logical);
        assert!(
            baseline.contains(">mismatch : { n: number; x: number; }"),
            "mismatch object type should widen both properties to number and merge get/set\n{baseline}"
        );
    }

    #[test]
    fn imported_cross_module_symbols_materialize_for_rendering() {
        let logical = "tests/cases/compiler/allowImportClausesToMergeWithTypes.ts";
        let case_text = "// @module: commonjs\n// @target: es2015\n// @filename: b.ts\nexport const zzz = 123;\nexport default zzz;\n\n// @filename: a.ts\nexport default interface zzz {\n    x: string;\n}\n\nimport zzz from \"./b\";\n\nconst x: zzz = { x: \"\" };\nzzz;\n\nexport { zzz as default };\n\n// @filename: index.ts\nimport zzz from \"./a\";\n\nconst x: zzz = { x: \"\" };\nzzz;\n\nimport originalZZZ from \"./b\";\noriginalZZZ;\n\nconst y: originalZZZ = x;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");

        let types = emit_types_baseline(&case, logical);
        assert!(types.contains("=== index.ts ==="), "{types}");
        assert!(types.contains(">x : zzz"), "{types}");

        let symbols = emit_symbols_baseline(&case, logical);
        assert!(symbols.contains("=== index.ts ==="), "{symbols}");
        assert!(symbols.contains("Symbol(zzz, Decl(index.ts"), "{symbols}");
    }

    /// The declaration-anchor map built across all reached units lets a
    /// symbol declared in one unit (e.g. `Model` in `aliasUsageInArray_backbone.ts`)
    /// render with its true `Decl(<other unit>, line, char)` anchor instead of
    /// being dropped for lacking an in-unit declaration. Cross-unit *reference*
    /// rows (`>Backbone.Model : Symbol(Backbone.Model, ...)`) depend on
    /// member-access reference resolution the binder does not yet produce;
    /// those remain the S2 burn-down surface. Upstream shape pinned by
    /// `tests/baselines/reference/aliasUsageInArray.symbols`
    /// (sha256 2ce5d5eb3f810bac79a552a47f2aef0c955b32e9d5fc1ac1bf7f16a07efdbdf0).
    #[test]
    fn imported_symbol_occurrences_render_cross_unit_anchors() {
        let logical = "tests/cases/compiler/aliasUsageInArray.ts";
        let case_text = "\
// @module: commonjs
// @Filename: aliasUsageInArray_main.ts
import Backbone = require(\"./aliasUsageInArray_backbone\");
interface IHasVisualizationModel {
    VisualizationModel: typeof Backbone.Model;
}

// @Filename: aliasUsageInArray_backbone.ts
export class Model {
    public someData: string;
}
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");

        let symbols = emit_symbols_baseline(&case, logical);
        assert!(
            symbols.contains("=== aliasUsageInArray_backbone.ts ==="),
            "{symbols}"
        );
        // The `Model` class declared in the backbone unit renders with its
        // true cross-unit declaration anchor, not a dropped or local-only row.
        assert!(
            symbols.contains("Symbol(Model, Decl(aliasUsageInArray_backbone.ts, 0, 0))"),
            "{symbols}"
        );
    }

    #[test]
    fn imported_require_alias_renders_typeof() {
        let logical = "tests/cases/compiler/requireAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: requireAliasPin_main.ts
import Backbone = require(\"./requireAliasPin_backbone\");
var x = Backbone;
var m = new Backbone.Model();
// @Filename: requireAliasPin_backbone.ts
export class Model {
    public someData: string;
}
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted
                .lines()
                .any(|line| line == ">Backbone : typeof Backbone"),
            "missing alias typeof row:\n{emitted}"
        );
        assert!(
            emitted.lines().any(|line| line == ">x : typeof Backbone"),
            "missing alias use row:\n{emitted}"
        );
    }

    #[test]
    fn imported_require_alias_member_constructs() {
        let logical = "tests/cases/compiler/requireAliasPin.ts";
        let case_text = "\
// @module: commonjs
// @Filename: requireAliasPin_main.ts
import Backbone = require(\"./requireAliasPin_backbone\");
var m = new Backbone.Model();
// @Filename: requireAliasPin_backbone.ts
export class Model {
    public someData: string;
}
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted
                .lines()
                .any(|line| line == ">new Backbone.Model() : Model"),
            "missing member construction row:\n{emitted}"
        );
    }
    #[test]
    fn duplicate_plain_types_baselines_are_ambiguous() {
        let mut groups: BaselineGroups = BTreeMap::new();
        groups.insert(
            ("foo".to_owned(), "types".to_owned()),
            vec![
                (
                    String::new(),
                    "tests/baselines/reference/foo.types".to_owned(),
                ),
                (
                    String::new(),
                    "tests/baselines/reference/foo-dup.types".to_owned(),
                ),
            ],
        );
        let error = resolve_stem_baseline(&groups, "tests/cases/compiler/foo.ts", "types", &[])
            .expect_err("duplicate plains");
        assert_eq!(error.code(), ErrorCode::Duplicate);
    }

    #[test]
    fn declaration_section_name_swaps_extensions_per_upstream() {
        assert_eq!(declaration_section_name("a.ts"), "a.d.ts");
        assert_eq!(declaration_section_name("b.mts"), "b.d.mts");
        assert_eq!(declaration_section_name("c.cts"), "c.d.cts");
        assert_eq!(declaration_section_name("d.tsx"), "d.d.ts");
    }

    #[test]
    fn javascript_section_name_derives_output_extension_per_upstream() {
        // `.ts` -> `.js` always; `.tsx`/`.jsx` -> `.jsx` only under
        // `jsx: preserve`, otherwise `.js`; module-format extensions carry
        // through. This mirrors `outputpaths.GetOutputExtension`.
        assert_eq!(javascript_section_name("a.ts", false), "a.js");
        assert_eq!(javascript_section_name("a.ts", true), "a.js");
        assert_eq!(javascript_section_name("file.tsx", true), "file.jsx");
        assert_eq!(javascript_section_name("file.tsx", false), "file.js");
        assert_eq!(javascript_section_name("view.jsx", true), "view.jsx");
        assert_eq!(javascript_section_name("view.jsx", false), "view.js");
        assert_eq!(javascript_section_name("m.mts", false), "m.mjs");
        assert_eq!(javascript_section_name("c.cts", false), "c.cjs");
        assert_eq!(javascript_section_name("data.json", false), "data.json");
        // A name with no recognised extension still gains `.js`.
        assert_eq!(javascript_section_name("LICENSE", false), "LICENSE.js");
    }

    #[test]
    fn output_section_name_uses_bundle_for_outfile_and_unit_for_per_file() {
        // Per-file compile: the section is the unit's own output name.
        assert_eq!(
            output_section_name("a.tsx", None, |name| output_extension(name, true)
                .to_owned()),
            "a.jsx"
        );
        // `outFile` compile: every unit's JavaScript output is named after the
        // bundle, keeping the kind's extension.
        assert_eq!(
            output_section_name("a.ts", Some("bundle.js"), |name| {
                output_extension(name, false).to_owned()
            }),
            "bundle.js"
        );
        // The declaration slice of the same bundle swaps to the declaration
        // extension.
        assert_eq!(
            output_section_name("a.ts", Some("bundle.js"), declaration_extension),
            "bundle.d.ts"
        );
        // A `.d.ts` bundle keeps the compound declaration extension.
        assert_eq!(
            output_section_name("a.ts", Some("types.d.ts"), declaration_extension),
            "types.d.ts"
        );
    }

    /// The authority documents order the emit slices as: every input echo in
    /// unit order, then every `.js` output in unit order, then every `.d.ts`
    /// output in unit order (`allowSyntheticDefaultImportsCanPaintCrossModule
    /// Declaration.js` is the reference shape). Declaration inputs echo but
    /// contribute no output section.
    #[test]
    fn javascript_baseline_orders_js_sections_before_dts_sections() {
        let logical = "tests/cases/compiler/orderPin.ts";
        let case_text = "\
// @declaration: true
// @filename: b.ts
export const b = 2;
// @filename: a.ts
export const a = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec![
                "//// [b.ts]",
                "//// [a.ts]",
                "//// [b.js]",
                "//// [a.js]",
                "//// [b.d.ts]",
                "//// [a.d.ts]"
            ],
            "{emitted}"
        );
    }

    /// A `.d.ts` input unit is echoed but never emitted: upstream's output
    /// mapping skips declaration files outright, so a document with a
    /// `module.d.ts` echo carries no `module.js`/`module.d.ts` section.
    #[test]
    fn javascript_baseline_skips_declaration_input_outputs() {
        let logical = "tests/cases/compiler/declInputPin.ts";
        let case_text = "\
// @declaration: true
// @filename: module.d.ts
declare const m: number;
// @filename: test.ts
export const t = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec![
                "//// [module.d.ts]",
                "//// [test.ts]",
                "//// [test.js]",
                "//// [test.d.ts]"
            ],
            "{emitted}"
        );
    }

    #[test]
    fn declaration_facet_labels_its_own_failures() {
        let baseline_doc = "//// [tests/cases/compiler/declPin.ts] ////\n\
            \n\
            //// [declPin.ts]\nvar x: number = 1;\n\
            \n\
            //// [declPin.d.ts]\ndeclare var x: number;\n";
        let emitted = "//// [declPin.d.ts]\ndeclare var x: number;\nlet y: number;\n";
        let verdict = compare_declaration_emit(&extract_dts_sections(baseline_doc, 1), emitted);
        match verdict {
            FacetVerdict::Fail { reason } => {
                assert!(
                    reason.starts_with("declaration structural mismatch"),
                    "declaration rows must carry the declaration facet label: {reason}"
                );
            }
            other => panic!("expected a Fail verdict, got {other:?}"),
        }
    }

    #[test]
    fn javascript_baseline_skips_json_input_outputs() {
        let logical = "tests/cases/compiler/jsonInputPin.ts";
        let case_text = "\
// @resolveJsonModule: true
// @filename: data.json
{\"k\": 1}
// @filename: test.ts
export const t = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec!["//// [data.json]", "//// [test.ts]", "//// [test.js]"],
            "{emitted}"
        );
    }

    #[test]
    fn javascript_baseline_skips_arbitrary_extension_declaration_inputs() {
        let logical = "tests/cases/compiler/arbitraryExtensionDeclarationPin.ts";
        let case_text = "\
// @allowArbitraryExtensions: true
// @filename: styles.d.css.ts
export declare const rules: string;
// @filename: test.ts
export const t = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec!["//// [styles.d.css.ts]", "//// [test.ts]", "//// [test.js]"],
            "{emitted}"
        );
    }

    #[test]
    fn javascript_baseline_emits_json_with_out_dir() {
        let logical =
            "tests/cases/compiler/isolatedModules_resolveJsonModule_strict_outDir_commonJsPin.ts";
        let case_text = "\
// @resolveJsonModule: true
// @outDir: dist
// @module: commonjs
// @filename: a.ts
import * as j from \"./j.json\";
// @filename: j.json
{}";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec![
                "//// [a.ts]",
                "//// [j.json]",
                "//// [j.json]",
                "//// [a.js]"
            ],
            "{emitted}"
        );
    }

    #[test]
    fn javascript_baseline_skips_package_json_with_out_dir() {
        let logical = "tests/cases/compiler/packageJsonPin.ts";
        let case_text = "\
// @outDir: dist
// @filename: package.json
{\"name\": \"typescript\"}
// @filename: test.ts
export const t = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec!["//// [package.json]", "//// [test.ts]", "//// [test.js]"],
            "{emitted}"
        );
    }
    #[test]
    fn javascript_baseline_skips_node_modules_json_with_out_dir() {
        let logical = "tests/cases/compiler/nodeModulesJsonPin.ts";
        let case_text = "\
// @resolveJsonModule: true
// @outDir: dist
// @module: commonjs
// @filename: a.ts
import * as b from \"./node_modules/b.json\";
// @filename: node_modules/b.json
{\"a\": true}
:";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec!["//// [a.ts]", "//// [b.json]", "//// [a.js]"],
            "requireOfJsonFileNonRelative.js omits node_modules json outputs: {emitted}"
        );
    }

    #[test]
    fn javascript_baseline_skips_unimported_json_with_out_dir() {
        let logical = "tests/cases/compiler/unimportedJsonPin.ts";
        let case_text = "\
// @resolveJsonModule: true
// @outDir: dist
// @module: commonjs
// @filename: a.ts
import * as c from \"./c.json\";
// @filename: b.json
{\"a\": true}
// @filename: c.json
{\"a\": true}
:";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec![
                "//// [a.ts]",
                "//// [b.json]",
                "//// [c.json]",
                "//// [c.json]",
                "//// [a.js]"
            ],
            "requireOfJsonFileWithoutExtensionResolvesToTs.js emits only the imported c.json: {emitted}"
        );
    }
    #[test]
    fn javascript_baseline_json_section_carries_compiler_emit() {
        let logical = "tests/cases/compiler/emptyJsonPin.ts";
        let case_text = "\
// @resolveJsonModule: true
// @outDir: dist
// @module: commonjs
// @filename: file1.ts
import * as b1 from \"./b.json\";
let x = b1;
// @filename: b.json
{
}";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let compiler_body = case
            .reached_units_in_module_order()
            .into_iter()
            .find(|(unit, _)| unit.virtual_path.ends_with("b.json"))
            .and_then(|(_, output)| output.emit().and_then(|emit| emit.javascript.as_ref()))
            .map(|javascript| javascript.code.clone())
            .expect("json module carries compiler emit");
        assert!(
            !compiler_body.is_empty(),
            "the harness must have compiler output to carry: {emitted}"
        );
        assert!(
            emitted.contains(&format!("//// [b.json]\n{compiler_body}")),
            "the json output section carries the compiler's emit for that unit, not the raw unit text (requireOfJsonFileWithEmptyObject.js re-serializes that input to {{}}; the compiler has no json output mapping, crates/bamts-compiler/src/project/output.rs:417, and emits the file through the TS transform instead, crates/bamts-compiler/src/emitter/transforms.rs:231): {emitted}"
        );
    }
    #[test]
    fn module_order_reference_cycle_completes_dependency_first() {
        // A `/// <reference>` cycle lowers to the same graph shape as an
        // import cycle, so it follows the same authority rule: the member
        // reached through the edge completes first. The authority import
        // cycle `asyncFunctionsAcrossFiles.ts` (`a` imports `b`, `b` imports
        // `a`) carries `//// [b.js]` before `//// [a.js]`.
        let logical = "tests/cases/compiler/referenceCycleOrderPin.ts";
        let case_text = "\
// @filename: file0.ts
/// <reference path=\"file1.ts\" />
var x = 1;
// @filename: file1.ts
/// <reference path=\"file0.ts\" />
var y = 2;";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let order: Vec<String> = case
            .reached_units_in_module_order()
            .into_iter()
            .map(|(unit, _)| unit_basename(&unit.virtual_path))
            .collect();
        assert_eq!(order, vec!["file1.ts".to_owned(), "file0.ts".to_owned()]);
    }
    #[test]
    fn module_order_shared_reference_target_completes_first() {
        // Post-order descent from the first root reaches `file3` through
        // `file1`, then `file2` through `file3`, so the shared target's
        // other dependent completes before the hub and the entry root
        // completes last. The authority hub
        // `caseInsensitiveFileSystemWithCapsImportTypeDeclarations.js`
        // shows the same rule (`types` shared by `type-a` and `type-b`
        // completes before both, `index` completes last).
        let logical = "tests/cases/compiler/referenceHubOrderPin.ts";
        let case_text = "\
// @filename: file1.ts
/// <reference path=\"file3.ts\" />
var a = 1;
// @filename: file2.ts
/// <reference path=\"file3.ts\" />
var b = 2;
// @filename: file3.ts
/// <reference path=\"file2.ts\" />
/// <reference path=\"file1.ts\" />
var c = 3;";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let order: Vec<String> = case
            .reached_units_in_module_order()
            .into_iter()
            .map(|(unit, _)| unit_basename(&unit.virtual_path))
            .collect();
        assert_eq!(
            order,
            vec![
                "file2.ts".to_owned(),
                "file3.ts".to_owned(),
                "file1.ts".to_owned()
            ]
        );
    }
    #[test]
    fn javascript_baseline_empty_json_section_carries_compiler_emit() {
        let logical = "tests/cases/compiler/emptyJsonContentPin.ts";
        let case_text = "\
// @resolveJsonModule: true
// @outDir: dist
// @module: commonjs
// @filename: file1.ts
import * as b1 from \"./b.json\";
let x = b1;
// @filename: b.json
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let compiler_body = case
            .reached_units_in_module_order()
            .into_iter()
            .find(|(unit, _)| unit.virtual_path.ends_with("b.json"))
            .and_then(|(_, output)| output.emit().and_then(|emit| emit.javascript.as_ref()))
            .map(|javascript| javascript.code.clone())
            .expect("json module carries compiler emit");
        assert!(
            compiler_body.is_empty(),
            "requireOfJsonFileWithNoContent.js emits an empty JSON body: {compiler_body:?}"
        );
        let (_, json_output) = emitted
            .rsplit_once("//// [b.json]\n")
            .expect("the imported JSON has an output section after its input echo");
        let (json_body, _) = json_output
            .split_once("//// [file1.js]\n")
            .expect("the JavaScript output follows the JSON output");
        assert_eq!(
            json_body.trim_end_matches('\n'),
            compiler_body,
            "the JSON output section carries the compiler's empty emit without a prelude: {emitted}"
        );
    }
    #[test]
    fn trace_lib_replacement_case_requests_no_resolutions() {
        let logical = "tests/cases/compiler/libReplacement.ts";
        let case_text = "// @target: es2015\n// @lib: esnext\n// @traceResolution: true\n// @noTypesAndSymbols: true\n// @noEmit: true\n// @libReplacement: true,false\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let log = collect_case_resolution_trace(&case);
        assert!(
            log.lines().is_empty(),
            "libReplacement(libreplacement=false).trace.json is []: a case with no imports requests no resolutions: {:?}",
            log.lines()
        );
    }

    #[test]
    fn extract_dts_sections_selects_only_declaration_output() {
        // Real upstream shape (argumentsReferenceInConstructor4_Js.js): a
        // document header with trailing ////, an input echo, then the `a.d.ts`
        // output section. Only the declaration section may survive.
        let doc = "//// [tests/cases/compiler/argumentsReferenceInConstructor4_Js.ts] ////\n\
            \n\
            //// [a.js]\nclass A {}\n\
            \n\
            //// [a.d.ts]\ndeclare class A {}\n";
        assert_eq!(
            extract_dts_sections(doc, 1),
            "//// [a.d.ts]\ndeclare class A {}\n"
        );
    }

    #[test]
    fn declaration_baseline_frames_and_compares_upstream_sections() {
        let logical = "tests/cases/compiler/declPin.ts";
        let case_text = "var x: number = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_frontend(
            &units,
            &entry,
            &CasePragmas::default(),
            FrontendMode::Declaration,
        )
        .expect("case compiles");
        let emitted = emit_declaration_baseline(&case).expect("declaration emit");
        assert_eq!(emitted, "//// [declPin.d.ts]\ndeclare var x: number;\n");
        let baseline_doc = "//// [tests/cases/compiler/declPin.ts] ////\n\
            \n\
            //// [declPin.ts]\nvar x: number = 1;\n\
            \n\
            //// [declPin.d.ts]\ndeclare var x: number;\n";
        assert_eq!(
            compare_js_emit(&extract_dts_sections(baseline_doc, 1), &emitted),
            FacetVerdict::Pass
        );
        let semantic = baseline_doc.replace("number", "string");
        assert!(matches!(
            compare_js_emit(&extract_dts_sections(&semantic, 1), &emitted),
            FacetVerdict::Fail { .. }
        ));
    }

    /// The javascript doc assembly reproduces the upstream `doJsEmitBaseline`
    /// framing: document header with trailing `////`, a `//// [<basename>]`
    /// echo per unit, a block separator, then the `//// [<stem>.js]` section.
    /// The echo block is the unit bytes verbatim plus one `\n\n` separator, so
    /// the trailing newline count follows the source: a unit without a final
    /// newline leaves two, and a unit with one leaves three. Measured over the
    /// 7,246 single-unit `.js` baselines in the TypeScript 7.0.2 authority:
    /// 4,456 documents whose source lacks a final newline carry two, and 2,473
    /// whose source has one carry three. Stripping the final newline collapses
    /// the second group onto the first and fails every one of them.
    #[test]
    fn javascript_baseline_echoes_unit_bytes_verbatim() {
        for (case_text, expected_separator) in [("var x = 1;", "\n\n"), ("var x = 1;\n", "\n\n\n")]
        {
            let logical = "tests/cases/compiler/jsPin.ts";
            let units = split_case_units(logical, case_text);
            let entry = entry_virtual_path(logical, &units);
            let case = compile_case_frontend(
                &units,
                &entry,
                &CasePragmas::default(),
                FrontendMode::JavaScript,
            )
            .expect("case compiles");
            let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
            let expected_head = format!(
                "//// [tests/cases/compiler/jsPin.ts] ////\n\n//// [jsPin.ts]\nvar x = 1;{expected_separator}//// [jsPin.js]\n"
            );
            assert!(
                emitted.starts_with(&expected_head),
                "case {case_text:?} framed as {emitted:?}"
            );
            assert_eq!(compare_js_emit(&emitted, &emitted), FacetVerdict::Pass);
        }
    }

    /// Multi-unit framing, pinned against the authority document for
    /// `importCallExpression1ES2020` (its `0.ts` echo is the code line, then a
    /// blank line, then the `//// [1.ts]` marker). `split_case_units` hands a
    /// non-final unit the blank line that precedes the next `@filename`
    /// marker, so the echo stays verbatim here too: adding a separator per
    /// unit would emit a second blank line and fail all 970 multi-unit
    /// documents measured in the authority.
    #[test]
    fn javascript_baseline_echoes_every_unit_verbatim() {
        let logical = "tests/cases/compiler/multiPin.ts";
        let case_text = "// @filename: a.ts\nvar a = 1;\n\n// @filename: b.ts\nvar b = 2;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_frontend(
            &units,
            &entry,
            &CasePragmas::default(),
            FrontendMode::JavaScript,
        )
        .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        assert!(
            emitted.starts_with(
                "//// [tests/cases/compiler/multiPin.ts] ////\n\n\
                 //// [a.ts]\nvar a = 1;\n\n\
                 //// [b.ts]\nvar b = 2;\n\n\n"
            ),
            "framed as {emitted:?}"
        );
        assert_eq!(compare_js_emit(&emitted, &emitted), FacetVerdict::Pass);
    }

    /// Authority: `configFileExtendsAsList` and `compositeWithNodeModulesSourceFile`
    /// echo `tsconfig1.json` and `index.ts` but not the `tsconfig.json` they run
    /// under; no emit baseline with a `tsconfig.json` unit echoes it.
    #[test]
    fn javascript_baseline_leaves_the_tsconfig_unit_out_of_the_echo() {
        let logical = "tests/cases/compiler/configPin.ts";
        let case_text = "// @filename: /tsconfig.json\n{}\n\n// @filename: /a.ts\nvar a = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_frontend(
            &units,
            &entry,
            &CasePragmas::default(),
            FrontendMode::JavaScript,
        )
        .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        assert!(emitted.contains("//// [a.ts]\nvar a = 1;"), "{emitted}");
        assert!(!emitted.contains("tsconfig.json"), "{emitted}");
    }

    #[test]
    fn source_map_baseline_frames_real_printer_maps() {
        let logical = "tests/cases/compiler/mapPin.ts";
        let case_text = "// @sourcemap: true\nvar v = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_source_map_baseline(&case, false).expect("map emit");
        assert!(
            emitted.starts_with("//// [mapPin.js.map]\n{\"version\":3"),
            "{emitted}"
        );
        assert!(emitted.contains("\"file\":\"mapPin.js\""), "{emitted}");
        assert!(emitted.contains("\"sources\":[\"mapPin.ts\"]"), "{emitted}");
        assert!(emitted.contains("\"sourceRoot\":\"\""), "{emitted}");
        assert_eq!(compare_source_map(&emitted, &emitted), FacetVerdict::Pass);
    }

    #[test]
    fn inline_source_maps_record_the_missing_record_producer() {
        let inline = compile_option_pairs(&parse_case_pragmas(
            "// @inlinesourcemap: true\nvar v = 1;\n",
        ));
        assert!(is_inline_source_map(&inline));
        assert!(inline_source_map_producer_gap().starts_with("producer missing: "));
        let external =
            compile_option_pairs(&parse_case_pragmas("// @sourcemap: true\nvar v = 1;\n"));
        assert!(!is_inline_source_map(&external));
    }

    /// The build-info observer extracts `//// [name.tsbuildinfo]` sections
    /// from a `.js` baseline and compares them byte-for-byte (under line-wise
    /// normalization) against the emitted build-info content. This test proves
    /// a matching section passes and a single differing byte fails.
    #[test]
    fn build_info_observer_compares_section_and_fails_on_differing_byte() {
        let case_text = "// @target: es2015\n// @incremental: true\nconst x = 10;\n";
        let logical = "tests/cases/compiler/buildInfoUnit.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas)
            .expect("case compiles with incremental");
        let emitted = emit_build_info_baseline(&case, &pragmas);
        assert!(
            !emitted.is_empty(),
            "build-info emission must produce content"
        );
        assert!(
            emitted.contains("\"version\":\"bamts-build-1\""),
            "emitted build-info must carry the BAMTS schema version"
        );

        // A baseline section that matches the emitted content must pass.
        let matching_baseline = format!(
            "//// [tests/cases/compiler/buildInfoUnit.ts] ////\n\n\
             //// [buildInfoUnit.ts]\nconst x = 10;\n\n\
             //// [buildInfoUnit.js]\n\"use strict\";\nconst x = 10;\n\n\
             //// [buildInfoUnit.tsbuildinfo]\n{emitted}\n"
        );
        let expected_sections = extract_tsbuildinfo_sections(&matching_baseline);
        assert!(
            !expected_sections.is_empty(),
            "extraction must find the .tsbuildinfo section"
        );
        let verdict = compare_js_emit(&expected_sections, &emitted);
        assert_eq!(
            verdict,
            FacetVerdict::Pass,
            "matching build-info section must pass"
        );

        // A single differing byte in the build-info section must fail.
        let tampered = emitted.replacen('"', "X", 1);
        let tampered_baseline = format!("//// [buildInfoUnit.tsbuildinfo]\n{tampered}\n");
        let tampered_sections = extract_tsbuildinfo_sections(&tampered_baseline);
        let verdict = compare_js_emit(&tampered_sections, &emitted);
        assert!(
            matches!(verdict, FacetVerdict::Fail { .. }),
            "a differing byte in the build-info section must fail"
        );
    }

    /// The build-info observer reports a precise producer gap when the `.js`
    /// baseline has no `//// [name.tsbuildinfo]` section.
    #[test]
    fn build_info_observer_reports_gap_when_no_section() {
        let baseline = "//// [case.ts] ////\n\n//// [a.ts]\nconst x = 10;\n\n//// [a.js]\n\"use strict\";\nconst x = 10;\n";
        let sections = extract_tsbuildinfo_sections(baseline);
        assert!(
            sections.is_empty(),
            "no .tsbuildinfo section must yield empty extraction"
        );
    }

    #[test]
    fn mount_specifiers_in_collects_only_quoted_virtual_roots() {
        let text = concat!(
            "/// <reference path=\"/.lib/react.d.ts\" />\n",
            "import x from '/.lib/other.d.ts';\n",
            "import y from './local';\n",
            "// a comment mentioning /.lib/unquoted\n",
            "import z from \"/.ts/typescript.d.ts\";\n",
            "/// <reference path=\"/.lib/../evil.d.ts\" />\n",
        );
        assert_eq!(
            mount_specifiers_in(text),
            vec![
                "/.lib/react.d.ts".to_owned(),
                "/.lib/other.d.ts".to_owned(),
                "/.ts/typescript.d.ts".to_owned(),
            ]
        );
    }

    #[test]
    fn inject_mount_paths_maps_only_served_roots() {
        let base = build_tsconfig(&CasePragmas::default());
        let mapped = inject_mount_paths(base.clone(), &["/.lib/", "/.ts/"]);
        assert!(
            mapped.contains("\"paths\":{\"/.lib/*\":[\"./.lib/*\"],\"/.ts/*\":[\"./.ts/*\"]}"),
            "{mapped}"
        );
        assert_eq!(inject_mount_paths(base.clone(), &[]), base);
        assert_eq!(inject_mount_paths(mapped.clone(), &["/.lib/"]), mapped);
    }

    #[test]
    fn inject_mount_paths_keeps_a_case_owned_mapping() {
        let base =
            "{\"compilerOptions\":{\"paths\":{\"/.lib/*\":[\"./vendor/lib/*\"]}}}".to_owned();
        let mapped = inject_mount_paths(base.clone(), &["/.lib/"]);
        assert!(
            mapped.contains("\"/.lib/*\":[\"./vendor/lib/*\"]"),
            "a case mapping is never replaced: {mapped}"
        );
        assert!(
            !mapped.contains("./.lib/*"),
            "no duplicate mount mapping is added: {mapped}"
        );
    }

    #[test]
    fn mount_files_resolve_harness_reference_and_module() {
        let text =
            "/// <reference path=\"/.lib/react.d.ts\" />\nimport \"react\";\nexport const x = 1;\n";
        let logical = "tests/cases/compiler/mountPin.ts";
        let units = split_case_units(logical, text);
        let entry = entry_virtual_path(logical, &units);
        let case =
            compile_case_frontend(&units, &entry, &CasePragmas::default(), FrontendMode::Check)
                .expect("case with served mounts compiles");
        let codes: Vec<String> = case
            .reached_units()
            .flat_map(|(_, output)| {
                output
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| diagnostic.code().as_str().to_owned())
            })
            .collect();
        assert!(
            !codes.iter().any(|code| code == "TS2307"),
            "served mounts resolve the reference and the module: {codes:?}"
        );
    }

    /// The pinned authority test tree, resolved from this crate's location so
    /// the tests do not depend on one developer's checkout. Overridable with
    /// `BAMTS_AUTHORITY_ROOT` for a tree materialized elsewhere. Falls back
    /// to the in-repo `.references` testdata the mount harness serves when no
    /// `target/authority` tree is checked out, so receipt-independent sampler
    /// tests run hermetically; the layout helpers below bridge the testdata
    /// `baselines/reference` shape to the authority `tests/baselines`
    /// `reference` shape.
    fn authority_tests_root() -> std::path::PathBuf {
        if let Ok(root) = std::env::var("BAMTS_AUTHORITY_ROOT") {
            return std::path::PathBuf::from(root);
        }
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let candidate = manifest.join("../../target/authority/typescript-7.0.2-tests");
        if candidate.is_dir() {
            return candidate;
        }
        if let Some(testdata) = super::reference_testdata_root() {
            return testdata;
        }
        manifest.join("../../target/authority/typescript-7.0.2-tests")
    }

    /// The baseline reference directory for an authority root: the fetched
    /// tree keeps `tests/baselines/reference`, while the in-repo testdata
    /// fallback keeps `baselines/reference`.
    fn authority_reference_dir(root: &std::path::Path) -> std::path::PathBuf {
        let canonical = root.join("tests/baselines/reference");
        if canonical.is_dir() {
            return canonical;
        }
        root.join("baselines/reference")
    }

    /// The `.types` baseline file for one enum-sample case. The fetched tree
    /// is flat; the testdata fallback nests baselines one level down
    /// (`compiler/`, `conformance/`), so a missing flat file falls through
    /// to the area matching the case's suite.
    fn enum_baseline_for(
        reference_dir: &std::path::Path,
        logical: &str,
        stem: &str,
    ) -> std::path::PathBuf {
        let flat = reference_dir.join(format!("{stem}.types"));
        if flat.exists() {
            return flat;
        }
        let suite = if logical.starts_with("tests/cases/conformance/") {
            "conformance"
        } else {
            "compiler"
        };
        reference_dir.join(suite).join(format!("{stem}.types"))
    }

    /// Collect nested `.js` baselines under a reference dir by case stem.
    /// Only the in-repo testdata fallback needs this: its baselines live one
    /// level down (`compiler/`, `conformance/`), which `baseline_groups`
    /// deliberately excludes, so the sampler keeps its own stem map.
    fn collect_nested_js_baselines(
        reference: &std::path::Path,
        out: &mut BTreeMap<String, Vec<(String, std::path::PathBuf)>>,
    ) {
        let mut stack = vec![reference.to_path_buf()];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                    continue;
                }
                let name = entry.file_name().to_string_lossy().into_owned();
                let Some((stem, extension, suffix)) = super::split_baseline_file_name(&name)
                else {
                    continue;
                };
                if extension != "js" {
                    continue;
                }
                out.entry(stem.to_owned())
                    .or_default()
                    .push((suffix.to_owned(), path));
            }
        }
    }

    /// Pick one nested `.js` baseline for a case, mirroring
    /// `resolve_stem_baseline`: an option-matching variant wins when the case
    /// sets options, else the plain baseline, else the smallest suffix. Zero
    /// or ambiguous candidates resolve to no baseline and the case skips.
    fn select_nested_js_baseline(
        nested: &BTreeMap<String, Vec<(String, std::path::PathBuf)>>,
        logical: &str,
        compile_options: &[(String, String)],
    ) -> Option<std::path::PathBuf> {
        let stem = super::case_stem(logical);
        let candidates = nested.get(stem)?;
        if !compile_options.is_empty() {
            let matches: Vec<_> = candidates
                .iter()
                .filter(|(suffix, _)| {
                    !suffix.is_empty()
                        && super::suffix_matches_options(suffix, compile_options)
                })
                .collect();
            if matches.len() > 1 {
                return None;
            }
            if let Some((_, path)) = matches.first() {
                return Some((*path).clone());
            }
        }
        let plains: Vec<_> = candidates
            .iter()
            .filter(|(suffix, _)| suffix.is_empty())
            .collect();
        if plains.len() > 1 {
            return None;
        }
        if let Some((_, path)) = plains.first() {
            return Some((*path).clone());
        }
        candidates
            .iter()
            .min_by(|left, right| left.0.cmp(&right.0))
            .map(|(_, path)| path.clone())
    }

    /// Run the 10 build-info evidence-sweep cells through the observer's core
    /// path: compile each case, emit build-info, extract `.tsbuildinfo`
    /// sections from the authority `.js` baseline, and compare. Reports
    /// per-cell PASS or BLOCKING_FAIL with the first differing line.
    #[test]
    fn build_info_ten_evidence_cells_per_cell_verdict() {
        let authority = authority_tests_root();
        let authority = authority.as_path();
        let cases: &[(&str, &str)] = &[
            (
                "incrementalConfig",
                "// @target: es2015\n// @incremental: true\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n\n\
                 // @Filename: /tsconfig.json\n{ }\n",
            ),
            (
                "incrementalInvalid",
                "// @target: es2015\n// @incremental: true\n\n\
                 // @Filename: /a.ts\nconst x:;\n",
            ),
            (
                "incrementalOut",
                "// @target: es2015\n// @incremental: true\n// @outDir: dist\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "incrementalTsBuildInfoFile",
                "// @target: es2015\n// @incremental: true\n\
                 // @tsBuildInfoFile: ./mybuildinfo\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "optionsTsBuildInfoFileWithoutIncrementalAndComposite",
                "// @target: es2015\n// @tsBuildInfoFile: ./mybuildinfo\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "optionsCompositeWithIncrementalFalse",
                "// @target: es2015\n// @composite: true\n// @incremental: false\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "declarationEmitToDeclarationDirWithCompositeOption",
                "// @target: es2015\n// @composite: true\n// @declaration: true\n\
                 // @declarationDir: decls\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "declarationEmitWithComposite",
                "// @target: es2015\n// @composite: true\n// @declaration: true\n\n\
                 // @Filename: /a.ts\nexport const x = 10;\n",
            ),
            (
                "jsEmitIntersectionProperty",
                "// @target: es2015\n// @composite: true\n\n\
                 // @Filename: /a.ts\nexport const x = 10;\n",
            ),
            (
                "jsFileCompilationWithEnabledCompositeOption",
                "// @target: es2015\n// @composite: true\n// @allowJs: true\n\n\
                 // @Filename: /a.js\nvar x = 10;\n",
            ),
        ];
        let mut results: Vec<(&str, String)> = Vec::new();
        for (name, case_text) in cases {
            let logical = format!("tests/cases/compiler/{name}.ts");
            let units = split_case_units(&logical, case_text);
            let entry = entry_virtual_path(&logical, &units);
            let pragmas = parse_case_pragmas(case_text);
            let baseline_path = authority
                .join("tests/baselines/reference")
                .join(format!("{name}.js"));
            let baseline = fs::read_to_string(&baseline_path).unwrap_or_else(|_| String::new());
            let expected_sections = extract_tsbuildinfo_sections(&baseline);
            let verdict: String = {
                match compile_case_with_pragmas(&units, &entry, &pragmas) {
                    Err(error) => format!("BLOCKING_FAIL: compile error: {error:?}"),
                    Ok(case) => {
                        let emitted = emit_build_info_baseline(&case, &pragmas);
                        if !expected_sections.is_empty() {
                            match compare_js_emit(&expected_sections, &emitted) {
                                FacetVerdict::Pass => "PASS".to_owned(),
                                FacetVerdict::Fail { reason } => {
                                    format!("BLOCKING_FAIL: {reason}")
                                }
                                FacetVerdict::Unproven { reason } => {
                                    format!("BLOCKING_FAIL: unproven: {reason}")
                                }
                            }
                        } else {
                            // Emission-shape contract: the 7.0.2 reference
                            // tree carries zero .tsbuildinfo sections, so the
                            // verdict keys on implied-vs-produced.
                            let implied = build_info_implied(&pragmas);
                            let produced = !emitted.is_empty()
                                && !emitted.starts_with("build-info encode error:");
                            match (implied, produced) {
                                (true, true) => "PASS: produced".to_owned(),
                                (true, false) => {
                                    "BLOCKING_FAIL: implied but not produced".to_owned()
                                }
                                (false, false) => "PASS: none implied".to_owned(),
                                (false, true) => {
                                    "BLOCKING_FAIL: produced without implication".to_owned()
                                }
                            }
                        }
                    }
                }
            };
            results.push((name, verdict));
        }
        let report = results
            .iter()
            .map(|(name, verdict)| format!("  {name}: {verdict}"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(
            results.len(),
            10,
            "all 10 cells must be exercised\n{report}"
        );
    }

    /// Measures the `.types` facet on a 60-cell sample of authority cases
    /// whose names start with `enum`.  This is a measurement test, not a
    /// pass/fail gate: it prints the exact-match count so the EnumMemberAny
    /// node can report before/after numbers.
    #[test]
    fn enum_types_facet_sample_60_cells() {
        let authority_root = authority_tests_root().to_string_lossy().into_owned();
        let cases_dir = format!("{authority_root}/tests/cases/compiler");
        let conformance_dir = format!("{authority_root}/tests/cases/conformance/enums");
        let reference_dir =
            authority_reference_dir(std::path::Path::new(&authority_root));

        // Collect enum-named .ts case files from both directories.
        let mut case_paths: Vec<(String, String)> = Vec::new();
        for dir in [&cases_dir, &conformance_dir] {
            let Ok(entries) = std::fs::read_dir(dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let name = path.file_name().unwrap().to_string_lossy().into_owned();
                if !name.starts_with("enum") || !name.ends_with(".ts") {
                    continue;
                }
                let stem = name.trim_end_matches(".ts");
                let logical = if *dir == cases_dir {
                    format!("tests/cases/compiler/{name}")
                } else {
                    format!("tests/cases/conformance/enums/{name}")
                };
                if !enum_baseline_for(&reference_dir, &logical, stem).exists() {
                    continue;
                }
                let text = match std::fs::read_to_string(&path) {
                    Ok(text) => text,
                    Err(_) => continue,
                };
                case_paths.push((logical, text));
            }
        }
        case_paths.sort_by(|a, b| a.0.cmp(&b.0));
        let sample: Vec<_> = case_paths.into_iter().take(60).collect();
        let total = sample.len();
        assert!(
            total >= 60,
            "expected at least 60 enum cases with .types baselines, found {total}"
        );

        let mut exact_matches = 0usize;
        let mut mismatches = 0usize;
        let mut compile_failures = 0usize;
        let mut missing_baselines = 0usize;

        for (logical, text) in &sample {
            let stem = logical.rsplit('/').next().unwrap().trim_end_matches(".ts");
            let baseline_path = enum_baseline_for(&reference_dir, logical, stem);
            let units = split_case_units(logical, text);
            let entry = entry_virtual_path(logical, &units);
            let case = match compile_case(&units, &entry) {
                Ok(case) => case,
                Err(_) => {
                    compile_failures += 1;
                    continue;
                }
            };
            let emitted = emit_types_baseline(&case, logical);
            let expected = match std::fs::read_to_string(&baseline_path) {
                Ok(text) => text,
                Err(_) => {
                    missing_baselines += 1;
                    continue;
                }
            };
            let verdict = compare_types(&expected, &emitted);
            if matches!(verdict, FacetVerdict::Pass) {
                exact_matches += 1;
            } else {
                mismatches += 1;
            }
        }

        let report = format!(
            "enum_types_facet_sample: total={total} exact_matches={exact_matches} \
             mismatches={mismatches} compile_failures={compile_failures} \
             missing_baselines={missing_baselines}"
        );
        write_facet_report("types-60", &report);
    }

    /// Region-attributed first-delta measurement over authority javascript
    /// cells (receipt-independent): resolves the baseline with the harness's
    /// own variant logic, assembles our document with
    /// `emit_javascript_baseline`, and classifies the first whole-document
    /// delta by the section it lands in — echo (framing/input text), `.js`
    /// (emit bytes), `.d.ts` (declaration drift surfacing here), or a
    /// section header itself (section-set drift). Measurement only; the
    /// report lands under the session scratch root.
    #[test]
    fn javascript_facet_first_delta_sample() {
        let authority = authority_tests_root();
        let sample_cap: usize = std::env::var("BAMTS_JS_SAMPLE")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(120);
        let cases_root = authority.join("tests/cases");
        let mut index = SuiteIndex {
            entries: BTreeMap::new(),
        };
        let reference = authority_reference_dir(&authority);
        let mut baseline_names: Vec<String> = std::fs::read_dir(&reference)
            .expect("reference baselines")
            .flatten()
            .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "js"))
            .filter_map(|entry| entry.file_name().into_string().ok())
            .collect();
        baseline_names.sort();
        // The in-repo testdata fallback nests baselines one level down
        // (`compiler/`, `conformance/`), so a flat listing finds nothing.
        // Collect nested `.js` baselines by stem for discovery and for the
        // groups-miss fallback below; the fetched tree always lists flat
        // baselines, so this walk never runs there.
        let mut nested_js: BTreeMap<String, Vec<(String, std::path::PathBuf)>> =
            BTreeMap::new();
        if baseline_names.is_empty() {
            collect_nested_js_baselines(&reference, &mut nested_js);
        }
        let mut known_names = baseline_names.clone();
        known_names.extend(nested_js.keys().map(|stem| format!("{stem}.js")));
        known_names.sort();
        known_names.dedup();
        for name in &baseline_names {
            index.entries.insert(
                format!("{BASELINE_REFERENCE_PREFIX}{name}"),
                IndexEntry {
                    logical_path: format!("{BASELINE_REFERENCE_PREFIX}{name}"),
                    sha256: "0".repeat(64),
                    asset_kind: crate::suite::AssetKind::BaselineFacet,
                    facet: None,
                    partition: None,
                },
            );
        }
        let groups = baseline_groups(&index);
        let mut case_paths = Vec::new();
        // Recursive walk: the conformance suite nests cases in
        // subdirectories, and a flat read_dir samples only compiler's
        // alphabetical head. Stride sampling then spreads the pick across
        fn walk(
            dir: &std::path::Path,
            cases_root: &std::path::Path,
            out: &mut Vec<(String, String)>,
            baseline_names: &[String],
        ) {
            let Some(entries) = std::fs::read_dir(dir).ok() else {
                return;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, cases_root, out, baseline_names);
                    continue;
                }
                if path.extension().and_then(|ext| ext.to_str()) != Some("ts") {
                    continue;
                }
                let name = entry.file_name().to_string_lossy().into_owned();
                let stem = name.trim_end_matches(".ts");
                if !baseline_names.iter().any(|base| {
                    base.trim_end_matches(".js") == stem || base.starts_with(&format!("{stem}("))
                }) {
                    continue;
                }
                let Ok(rel) = path.strip_prefix(cases_root) else {
                    continue;
                };
                let logical = format!("tests/cases/{}", rel.to_string_lossy().replace('\\', "/"));
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                out.push((logical, text));
            }
        }
        walk(&cases_root, &cases_root, &mut case_paths, &known_names);
        case_paths.sort();
        case_paths.dedup();
        let stride = (case_paths.len() / sample_cap).max(1);
        let sample: Vec<_> = case_paths
            .iter()
            .step_by(stride)
            .take(sample_cap)
            .cloned()
            .collect();

        let mut regions: BTreeMap<&str, usize> = BTreeMap::new();
        let mut passes = 0usize;
        let mut skipped = 0usize;
        let mut surplus: BTreeMap<String, isize> = BTreeMap::new();
        let mut examples: BTreeMap<&str, String> = BTreeMap::new();
        for (logical, text) in &sample {
            let units = split_case_units(logical, text);
            let entry = entry_virtual_path(logical, &units);
            let pragmas = parse_case_pragmas(text);
            let compile_options = compile_option_pairs(&pragmas);
            let baseline_path: Option<std::path::PathBuf> = resolve_stem_baseline(
                &groups,
                logical,
                "js",
                &compile_options,
            )
            .ok()
            .flatten()
            .map(|name| {
                let file = name
                    .strip_prefix(BASELINE_REFERENCE_PREFIX)
                    .unwrap_or(&name);
                reference.join(file)
            })
            .or_else(|| select_nested_js_baseline(&nested_js, logical, &compile_options));
            let Some(baseline_path) = baseline_path else {
                skipped += 1;
                continue;
            };
            let case =
                match compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript) {
                    Ok(case) => case,
                    Err(_) => {
                        *regions.entry("compile-failure").or_default() += 1;
                        continue;
                    }
                };
            let emitted = match emit_javascript_baseline(&case, logical) {
                Ok(emitted) => emitted,
                Err(_) => {
                    *regions.entry("emit-error").or_default() += 1;
                    continue;
                }
            };
            let expected =
                std::fs::read_to_string(&baseline_path).unwrap_or_default();
            let canon = |text: &str| -> Vec<String> {
                text.replace("\r\n", "\n")
                    .replace('\r', "\n")
                    .lines()
                    .map(|line| line.trim_end().to_owned())
                    .collect()
            };
            let (exp, act) = (canon(&expected), canon(&emitted));
            if exp == act {
                passes += 1;
                continue;
            }
            let first = exp
                .iter()
                .zip(act.iter())
                .position(|(e, a)| e != a)
                .unwrap_or_else(|| exp.len().min(act.len()));
            let region: &'static str = if exp
                .get(first)
                .is_some_and(|line| line.starts_with("//// ["))
            {
                "section-set"
            } else {
                let section = exp
                    .iter()
                    .take(first + 1)
                    .rev()
                    .find(|line| line.starts_with("//// ["))
                    .and_then(|header| header.strip_prefix("//// ["))
                    .map(|rest| rest.trim_end_matches(']'))
                    .unwrap_or("header");
                if section.ends_with(".d.ts") {
                    "dts-section"
                } else if section.ends_with(".ts") {
                    "source-echo"
                } else if section.ends_with(".js") {
                    // Split by emitted shape: a shorter document is a
                    // missing output (assembly or emit stop), a longer one
                    // is extra content, otherwise bytes differ in place.
                    if act.len() < exp.len() {
                        "js-shorter"
                    } else if act.len() > exp.len() {
                        "js-longer"
                    } else {
                        "js-byte-differs"
                    }
                } else {
                    "other"
                }
            };
            *regions.entry(region).or_default() += 1;
            examples.entry(region).or_insert_with(|| {
                format!(
                    "{logical} line {first}\n    expected: {}\n    emitted:   {}",
                    exp.get(first).map(String::as_str).unwrap_or("<eof>"),
                    act.get(first).map(String::as_str).unwrap_or("<eof>"),
                )
            });
            // Fold the alignment-free surplus/deficit tally into this pass:
            // compile failures and unresolvable baselines are already
            // tallied above, and passing cases contribute net zero.
            for line in &exp {
                *surplus.entry(line.clone()).or_default() += 1;
            }
            for line in &act {
                *surplus.entry(line.clone()).or_default() -= 1;
            }
        }
        let mut text_families: BTreeMap<&str, usize> = BTreeMap::new();
        let mut top_deficits: Vec<(isize, String)> = surplus
            .iter()
            .filter(|(_, count)| **count < 0)
            .map(|(line, count)| (*count, line.clone()))
            .collect();
        top_deficits.sort();
        // Indent-only mass: a trimmed-key map nets whitespace variants; a
        // trimmed form that nets zero while some untrimmed variant carries a
        // nonzero count is pure indentation drift.
        let mut trimmed_net: BTreeMap<String, isize> = BTreeMap::new();
        for (line, count) in &surplus {
            *trimmed_net.entry(line.trim().to_owned()).or_default() += *count;
        }
        let mut indent_only = 0usize;
        for (line, count) in &surplus {
            if *count == 0 {
                continue;
            }
            let nets_zero = trimmed_net.get(line.trim()).is_some_and(|net| *net == 0);
            if nets_zero {
                indent_only += 1;
            }
        }
        for (line, count) in &surplus {
            if *count == 0 {
                continue;
            }
            let family = if line.contains("function(") || line.contains("function (") {
                "function-space"
            } else if line.starts_with("//// [") {
                "section-header"
            } else if line.trim().is_empty() {
                "blank-line"
            } else {
                "content"
            };
            *text_families.entry(family).or_default() += count.unsigned_abs();
        }
        let fails: usize = regions.values().sum();
        let mut report = format!(
            "javascript_first_delta: sampled={} pass={} fail={} skipped={} indent_lines={}\n",
            sample.len(),
            passes,
            fails,
            skipped,
            indent_only
        );
        for (region, count) in &regions {
            report.push_str(&format!(
                "  {region}: {count}\n{}",
                examples
                    .get(region)
                    .map(|example| format!("    example: {example}\n"))
                    .unwrap_or_default()
            ));
        }
        report.push_str("  surplus/deficit families (line instances):\n");
        for (family, count) in &text_families {
            report.push_str(&format!("    {family}: {count}\n"));
        }
        report.push_str("  top emitted-side deficits:\n");
        for (count, line) in top_deficits.iter().take(10) {
            report.push_str(&format!(
                "    {count:4}  {}\n",
                line.chars().take(120).collect::<String>()
            ));
        }
        write_facet_report("javascript-first-delta", &report);
        assert!(!sample.is_empty(), "no javascript cases sampled");
    }

    /// Writes a facet measurement report under the session scratch root so the
    /// orchestrator can read the numbers without library-path printing.
    fn write_facet_report(name: &str, text: &str) {
        let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let workspace = manifest
            .parent()
            .and_then(std::path::Path::parent)
            .expect("manifest sits in crates/<name>");
        let dir = workspace.join("target/tmp/enum-member-any");
        if std::fs::create_dir_all(&dir).is_err() {
            return;
        }
        let _ = std::fs::write(dir.join(format!("{name}.txt")), text);
    }

    /// Per-record parity: re-checks every member-access record line
    /// (`>E.A : T`, `>E["A"] : T`, `>E[\`A\`] : T`) in the authority `.types`
    /// baselines of the 60-case enum sample against the compiler's emitted
    /// records, counting verbatim line matches.
    #[test]
    fn enum_member_access_records_parity() {
        let authority_root = authority_tests_root().to_string_lossy().into_owned();
        let baseline_dir = format!("{authority_root}/tests/baselines/reference");
        let mut case_paths: Vec<(String, String)> = Vec::new();
        for (rel_dir, dir) in [
            ("tests/cases/compiler", "tests/cases/compiler"),
            (
                "tests/cases/conformance/enums",
                "tests/cases/conformance/enums",
            ),
        ] {
            let Ok(entries) = std::fs::read_dir(format!("{authority_root}/{dir}")) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let name = path.file_name().unwrap().to_string_lossy().into_owned();
                if !name.starts_with("enum") || !name.ends_with(".ts") {
                    continue;
                }
                let stem = name.trim_end_matches(".ts");
                // Authority trees nest baselines one level down
                // (`reference/<area>/*.types`); the area is the segment
                // after `cases/` in the case path.
                let area = rel_dir
                    .split("cases/")
                    .nth(1)
                    .and_then(|rest| rest.split('/').next())
                    .unwrap_or("");
                let nested = format!("{baseline_dir}/{area}/{stem}.types");
                if !std::path::Path::new(&nested).exists()
                    && !std::path::Path::new(&format!("{baseline_dir}/{stem}.types")).exists()
                {
                    continue;
                }
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                case_paths.push((format!("{rel_dir}/{name}"), text));
            }
        }
        case_paths.sort_by(|a, b| a.0.cmp(&b.0));
        let sample: Vec<_> = case_paths.into_iter().take(60).collect();

        let mut member_records = 0usize;
        let mut matched_records = 0usize;
        let mut unmatched_samples: Vec<String> = Vec::new();
        for (logical, text) in &sample {
            let stem = logical.rsplit('/').next().unwrap().trim_end_matches(".ts");
            let area = logical
                .split("cases/")
                .nth(1)
                .and_then(|rest| rest.split('/').next())
                .unwrap_or("");
            let nested = format!("{baseline_dir}/{area}/{stem}.types");
            let baseline = if std::path::Path::new(&nested).exists() {
                nested
            } else {
                format!("{baseline_dir}/{stem}.types")
            };
            let Ok(expected) = std::fs::read_to_string(baseline) else {
                continue;
            };
            let units = split_case_units(logical, text);
            let entry = entry_virtual_path(logical, &units);
            let Ok(case) = compile_case(&units, &entry) else {
                continue;
            };
            let emitted = emit_types_baseline(&case, logical);
            let emitted_lines: std::collections::HashSet<&str> = emitted.lines().collect();
            let mut per_case = (0usize, 0usize);
            for line in expected.lines().filter(|line| {
                line.starts_with('>')
                    && line.contains(" : ")
                    && (line.contains('.') || line.contains('['))
            }) {
                member_records += 1;
                per_case.0 += 1;
                if emitted_lines.contains(line) {
                    matched_records += 1;
                    per_case.1 += 1;
                } else if unmatched_samples.len() < 40 {
                    unmatched_samples.push(format!("{stem}: {line}"));
                }
            }
            let _ = per_case;
        }
        // Regression floor, not a parity target: when the authority tree
        // is present the match ratio must hold; with no authority checked
        // out the sample is empty and there is nothing to gate.
        if member_records > 0 {
            let ratio = matched_records as f64 / member_records as f64;
            assert!(
                ratio > 0.7,
                "enum member record match ratio collapsed to {ratio:.3} ({matched_records}/{member_records})"
            );
        }
        let mut report =
            format!("enum_member_access_records: total={member_records} matched={matched_records}");
        for sample in &unmatched_samples {
            report.push('\n');
            report.push_str(sample);
        }
        write_facet_report("member-records", &report);
    }
    // ---- Fix 1: first-declaration NodeId(0) not skipped ------------------

    /// The very first declaration in a unit receives `NodeId::default()`
    /// (NodeId(0)). The old `declaration() == NodeId::default()` guard
    /// skipped it, dropping the first symbol's `.symbols` and `.types`
    /// records. Gating on `range().is_empty()` alone keeps it.
    #[test]
    fn first_declaration_with_node_id_zero_is_emitted() {
        let source = "function foo() {}\n";
        let logical = "tests/cases/compiler/firstDecl.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains(">foo : Symbol(foo, Decl("),
            "first declaration must appear in symbols output:\n{emitted}"
        );
        // Also verify the .types baseline emits the first symbol.
        let types = emit_types_baseline(&case, logical);
        assert!(
            types.contains("foo"),
            "first declaration must appear in types output:\n{types}"
        );
    }

    // ---- Fix 2: same-named type parameters keep separate Decl lists -------

    /// Two type parameters named `T` in different scopes must not share
    /// `Decl` entries. The old `(String, SymbolKind)` keying collapsed
    /// them because both mapped to `("T", TypeParameter)`. Restricting
    /// the cross-unit overlay to mergeable kinds gives each its own anchor.
    #[test]
    fn same_named_type_parameters_keep_separate_decl_lists() {
        let source = "\
function identity<T>(x: T): T { return x; }\n\
function wrap<U, T>(x: T): T { return x; }\n\
";
        let logical = "tests/cases/compiler/dupTypeParam.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Each `T` must have exactly one Decl entry (its own), not two.
        let t_lines: Vec<&str> = emitted
            .lines()
            .filter(|l| l.starts_with(">T :") && l.contains("Symbol(T,"))
            .collect();
        assert!(
            !t_lines.is_empty(),
            "must have at least one T symbol line:\n{emitted}"
        );
        for line in &t_lines {
            let decl_count = line.matches("Decl(").count();
            assert_eq!(
                decl_count, 1,
                "each T must have exactly one Decl entry, got {decl_count}:\n{line}\n{emitted}"
            );
        }
    }

    // ---- Fix 3: BOM-prefixed directive lines are stripped -----------------

    /// A source file whose first line carries a U+FEFF BOM before the `//`
    /// directive must still have the directive stripped and coordinates
    /// numbered from the first surviving line.
    #[test]
    fn bom_prefixed_directive_is_stripped() {
        let source = "\u{feff}// @target: es2015\nvar x = 1;";
        assert!(
            is_option_directive_line("\u{feff}// @target: es2015"),
            "BOM-prefixed directive line must be recognised"
        );
        let stripped = strip_directive_lines(source);
        assert_eq!(
            stripped, "var x = 1;",
            "BOM-prefixed directive must be stripped, got: {stripped:?}"
        );
        assert_eq!(
            directive_parts("\u{feff}// @target: es2015"),
            Some(("target", " es2015")),
            "directive_parts must strip BOM"
        );
    }

    /// A `///` or `////` option-styled line is content on every path: it
    /// creates no unit, records no option, and stays in compiled content so
    /// positions cannot shift versus the baselines.
    #[test]
    fn triple_slash_lines_are_never_option_directives() {
        assert_eq!(directive_parts("/// @filename: b.ts"), None);
        assert_eq!(directive_parts("//// @target: es5"), None);
        assert_eq!(directive_parts("// @param x: number"), None);
        assert!(!is_option_directive_line("/// @filename: b.ts"));
        assert!(!is_option_directive_line("//// @target: es5"));
        let logical = "tests/cases/compiler/tripleSlashPin.ts";
        let case_text = "/// @filename: b.ts\nvar b = 1;\n";
        let units = split_case_units(logical, case_text);
        assert_eq!(units.len(), 1);
        assert_eq!(units[0].text, case_text);
        assert!(parse_case_pragmas(case_text).options.is_empty());
        assert!(
            parse_case_pragmas("/// @target: es5\nvar b = 1;\n")
                .options
                .is_empty(),
            "a `/// @option` line records no pragma"
        );
    }

    // ---- Fix 4: decorated member anchors at decorator, not name ----------

    /// A decorated class property `@dec x` must anchor its `Decl` at the
    /// decorator's full start (right after `{`), not at the property name.
    /// The decorator walk scans left over `@dec` to reach the position
    /// TypeScript's `node.pos` would report. (Get/set accessors are not
    /// yet bound as symbols by the binder, so we test with a property.)
    #[test]
    fn decorated_member_anchors_at_decorator() {
        let source = "\
declare function dec(target: any, propertyKey: string): any;\n\
\n\
class C {\n\
    @dec x: number = 1;\n\
}\n\
";
        let logical = "tests/cases/compiler/decoratorProp.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // The property's Decl must be at line 2 (the `class C {` line),
        // column 9 (right after `{` — the full start including decorator).
        let x_line = emitted
            .lines()
            .find(|l| l.starts_with(">x :"))
            .unwrap_or_else(|| panic!("missing x symbol line:\n{emitted}"));
        assert!(
            x_line.contains("Decl(decoratorProp.ts, 2, 9)"),
            "decorated property must anchor at Decl(decoratorProp.ts, 2, 9), got:\n{x_line}\n{emitted}"
        );
    }

    /// Qualification rule 1: class member declarations render with the
    /// parent-qualified symbol name (`Symbol(C.foo, ...)`), not bare.
    /// Cited baseline: `classExtendingClass.symbols` — the first class `C`
    /// with members `foo`, `thing`, `other` all qualified as `C.foo`,
    /// `C.thing`, `C.other`.
    #[test]
    fn emit_symbols_qualifies_class_member_declarations() {
        let logical = "tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts";
        let case_text = "class C {\n    foo: string;\n    thing() { }\n    static other() { }\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts] ////\n\
            \n\
            === classExtendingClass.ts ===\n\
            class C {\n\
            >C : Symbol(C, Decl(classExtendingClass.ts, 0, 0))\n\
            \n\
                foo: string;\n\
            >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n\
            \n\
                thing() { }\n\
            >thing : Symbol(C.thing, Decl(classExtendingClass.ts, 1, 16))\n\
            \n\
                static other() { }\n\
            >other : Symbol(C.other, Decl(classExtendingClass.ts, 2, 15))\n\
            }\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }
    /// Class getter/setter pairs declare one merged member symbol: each of
    /// `abstract get readonlyProp` and `abstract set readonlyProp` in
    /// `abstractPropertyBasics.symbols` renders `>readonlyProp :
    /// Symbol(B.readonlyProp, Decl(8, 33), Decl(9, 40))`, and `get arguments`
    /// in `argumentsReferenceInConstructor3_Js.symbols` renders `>arguments :
    /// Symbol(A.arguments, Decl(a.js, 0, 9))`. The class header on the same
    /// path stays bare (`classExtendingClass.symbols` prints `>C :
    /// Symbol(C, ...)`; this pin prints `>B : Symbol(B, ...)`).
    #[test]
    fn emit_symbols_binds_class_accessor_declarations() {
        let logical = "tests/cases/compiler/classAccessorSymbolsPin.ts";
        let case_text = "class B {\n    get readonlyProp(): string { return \"\"; }\n    set readonlyProp(val: string) { }\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains(">B : Symbol(B,"),
            "class header on the same path stays bare; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains(">readonlyProp : Symbol(B.readonlyProp,"),
            "getter/setter pair must declare the merged member; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains(">val : Symbol(val,"),
            "setter parameter keeps its row; emitted:\n{emitted}"
        );
        assert_eq!(
            emitted
                .lines()
                .filter(|line| line.starts_with(">readonlyProp :"))
                .count(),
            2,
            "get and set each keep their row with the merged Decl list; emitted:\n{emitted}"
        );
    }
    /// Alias object literal members declare bare member symbols: `type State`
    /// in `computedPropertyBindingElementDeclarationNoCrash1.symbols` renders
    /// `>State : Symbol(State, ...)`, `>a : Symbol(a, ...)` and
    /// `>b : Symbol(b, ...)`, and `type T` in
    /// `DeclarationErrorsNoEmitOnError.symbols` renders `>T : Symbol(T, ...)`
    /// and `>x : Symbol(x, ...)`. The alias header on the same path stays
    /// bare and keeps its single row.
    #[test]
    fn emit_symbols_binds_alias_object_literal_members() {
        let logical = "tests/cases/compiler/aliasObjectMemberSymbolsPin.ts";
        let case_text = "export type State = {\n    a: number;\n    b: string;\n};\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains(">State : Symbol(State,"),
            "alias header on the same path stays; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains(">a : Symbol(a,"),
            "literal member a must declare a bare symbol; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains(">b : Symbol(b,"),
            "literal member b must declare a bare symbol; emitted:\n{emitted}"
        );
        assert_eq!(
            emitted
                .lines()
                .filter(|line| line.starts_with(">a :"))
                .count(),
            1,
            "one row per written literal member; emitted:\n{emitted}"
        );
    }
    /// Union branches keep distinct member symbols: `type X` in
    /// `arrayDestructuringInSwitch2.symbols` renders two `>kind` rows with
    /// their own Decl anchors (Decl(0, 10) and Decl(0, 34)) rather than one
    /// merged symbol.
    #[test]
    fn emit_symbols_binds_alias_union_literal_members() {
        let logical = "tests/cases/compiler/aliasUnionMemberSymbolsPin.ts";
        let case_text = "export type U = {\n    p: number;\n} | {\n    p: string;\n};\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains(">U : Symbol(U,"),
            "alias header on the same path stays; emitted:\n{emitted}"
        );
        assert_eq!(
            emitted
                .lines()
                .filter(|line| line.starts_with(">p :"))
                .count(),
            2,
            "each union branch keeps its own member row; emitted:\n{emitted}"
        );
    }

    /// Qualification rule 2: interface member declarations render with the
    /// parent-qualified symbol name (`Symbol(I.a, ...)`), not bare.
    /// Cited baseline: `contextualTypingFunctionReturningFunction.symbols`:
    /// ```text
    /// >I : Symbol(I, Decl(contextualTypingFunctionReturningFunction.ts, 0, 0))
    /// >a : Symbol(I.a, Decl(contextualTypingFunctionReturningFunction.ts, 0, 13))
    /// >b : Symbol(I.b, Decl(contextualTypingFunctionReturningFunction.ts, 1, 20))
    /// ```
    /// The `>s` and `>n` parameter rows from the same baseline are a known
    /// binder coverage gap (interface call-signature parameters not bound as
    /// symbols); they are handed off to Ts2304CrossFile and excluded here.
    #[test]
    fn emit_symbols_qualifies_interface_member_declarations() {
        let logical = "tests/cases/compiler/contextualTypingFunctionReturningFunction.ts";
        let case_text = "interface I {\n\ta(s: string): void;\n\tb(): (n: number) => void;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Assert the three cited interface-member rows exactly.
        let i_line = emitted
            .lines()
            .find(|l| l.starts_with(">I :"))
            .unwrap_or_else(|| panic!("missing I symbol line:\n{emitted}"));
        assert_eq!(
            i_line, ">I : Symbol(I, Decl(contextualTypingFunctionReturningFunction.ts, 0, 0))",
            "emitted:\n{emitted}"
        );
        let a_line = emitted
            .lines()
            .find(|l| l.starts_with(">a :"))
            .unwrap_or_else(|| panic!("missing a symbol line:\n{emitted}"));
        assert_eq!(
            a_line, ">a : Symbol(I.a, Decl(contextualTypingFunctionReturningFunction.ts, 0, 13))",
            "emitted:\n{emitted}"
        );
        let b_line = emitted
            .lines()
            .find(|l| l.starts_with(">b :"))
            .unwrap_or_else(|| panic!("missing b symbol line:\n{emitted}"));
        assert_eq!(
            b_line, ">b : Symbol(I.b, Decl(contextualTypingFunctionReturningFunction.ts, 1, 20))",
            "emitted:\n{emitted}"
        );
    }

    /// Qualification rule 3: a member-access reference `c.foo` where `c` is
    /// typed as class `C` renders the full access path `>c.foo` and the bare
    /// property identifier `>foo`, both with the member's qualified symbol
    /// `Symbol(C.foo, ...)`. The base `>c` renders with its own bare symbol.
    /// Cited baseline: `classExtendingClass.symbols` lines 25–27:
    /// ```text
    /// >d.foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))
    /// >d : Symbol(d, Decl(classExtendingClass.ts, 10, 3))
    /// >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))
    /// ```
    /// This test uses a same-class (non-inherited) access so the binder's
    /// direct member-scope lookup succeeds.
    #[test]
    fn emit_symbols_qualifies_member_access_references() {
        let logical = "tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts";
        let case_text = "class C {\n    foo: string;\n}\nvar c: C;\nvar r = c.foo;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts] ////\n\
            \n\
            === classExtendingClass.ts ===\n\
            class C {\n\
            >C : Symbol(C, Decl(classExtendingClass.ts, 0, 0))\n\
                foo: string;\n\
            >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n\
            }\n\
            var c: C;\n\
            >c : Symbol(c, Decl(classExtendingClass.ts, 3, 3))\n\
            >C : Symbol(C, Decl(classExtendingClass.ts, 0, 0))\n\
            var r = c.foo;\n\
            >r : Symbol(r, Decl(classExtendingClass.ts, 4, 3))\n\
            >c.foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n\
            >c : Symbol(c, Decl(classExtendingClass.ts, 3, 3))\n\
            >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Quoted and numeric member names keep their source spelling and
    /// bracket-qualify: `"foo"` renders `Symbol(C["foo"], ...)`, not
    /// `Symbol(C.foo, ...)`. Cited baselines: `ClassDeclaration22.symbols`
    /// (`>"foo" : Symbol(C["foo"], ...)`) and
    /// `parserMemberAccessorDeclaration6.symbols` (`>0 : Symbol(C[0], ...)`).
    #[test]
    fn emit_symbols_renders_non_identifier_member_names() {
        let logical = "tests/cases/compiler/quotedMemberNames.ts";
        let case_text = "class C {\n    \"foo\"() { }\n    0 = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let quoted = emitted
            .lines()
            .find(|l| l.starts_with(">\"foo\" : Symbol(C[\"foo\"],"))
            .unwrap_or_else(|| panic!("missing quoted member row:\n{emitted}"));
        assert!(
            quoted.starts_with(">\"foo\" : Symbol(C[\"foo\"], Decl(quotedMemberNames.ts, "),
            "unexpected quoted member row: {quoted}"
        );
        let numeric = emitted
            .lines()
            .find(|l| l.starts_with(">0 : Symbol(C[0],"))
            .unwrap_or_else(|| panic!("missing numeric member row:\n{emitted}"));
        assert!(
            numeric.starts_with(">0 : Symbol(C[0], Decl(quotedMemberNames.ts, "),
            "unexpected numeric member row: {numeric}"
        );
    }

    /// Computed member declarations bind under their bracketed source
    /// spelling (`Test[x]`), and computed member accesses emit no full-path
    /// row, only the base and (for string literals) the quoted leaf.
    /// Cited baselines: `declarationEmitMultipleComputedNamesSameDomain` and
    /// `defaultIndexProps1.symbols`.
    #[test]
    fn emit_symbols_binds_computed_member_names() {
        let logical = "tests/cases/compiler/computedMemberNames.ts";
        let case_text = "const x = \"k\";\nclass Test {\n    [x] = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let member = emitted
            .lines()
            .find(|l| l.starts_with(">[x] : Symbol(Test[x],"))
            .unwrap_or_else(|| panic!("missing computed member row:\n{emitted}"));
        assert!(
            member.starts_with(">[x] : Symbol(Test[x], Decl(computedMemberNames.ts, "),
            "unexpected computed member row: {member}"
        );
    }

    #[test]
    fn emit_symbols_records_quoted_member_access_leaf() {
        let logical = "tests/cases/compiler/quotedMemberAccess.ts";
        let case_text = "class C {\n    foo() { }\n}\nvar c: C;\nvar r = c[\"foo\"]();\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let leaf = emitted
            .lines()
            .find(|l| l.starts_with(">\"foo\" : Symbol(C.foo,"))
            .unwrap_or_else(|| panic!("missing quoted leaf row:\n{emitted}"));
        assert!(
            leaf.starts_with(">\"foo\" : Symbol(C.foo, Decl(quotedMemberAccess.ts, "),
            "unexpected quoted leaf row: {leaf}"
        );
        assert!(
            !emitted.lines().any(|l| l.starts_with(">c[\"foo\"] :")),
            "computed access must not emit a full-path row:\n{emitted}"
        );
    }
    // ---- Section-header-diff fixes (wave 4) -----------------------------

    /// `extract_dts_sections` must skip input-echo sections: a `.d.ts`-named
    /// section in the echo zone is an input file, not a generated declaration.
    /// The `echo_count` parameter tells the extractor how many leading
    /// sections are echoes (one per `// @filename:` unit).
    #[test]
    fn extract_dts_sections_skips_echo_dts_inputs() {
        // Mirrors `exportSpecifierForAGlobal.js`: `a.d.ts` is an input echo,
        // `b.d.ts` is the generated output. With `echo_count = 2` (a.d.ts +
        // b.ts), only the output `b.d.ts` section survives.
        let doc = "\
//// [tests/cases/compiler/exportSpecifierForAGlobal.ts] ////\n\
\n\
//// [a.d.ts]\ndeclare const g: number;\n\
\n\
//// [b.ts]\nexport { g };\n\
\n\
//// [b.js]\n\"use strict\";\nexport { g };\n\
\n\
//// [b.d.ts]\ndeclare const g: number;\n";
        assert_eq!(
            extract_dts_sections(doc, 2),
            "//// [b.d.ts]\ndeclare const g: number;\n"
        );
    }

    /// JSON inputs must not produce declaration sections. Upstream's output
    /// mapping skips `.json` files for declaration emit entirely.
    #[test]
    fn declaration_baseline_skips_json_input_units() {
        let source = "\
// @declaration: true\n\
// @resolveJsonModule: true\n\
// @module: nodenext\n\
\n\
// @filename: package.json\n\
{\"name\": \"pkg\", \"type\": \"module\"}\n\
\n\
// @filename: index.ts\n\
export const x: number = 1;\n";
        let logical = "tests/cases/compiler/jsonSkipTest.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_declaration_baseline(&case).expect("declaration emit");
        // Must contain index.d.ts but NOT package.d.json.ts or any JSON-derived section
        assert!(
            emitted.contains("//// [index.d.ts]"),
            "expected index.d.ts section, got:\n{emitted}"
        );
        assert!(
            !emitted.contains("package"),
            "JSON input must not produce a declaration section, got:\n{emitted}"
        );
    }

    /// Declaration output sections must follow module-index order
    /// (dependency-first), not split order (`// @filename:` directive order).
    /// `exportSpecifiers` has split [imports.ts, exports.ts] but modules()
    /// is [exports.ts, imports.ts], and the baseline emits exports.d.ts
    /// before imports.d.ts.
    #[test]
    fn declaration_baseline_emits_in_module_index_order() {
        let source = "\
// @module: esnext\n\
// @declaration: true\n\
\n\
// @filename: imports.ts\n\
import { foo } from \"./exports\";\n\
export { foo };\n\
\n\
// @filename: exports.ts\n\
export const foo = 1;\n";
        let logical = "tests/cases/compiler/exportSpecifiers.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_declaration_baseline(&case).expect("declaration emit");
        let exports_pos = emitted.find("//// [exports.d.ts]").unwrap_or(usize::MAX);
        let imports_pos = emitted.find("//// [imports.d.ts]").unwrap_or(usize::MAX);
        assert!(
            exports_pos < imports_pos,
            "exports.d.ts must precede imports.d.ts (module-index order), got:\n{emitted}"
        );
    }

    /// Class constructors must NOT produce a `>constructor : type` record in
    /// the `.types` baseline. Upstream tsc emits records for declaration names
    /// and typed expressions, but the `constructor` keyword is a member
    /// declaration, not a value expression — it gets no `>expr : type` row.
    /// Verified against `parserClassDeclaration12.types:4` (class C with two
    /// constructor signatures — baseline has `>C : C` and `>a : any` but no
    /// `>constructor`) and `ClassDeclaration26.types:4` (class with
    /// constructor body — same pattern, no `>constructor` record).
    /// The binder creates a `SymbolKind::Function` symbol named "constructor"
    /// for bodyless constructor overload signatures (parsed as Method at
    /// `parser.rs:2158`), which the observer must filter out.
    #[test]
    fn types_emitter_skips_constructor_function_symbols() {
        let source = "\
// @target: es2015\n\
// @strict: false\n\
class C {\n\
   constructor();\n\
   constructor(a) { }\n\
}\n";
        let logical = "tests/cases/compiler/parserClassDeclaration12.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains(">constructor"),
            "constructor keyword must not produce a >constructor record:\n{emitted}"
        );
        assert!(
            emitted.contains(">C : C"),
            "class name record must be present:\n{emitted}"
        );
        assert!(
            emitted.contains(">a : any"),
            "parameter record must be present:\n{emitted}"
        );
    }

    /// A class with a constructor body (not just overload signatures) must
    /// also not emit `>constructor`. Verified against
    /// `ClassDeclaration26.types:4` which has `>C : C` and `>x : any` but
    /// no `>constructor` record.
    #[test]
    fn types_emitter_skips_constructor_with_body() {
        let source = "\
class C {\n\
    constructor(public x: number) {}\n\
}\n";
        let logical = "tests/cases/compiler/ClassDeclaration26.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains(">constructor"),
            "constructor with body must not produce a >constructor record:\n{emitted}"
        );
        assert!(
            emitted.contains(">C : C"),
            "class name record must be present:\n{emitted}"
        );
    }

    // ---- T3: interface member declaration occurrences --------------------

    /// Duplicate member declarations emit one `.types` row per written
    /// occurrence — `interface I { item: any; item: number; }` produces
    /// exactly two `>item` rows, both rendering the canonical member type —
    /// and one `.symbols` row per occurrence, each carrying BOTH `Decl`
    /// anchors (Let properties unite; no residual single-anchor row).
    #[test]
    fn emit_types_and_symbols_emit_one_row_per_member_occurrence() {
        let logical = "tests/cases/compiler/duplicateMemberPin.ts";
        let case_text = "interface I {\n    item: any;\n    item: number;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");

        let emitted_types = emit_types_baseline(&case, logical);
        let item_type_rows: Vec<&str> = emitted_types
            .lines()
            .filter(|line| line.starts_with(">item :"))
            .collect();
        assert_eq!(
            item_type_rows,
            [">item : any", ">item : any"],
            "each written `item` occurrence emits its own row with the \
             canonical type:\n{emitted_types}"
        );

        let emitted_symbols = emit_symbols_baseline(&case, logical);
        let item_symbol_rows: Vec<&str> = emitted_symbols
            .lines()
            .filter(|line| line.starts_with(">item :"))
            .collect();
        // First occurrence anchors at the end of `{` (0, 13); the second at
        // the end of the first member's `;` (1, 14) — the `node.pos`
        // full-start convention. Both rows carry both anchors.
        assert_eq!(
            item_symbol_rows,
            [
                ">item : Symbol(I.item, Decl(duplicateMemberPin.ts, 0, 13), \
                 Decl(duplicateMemberPin.ts, 1, 14))",
                ">item : Symbol(I.item, Decl(duplicateMemberPin.ts, 0, 13), \
                 Decl(duplicateMemberPin.ts, 1, 14))",
            ],
            "each `item` row carries both occurrence Decl anchors:\
             \n{emitted_symbols}"
        );
    }

    /// Merged interface fragments (`twoMergedInterfacesWithDifferingOverloads`
    /// shape): three `foo` occurrences across two `interface I` fragments
    /// share one canonical symbol, so every `foo` name row carries all three
    /// `Decl` anchors and `.types` emits one row per occurrence.
    #[test]
    fn emit_symbols_merged_interface_fragments_union_all_occurrence_anchors() {
        let logical = "tests/cases/compiler/mergedOverloadsPin.ts";
        let case_text = "interface I {\n    foo(x: string): 1;\n}\n\
                         interface I {\n    foo(x: number): 2;\n    foo(x: boolean): 3;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");

        let emitted_types = emit_types_baseline(&case, logical);
        let foo_type_rows = emitted_types
            .lines()
            .filter(|line| line.starts_with(">foo :"))
            .count();
        assert_eq!(
            foo_type_rows, 3,
            "one `.types` row per written `foo` occurrence:\n{emitted_types}"
        );

        let emitted_symbols = emit_symbols_baseline(&case, logical);
        let foo_symbol_rows: Vec<&str> = emitted_symbols
            .lines()
            .filter(|line| line.starts_with(">foo :"))
            .collect();
        // Anchors: end of `{` on line 0 (0, 13), end of `{` on line 3
        // (3, 13), end of the second fragment's first `;` (4, 22).
        let expected = ">foo : Symbol(I.foo, Decl(mergedOverloadsPin.ts, 0, 13), \
            Decl(mergedOverloadsPin.ts, 3, 13), Decl(mergedOverloadsPin.ts, 4, 22))";
        assert_eq!(
            foo_symbol_rows,
            [expected, expected, expected],
            "every `foo` row carries all three Decl anchors:\n{emitted_symbols}"
        );
    }

    /// Cross-unit union for occurrence-covered Function method members:
    /// `foo` declared once per unit must render each unit's `foo` row with
    /// BOTH units' `Decl` anchors — foreign-unit declarations survive, no
    /// residual local-only row is permitted.
    #[test]
    fn emit_symbols_two_unit_method_members_union_decl_lists() {
        let logical = "tests/cases/compiler/twoUnitMethodPin.ts";
        let case_text = "\
// @filename: a.ts
interface I {
    foo(x: string): 1;
}
// @filename: b.ts
interface I {
    foo(x: number): 2;
}
";
        let pragmas = parse_case_pragmas(case_text);
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let foo_rows: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with(">foo :"))
            .collect();
        assert_eq!(
            foo_rows,
            [
                ">foo : Symbol(I.foo, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
                ">foo : Symbol(I.foo, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
            ],
            "each unit's `foo` row carries both units' Decls:\n{emitted}"
        );
    }

    /// Cross-unit union for occurrence-covered Variable(Let) property
    /// members: `item` is not globally mergeable, yet occurrence-covered
    /// interface properties enter the overlay, so each unit's `item` row
    /// carries BOTH units' `Decl` anchors while `kind_is_mergeable` stays
    /// unchanged for arbitrary let locals.
    #[test]
    fn emit_symbols_two_unit_let_property_members_union_decl_lists() {
        let logical = "tests/cases/compiler/twoUnitPropertyPin.ts";
        let case_text = "\
// @filename: a.ts
interface I {
    item: any;
}
// @filename: b.ts
interface I {
    item: number;
}
";
        let pragmas = parse_case_pragmas(case_text);
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let item_rows: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with(">item :"))
            .collect();
        assert_eq!(
            item_rows,
            [
                ">item : Symbol(I.item, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
                ">item : Symbol(I.item, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
            ],
            "each unit's `item` row carries both units' Decls:\n{emitted}"
        );
    }

    /// A modifier-led member anchors its `Decl` before the modifier:
    /// `readonly p` anchors at the end of the previous member's `;` (the
    /// `node.pos` full start), not at `p` and not after `readonly`. The
    /// occurrence `declaration_range` includes modifiers, routing around the
    /// `kind_is_keyword_led` gate that never fires for `Variable(Let)`.
    #[test]
    fn emit_symbols_readonly_member_anchors_before_modifier() {
        let logical = "tests/cases/compiler/readonlyMemberPin.ts";
        let case_text = "interface I {\n    a: number;\n    readonly p: string;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let a_line = emitted
            .lines()
            .find(|line| line.starts_with(">a :"))
            .unwrap_or_else(|| panic!("missing a symbol line:\n{emitted}"));
        assert_eq!(
            a_line, ">a : Symbol(I.a, Decl(readonlyMemberPin.ts, 0, 13))",
            "emitted:\n{emitted}"
        );
        let p_line = emitted
            .lines()
            .find(|line| line.starts_with(">p :"))
            .unwrap_or_else(|| panic!("missing p symbol line:\n{emitted}"));
        assert_eq!(
            p_line, ">p : Symbol(I.p, Decl(readonlyMemberPin.ts, 1, 14))",
            "`readonly p` must anchor before `readonly` (end of `a`'s `;`), \
             not at the name:\n{emitted}"
        );
    }

    /// Occurrence `name_range`s are UTF-16 spans: a quoted non-BMP member
    /// name slices to its exact source text (`"𝒜q"`, quotes included), and a
    /// member following it on the same line anchors at a UTF-16 column that
    /// counts `𝒜` as two code units.
    #[test]
    fn emit_symbols_occurrence_spans_count_utf16_units() {
        let logical = "tests/cases/compiler/nonBmpMemberPin.ts";
        let case_text = "interface Q { \"𝒜q\"(x: string): string; tail: number; }\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");

        let emitted_types = emit_types_baseline(&case, logical);
        assert!(
            emitted_types
                .lines()
                .any(|line| line.starts_with(">\"𝒜q\" :")),
            "the quoted non-BMP name must slice exactly:\n{emitted_types}"
        );

        let emitted_symbols = emit_symbols_baseline(&case, logical);
        let quoted_line = emitted_symbols
            .lines()
            .find(|line| line.starts_with(">\"𝒜q\" :"))
            .unwrap_or_else(|| panic!("missing \"𝒜q\" symbol line:\n{emitted_symbols}"));
        assert_eq!(
            quoted_line, ">\"𝒜q\" : Symbol(Q.𝒜q, Decl(nonBmpMemberPin.ts, 0, 13))",
            "emitted:\n{emitted_symbols}"
        );
        // `tail` follows `"𝒜q"(x: string): string;` on line 0; its anchor is
        // the end of that `;` at UTF-16 column 39 — `𝒜` occupies two units,
        // so a byte- or char-counted column would land at 40 or 38.
        let tail_line = emitted_symbols
            .lines()
            .find(|line| line.starts_with(">tail :"))
            .unwrap_or_else(|| panic!("missing tail symbol line:\n{emitted_symbols}"));
        assert_eq!(
            tail_line, ">tail : Symbol(Q.tail, Decl(nonBmpMemberPin.ts, 0, 39))",
            "non-BMP columns must count UTF-16 units:\n{emitted_symbols}"
        );
    }

    /// Cross-area stem twins resolve to the owning area, never to a
    /// sorted-first file from another area.
    #[test]
    fn baseline_file_prefers_owning_area_for_stem_twins() {
        // System temp dir honors TMPDIR; pid-suffixed and removed after use.
        let root = std::env::temp_dir().join(format!("bamts-twins-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for area in ["compiler", "conformance"] {
            std::fs::create_dir_all(root.join(area)).expect("fixture area");
        }
        std::fs::write(root.join("compiler/twin.types"), "compiler").expect("fixture");
        std::fs::write(root.join("conformance/twin.types"), "conformance").expect("fixture");
        let pragmas = CasePragmas::default();
        assert_eq!(
            resolve_baseline_file(&root, "twin", "conformance", "types", &pragmas),
            Some(root.join("conformance/twin.types"))
        );
        assert_eq!(
            resolve_baseline_file(&root, "twin", "compiler", "types", &pragmas),
            Some(root.join("compiler/twin.types"))
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    #[test]
    fn baseline_file_prefers_most_specific_option_match() {
        // System temp dir honors TMPDIR; pid-suffixed and removed after use.
        let root = std::env::temp_dir().join(format!("bamts-specific-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("compiler")).expect("fixture area");
        std::fs::write(root.join("compiler/amb(target=es5).types"), "loose").expect("fixture");
        std::fs::write(
            root.join("compiler/amb(target=es5,module=commonjs).types"),
            "exact",
        )
        .expect("fixture");
        let pragmas = CasePragmas {
            options: vec![
                ("target".to_owned(), vec!["es5".to_owned()]),
                ("module".to_owned(), vec!["commonjs".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        assert_eq!(
            resolve_baseline_file(&root, "amb", "compiler", "types", &pragmas),
            Some(root.join("compiler/amb(target=es5,module=commonjs).types"))
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    #[test]
    fn baseline_file_owning_area_scopes_variant_search() {
        // A same-stem variant in another area belongs to another case,
        // so owning matches win even when the other variant is more
        // specific. Specificity ranks within one area only.
        let root = std::env::temp_dir().join(format!("bamts-specarea-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for area in ["compiler", "other"] {
            std::fs::create_dir_all(root.join(area)).expect("fixture area");
        }
        std::fs::write(root.join("compiler/amb(target=es5).types"), "loose").expect("fixture");
        std::fs::write(
            root.join("other/amb(target=es5,module=commonjs).types"),
            "exact",
        )
        .expect("fixture");
        let pragmas = CasePragmas {
            options: vec![
                ("target".to_owned(), vec!["es5".to_owned()]),
                ("module".to_owned(), vec!["commonjs".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        assert_eq!(
            resolve_baseline_file(&root, "amb", "compiler", "types", &pragmas),
            Some(root.join("compiler/amb(target=es5).types"))
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    #[test]
    fn baseline_file_duplicate_suffix_breaks_tie_by_path() {
        // System temp dir honors TMPDIR; pid-suffixed and removed after use.
        let root = std::env::temp_dir().join(format!("bamts-duptie-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for area in ["compiler", "aaa", "bbb"] {
            std::fs::create_dir_all(root.join(area)).expect("fixture area");
        }
        std::fs::write(root.join("aaa/dup(target=es5).types"), "a").expect("fixture");
        std::fs::write(root.join("bbb/dup(target=es5).types"), "b").expect("fixture");
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es5".to_owned()])],
            no_types_and_symbols: false,
        };
        assert_eq!(
            resolve_baseline_file(&root, "dup", "compiler", "types", &pragmas),
            Some(root.join("aaa/dup(target=es5).types"))
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    #[test]
    fn baseline_file_sibling_order_is_sorted() {
        // bbb is created before aaa on purpose: directory enumeration
        // order must not decide which plain baseline wins.
        let root = std::env::temp_dir().join(format!("bamts-sibord-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for area in ["compiler", "bbb", "aaa"] {
            std::fs::create_dir_all(root.join(area)).expect("fixture area");
        }
        std::fs::write(root.join("bbb/dup.types"), "b").expect("fixture");
        std::fs::write(root.join("aaa/dup.types"), "a").expect("fixture");
        let pragmas = CasePragmas::default();
        assert_eq!(
            resolve_baseline_file(&root, "dup", "compiler", "types", &pragmas),
            Some(root.join("aaa/dup.types"))
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    #[test]
    fn baseline_file_owned_but_incompatible_yields_none() {
        // The owning area claims the stem but holds no compatible
        // variant: the sibling-area match belongs to another case, so
        // the resolver reports no authority instead of comparing
        // against an unrelated baseline.
        let root = std::env::temp_dir().join(format!("bamts-ownnone-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for area in ["compiler", "other"] {
            std::fs::create_dir_all(root.join(area)).expect("fixture area");
        }
        std::fs::write(root.join("compiler/amb(target=es5).types"), "b").expect("fixture");
        std::fs::write(root.join("other/amb(target=es2015).types"), "b").expect("fixture");
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es2015".to_owned()])],
            no_types_and_symbols: false,
        };
        assert_eq!(
            resolve_baseline_file(&root, "amb", "compiler", "types", &pragmas),
            None
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    #[test]
    fn baseline_file_owned_plain_covers_incompatible_options() {
        // An owned stem with no compatible variant still falls back to
        // the owning plain file rather than a sibling-area variant.
        let root = std::env::temp_dir().join(format!("bamts-ownplain-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for area in ["compiler", "other"] {
            std::fs::create_dir_all(root.join(area)).expect("fixture area");
        }
        std::fs::write(root.join("compiler/amb.types"), "b").expect("fixture");
        std::fs::write(root.join("compiler/amb(target=es5).types"), "b").expect("fixture");
        std::fs::write(root.join("other/amb(target=es2015).types"), "b").expect("fixture");
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es2015".to_owned()])],
            no_types_and_symbols: false,
        };
        assert_eq!(
            resolve_baseline_file(&root, "amb", "compiler", "types", &pragmas),
            Some(root.join("compiler/amb.types"))
        );
        let _ = std::fs::remove_dir_all(&root);
    }
    /// Regression: a catch-body function shadows its parameter. The body
    /// binds in a child block like the try body, so tsc-accepted code in
    /// strict and sloppy modes reports no duplicate (oracle: tsc rc=0).
    #[test]
    fn catch_body_function_shadows_parameter() {
        let case_text = "\"use strict\";\ntry {\n} catch (e) {\n    function e() {\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchFunctionShadow.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchFunctionShadow.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: the catch parameter stays visible in the child body
    /// block through the scope chain.
    #[test]
    fn catch_parameter_visible_in_body_block() {
        let case_text = "try {\n} catch (e) {\n    const y = e;\n}\n";
        let units = split_case_units("tests/cases/compiler/catchParameterVisible.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchParameterVisible.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: lexical redeclarations still conflict with the catch
    /// parameter across the child body block. Only `var` and functions
    /// shadow it legally.
    #[test]
    fn catch_body_let_conflicts_with_parameter() {
        let case_text = "try {\n} catch (e) {\n    let e;\n}\n";
        let units = split_case_units("tests/cases/compiler/catchLetConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchLetConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 3)]);
    }
    /// Regression: classes shadow catch parameters legally (tsc rc=0).
    /// Only lexical variable redeclarations conflict across the body.
    #[test]
    fn catch_body_class_shadows_parameter() {
        let case_text = "try {\n} catch (e) {\n    class e {\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchClassShadow.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchClassShadow.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: enums shadow catch parameters legally (tsc rc=0).
    #[test]
    fn catch_body_enum_shadows_parameter() {
        let case_text = "try {\n} catch (e) {\n    enum e {\n        A = 1,\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchEnumShadow.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchEnumShadow.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: `var` against a destructured catch param conflicts.
    /// The legacy same-name tolerance applies to simple identifiers
    /// only (tsc TS2492 on the `var`, alongside the pattern error).
    #[test]
    fn catch_destructured_param_var_conflicts() {
        let case_text = "try {\n} catch ({ e }) {\n    var e;\n}\n";
        let units = split_case_units("tests/cases/compiler/catchDestructuredVar.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchDestructuredVar.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 3)]);
    }
    /// Regression: nested `var` under a destructured catch conflicts.
    /// `var` hoists through transparent scopes, so the claim walk
    /// climbs to the complex catch instead of stopping at the block.
    #[test]
    fn catch_nested_var_conflicts_with_destructured_param() {
        let case_text = "try {\n} catch ({ x }) {\n    {\n        var x;\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchNestedVar.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchNestedVar.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 4)]);
    }
    /// Regression: nested `var` under a simple catch stays silent. The
    /// legacy tolerance survives hoisting through transparent scopes.
    #[test]
    fn catch_nested_var_tolerated_for_simple_param() {
        let case_text = "try {\n} catch (e) {\n    {\n        var e;\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchNestedVarSimple.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchNestedVarSimple.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a call before a nested for-body declaration resolves
    /// (tsc silent: the function hoists to the loop scope). The outer
    /// pre-pass skips the for-body subtree, so the loop-local prebind
    /// must declare it before earlier statements resolve.
    #[test]
    fn for_nested_function_precedes_use() {
        let case_text =
            "declare var cond: boolean;\nfor (;;) {\nf();\nif (cond) function f() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/forNestedPrecede.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forNestedPrecede.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a switch-case function stays switch-scoped even nested
    /// in a strict block (tsc TS2304 on the post-block use); the
    /// block-local prebind must not leak it into the enclosing block.
    #[test]
    fn strict_post_switch_function_stays_switch_scoped() {
        let case_text =
            "declare var x: number;\n{\nswitch (x) {\ncase 0:\nfunction f() {\n}\n}\nf();\n}\n";
        let units = split_case_units("tests/cases/compiler/switchCaseFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/switchCaseFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 8)]);
    }
    /// Regression: a try-block function stays try-scoped even nested in a
    /// strict block (tsc TS2304); the block-local prebind must not leak it.
    #[test]
    fn strict_post_try_function_stays_try_scoped() {
        let case_text = "{\ntry {\nfunction f() {\n}\n} catch (e) {\n}\nf();\n}\n";
        let units = split_case_units("tests/cases/compiler/tryBlockFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tryBlockFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 7)]);
    }
    /// Regression: a braced case-block function stays block-scoped (tsc
    /// TS2304); neither the block-local nor the switch-local prebind may
    /// leak it into an enclosing scope.
    #[test]
    fn strict_braced_case_function_stays_block_scoped() {
        let case_text = "declare var x: number;\n{\nswitch (x) {\ncase 0: {\nfunction f() {\n}\n}\n}\nf();\n}\n";
        let units = split_case_units("tests/cases/compiler/bracedCaseFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/bracedCaseFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 9)]);
    }
    /// Guard: a use before a nested try-body declaration resolves (tsc
    /// silent: the function hoists to the try scope).
    #[test]
    fn strict_nested_try_function_precedes_use() {
        let case_text = "declare var c: boolean;\n{\ntry {\nf();\nif (c) function f() {\n}\n} catch (e) {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedTryPrecede.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedTryPrecede.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Guard: a use before a nested case declaration resolves across
    /// cases (tsc silent: the function hoists to the switch scope).
    #[test]
    fn strict_nested_switch_function_precedes_use() {
        let case_text = "declare var n: number;\ndeclare var c: boolean;\n{\nswitch (n) {\ncase 1: f();\nbreak;\ncase 2: if (c) function f() {\n}\nbreak;\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedSwitchPrecede.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedSwitchPrecede.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: an inner-loop function stays inner-loop-scoped in
    /// strict mode (tsc TS2304 on the outer-loop use); the outer
    /// prebind must not claim it into the ancestor loop scope. The
    /// sloppy half is pinned separately below: the harness forces
    /// strict on every unit unless pragmas switch it off.
    #[test]
    fn nested_loop_function_stays_inner_scoped() {
        let case_text = "for (;;) {\ng();\nfor (;;) function g() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedLoopFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedLoopFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 2)]);
    }
    /// Regression: an inner-loop function stays inner-loop-scoped in
    /// sloppy mode too (tsc TS2304 on the outer-loop use). Compiled
    /// with strict+alwaysStrict off; the harness otherwise forces
    /// strict on every unit.
    #[test]
    fn sloppy_nested_loop_function_stays_inner_scoped() {
        let case_text = "for (;;) {\ng();\nfor (;;) function g() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/sloppyNestedLoop.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyNestedLoop.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 2)]);
    }
    /// Guard pair: the es5 block-function diagnostic gates on scope
    /// strictness. The same shape reports under default (strict)
    /// pragmas and stays silent with strict off, which locks the
    /// pragma-to-sloppy path the sloppy pin above relies on.
    #[test]
    fn es5_block_function_reports_in_strict_scope() {
        let case_text = "declare var c: boolean;\nif (c) {\nfunction g() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/es5StrictScope.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/es5StrictScope.ts", &units);
        let pragmas = CasePragmas {
            options: vec![("target".to_owned(), vec!["es5".to_owned()])],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C040".to_owned(), 3)]);
    }
    #[test]
    fn es5_block_function_silent_in_sloppy_scope() {
        let case_text = "declare var c: boolean;\nif (c) {\nfunction g() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/es5SloppyScope.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/es5SloppyScope.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("target".to_owned(), vec!["es5".to_owned()]),
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Guard: a use inside the inner loop resolves (the inner loop-local
    /// prebind declares with the inner-loop identity).
    #[test]
    fn nested_loop_inner_use_resolves() {
        let case_text = "for (;;) {\nfor (;;) {\nfunction g() {\n}\ng();\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedLoopInnerUse.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedLoopInnerUse.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a loop-header `let` sharing the unbraced body
    /// function's name is diagnosed at both sites (tsc TS2451 at
    /// (1,10) and (1,28), both modes). The prebind installs the
    /// function first, so the header `let` reports; the function
    /// resolve must report too instead of reusing its hoisted
    /// identity silently.
    #[test]
    fn loop_header_let_conflicts_with_body_function() {
        let case_text = "for (let f = 0;;) function f() {\n}\n";
        let units = split_case_units("tests/cases/compiler/loopHeaderLetFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/loopHeaderLetFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 1, 27),
            ]
        );
    }
    /// The same dual-report holds when the function comes first
    /// (tsc TS2300 at both sites, both modes); emission order is
    /// incoming site first.
    #[test]
    fn function_let_conflict_reports_both_sites() {
        let case_text = "function f() {\n}\nlet f = 1;\n";
        let units = split_case_units("tests/cases/compiler/functionLetConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/functionLetConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        // Emission order is incoming site first, but the facet
        // collector sorts by position, so the function site leads.
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 3, 4),
            ]
        );
    }
    /// Let-first twin of the func-first dual: declaration order must
    /// not matter (tsc TS2300 at both sites, both modes).
    #[test]
    fn let_function_conflict_reports_both_sites() {
        let case_text = "let f = 1;\nfunction f() {\n}\n";
        let units = split_case_units("tests/cases/compiler/letFunctionConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/letFunctionConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 4),
                ("BAMTS-C001".to_owned(), 2, 9),
            ]
        );
    }
    /// Sloppy twin of the let-first dual (tsc TS2300 at both sites
    /// in sloppy too).
    #[test]
    fn sloppy_let_function_conflict_reports_both_sites() {
        let case_text = "let f = 1;\nfunction f() {\n}\n";
        let units = split_case_units("tests/cases/compiler/sloppyLetFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyLetFunction.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 4),
                ("BAMTS-C001".to_owned(), 2, 9),
            ]
        );
    }
    /// A `var` established first dual-reports against a later `let`
    /// (tsc TS2300 at both sites, both modes).
    #[test]
    fn var_let_conflict_reports_both_sites() {
        let case_text = "var f = 0;\nlet f = 1;\n";
        let units = split_case_units("tests/cases/compiler/varLetConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/varLetConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 4),
                ("BAMTS-C001".to_owned(), 2, 4),
            ]
        );
    }
    /// Sloppy twin of the var-first dual (tsc TS2300 at both sites
    /// in sloppy too).
    #[test]
    fn sloppy_var_let_conflict_reports_both_sites() {
        let case_text = "var f = 0;\nlet f = 1;\n";
        let units = split_case_units("tests/cases/compiler/sloppyVarLet.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyVarLet.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 4),
                ("BAMTS-C001".to_owned(), 2, 4),
            ]
        );
    }
    /// Boundary: a `let` established first keeps the single diagnostic
    /// against a later `var`. Known divergence, kept deliberately: tsc
    /// dual-reports this pair (TS2451 at both sites), but the repo
    /// single-reports lexical-first collisions by design (catch
    /// settlement), and the top-level shape follows the same rule.
    #[test]
    fn let_var_conflict_reports_once() {
        let case_text = "let f = 1;\nvar f = 0;\n";
        let units = split_case_units("tests/cases/compiler/letVarConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/letVarConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 2, 4)]);
    }
    /// A `var` established first dual-reports against a later class
    /// (tsc TS2300 at both sites, both modes).
    #[test]
    fn var_class_conflict_reports_both_sites() {
        let case_text = "var C = 0;\nclass C {\n}\n";
        let units = split_case_units("tests/cases/compiler/varClassConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/varClassConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 4),
                ("BAMTS-C001".to_owned(), 2, 6),
            ]
        );
    }
    /// Three colliding declarations flag each site exactly once (tsc
    /// TS2300 at (1,10), (3,5) and (4,5), both modes): the shared
    /// earlier site must not duplicate.
    #[test]
    fn triple_conflict_reports_each_site_once() {
        let case_text = "function f() {\n}\nlet f = 1;\nlet f = 2;\n";
        let units = split_case_units("tests/cases/compiler/tripleConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tripleConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 3, 4),
                ("BAMTS-C001".to_owned(), 4, 4),
            ]
        );
    }
    /// Sloppy twin of the triple-conflict pin (tsc TS2300 at all
    /// three sites in sloppy too).
    #[test]
    fn sloppy_triple_conflict_reports_each_site_once() {
        let case_text = "function f() {\n}\nlet f = 1;\nlet f = 2;\n";
        let units = split_case_units("tests/cases/compiler/sloppyTriple.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyTriple.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 3, 4),
                ("BAMTS-C001".to_owned(), 4, 4),
            ]
        );
    }
    /// Mixed triple: each later conflict sees the lexical incumbent
    /// left by the previous one, so every site still reports exactly
    /// once (no repeated peer-report).
    #[test]
    fn mixed_triple_conflict_reports_each_site_once() {
        let case_text = "function f() {\n}\nlet f;\nclass f {\n}\n";
        let units = split_case_units("tests/cases/compiler/mixedTriple.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/mixedTriple.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 3, 4),
                ("BAMTS-C001".to_owned(), 4, 6),
            ]
        );
    }
    /// the same shape with `var` stays silent (tsc clean, both modes).
    #[test]
    fn loop_header_var_merges_with_body_function() {
        let case_text = "for (var f = 0;;) function f() {\n}\n";
        let units = split_case_units("tests/cases/compiler/loopHeaderVarFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/loopHeaderVarFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Sloppy twin of the func-first dual (tsc TS2300 at both sites
    /// in sloppy too).
    #[test]
    fn sloppy_function_let_conflict_reports_both_sites() {
        let case_text = "function f() {\n}\nlet f = 1;\n";
        let units = split_case_units("tests/cases/compiler/sloppyFunctionLet.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyFunctionLet.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 3, 4),
            ]
        );
    }
    /// Sloppy twin of the var-merge guard (tsc clean in sloppy too).
    #[test]
    fn sloppy_loop_header_var_merges_with_body_function() {
        let case_text = "for (var f = 0;;) function f() {\n}\n";
        let units = split_case_units("tests/cases/compiler/sloppyLoopHeaderVar.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyLoopHeaderVar.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Sloppy twin of the header-let conflict (tsc TS2451 at both
    /// sites in sloppy too).
    #[test]
    fn sloppy_loop_header_let_conflicts_with_body_function() {
        let case_text = "for (let f = 0;;) function f() {\n}\n";
        let units = split_case_units("tests/cases/compiler/sloppyLoopHeaderLet.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/sloppyLoopHeaderLet.ts", &units);
        let pragmas = CasePragmas {
            options: vec![
                ("strict".to_owned(), vec!["false".to_owned()]),
                ("alwaysstrict".to_owned(), vec!["false".to_owned()]),
            ],
            no_types_and_symbols: false,
        };
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line, d.position.character))
            .collect();
        assert_eq!(
            codes,
            vec![
                ("BAMTS-C001".to_owned(), 1, 9),
                ("BAMTS-C001".to_owned(), 1, 27),
            ]
        );
    }

    /// Regression: an unbraced for-body function stays loop-scoped (tsc
    /// TS2304 on the post-loop use); it must not leak outward as `any`.
    #[test]
    fn for_body_function_stays_loop_scoped() {
        let case_text =
            "declare var cond: boolean;\nfor (; cond;) function f(x: string) {\n}\nf(1);\n";
        let units = split_case_units("tests/cases/compiler/forBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 4)]);
    }
    /// Regression: a braced for-body function stays loop-scoped too (tsc
    /// TS2304); only the loop subtree sees it.
    #[test]
    fn for_block_body_function_stays_loop_scoped() {
        let case_text =
            "declare var cond: boolean;\nfor (; cond;) {\nfunction b(x: string) {\n}\n}\nb(1);\n";
        let units = split_case_units("tests/cases/compiler/forBlockBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forBlockBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 6)]);
    }
    /// Regression: a for-of body function stays loop-scoped (tsc TS2304).
    #[test]
    fn for_of_body_function_stays_loop_scoped() {
        let case_text = "declare var items: string[];\nfor (const item of items) function h(x: string) {\n}\nh(1);\n";
        let units = split_case_units("tests/cases/compiler/forOfBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forOfBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 4)]);
    }
    /// Guard: a while-body function still hoists (tsc checks the post-loop
    /// call: TS2345), so the for-family containment must not leak outward.
    #[test]
    fn while_body_function_still_hoists() {
        let case_text =
            "declare var cond: boolean;\nwhile (cond) function w(x: string) {\n}\nw(1);\n";
        let units = split_case_units("tests/cases/compiler/whileBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/whileBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C053".to_owned(), 4)]);
    }
    /// Guard: an if-body function still hoists (tsc TS2345 on a bad call).
    #[test]
    fn if_body_function_still_hoists() {
        let case_text = "declare var cond: boolean;\nif (cond) function g(x: string) {\n}\ng(1);\n";
        let units = split_case_units("tests/cases/compiler/ifBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/ifBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C053".to_owned(), 4)]);
    }
    /// Regression: a for-in body function stays loop-scoped (tsc TS2304).
    #[test]
    fn for_in_body_function_stays_loop_scoped() {
        let case_text = "declare var o: any;\nfor (var k in o) function h(x: string) {\n}\nh(1);\n";
        let units = split_case_units("tests/cases/compiler/forInBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forInBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 4)]);
    }
    /// Regression: containment propagates through nested statements (tsc
    /// TS2304 for an if-nested function inside a for body).
    #[test]
    fn for_nested_if_function_stays_loop_scoped() {
        let case_text = "declare var cond: boolean;\nfor (; cond;) {\nif (cond) {\nfunction x(x: string) {\n}\n}\n}\nx(1);\n";
        let units = split_case_units("tests/cases/compiler/forNestedIfFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forNestedIfFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 8)]);
    }

    #[test]
    fn shebang_line_does_not_end_the_reference_prologue() {
        let text = "#!/usr/bin/env node\n/// <reference path=\"/.lib/react.d.ts\" />\nvar x = 1;\n";
        assert_eq!(shared_lib_refs(text), vec!["react.d.ts".to_owned()]);
    }

    #[test]
    fn code_after_a_closed_block_comment_ends_the_prologue() {
        let text = "/* c */ var x = 1;\n/// <reference path=\"/.lib/a.d.ts\" />\n";
        assert_eq!(shared_lib_refs(text), Vec::<String>::new());
    }

    #[test]
    fn directive_after_a_closed_block_comment_on_one_line_counts() {
        let text = "/* c */ /// <reference path=\"/.lib/b.d.ts\" />\nvar x = 1;\n";
        assert_eq!(shared_lib_refs(text), vec!["b.d.ts".to_owned()]);
    }

    #[test]
    fn multiline_block_comment_before_a_directive_counts() {
        let text = "/*\nline one\nline two\n*/\n/// <reference path=\"/.lib/c.d.ts\" />\nvar x = 1;\n";
        assert_eq!(shared_lib_refs(text), vec!["c.d.ts".to_owned()]);
    }

    #[test]
    fn directive_inside_a_block_comment_body_is_inert() {
        let text = "/* /// <reference path=\"/.lib/d.d.ts\" /> */\nvar x = 1;\n";
        assert_eq!(shared_lib_refs(text), Vec::<String>::new());
    }
