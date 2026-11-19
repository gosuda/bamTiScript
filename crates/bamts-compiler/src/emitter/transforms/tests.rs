    use super::{LanguageFeature, ScriptTarget, analyze, codes, emit_transformed};
    use crate::checker;
    use crate::diagnostic::Recovered;
    use crate::emitter::{EmitFileNames, EmitOptions, EmitOutput, ModuleKind};
    use crate::parser;
    use crate::scanner;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use std::sync::Arc;

    fn parse(source: &str) -> crate::syntax::SourceFile {
        parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("test source fits the per-file source budget")),
        ))
        .into_product()
    }

    fn names() -> EmitFileNames {
        EmitFileNames {
            source_name: Arc::from("input.ts"),
            js_file_name: Some(Arc::from("output.js")),
            declaration_file_name: Some(Arc::from("output.d.ts")),
            source_root: None,
            ..EmitFileNames::default()
        }
    }

    fn options_for(target: ScriptTarget) -> EmitOptions {
        EmitOptions {
            target,
            ..EmitOptions::default()
        }
    }

    fn emit_at(source: &str, target: ScriptTarget) -> EmitOutput {
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let options = options_for(target);
        emit_transformed(
            &file,
            checked.product(),
            &options.transform_view(),
            &names(),
        )
    }

    fn emit_with_options(source: &str, options: EmitOptions) -> EmitOutput {
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        emit_transformed(
            &file,
            checked.product(),
            &options.transform_view(),
            &names(),
        )
    }

    fn javascript(output: &EmitOutput) -> &str {
        &output.javascript.as_ref().expect("JavaScript output").code
    }
    fn parse_json(source: &str) -> crate::syntax::SourceFile {
        parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::Json,
            Arc::new(SourceText::new(source).expect("test source fits the per-file source budget")),
        ))
        .into_product()
    }
    fn emit_json_at(source: &str, target: ScriptTarget) -> EmitOutput {
        let file = parse_json(source);
        let checked = checker::check(&Recovered::clean(parse_json(source)));
        let options = options_for(target);
        emit_transformed(
            &file,
            checked.product(),
            &options.transform_view(),
            &names(),
        )
    }
    #[test]
    fn an_object_rest_binding_becomes_a_rest_call_beside_the_kept_pattern() {
        let output = emit_at(
            "var { ...clone } = o;\nvar { a, ...justB } = o;\nvar { ['b']: renamed, ...justA } = o;\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var clone = __rest(o, []);\nvar { a } = o, justB = __rest(o, [\"a\"]);\nvar { ['b']: renamed } = o, justA = __rest(o, ['b']);\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_nested_object_rest_reads_its_parent_property_once() {
        let output = emit_at(
            "var { x: { ka, ...nested }, y: other, ...rest } = complex;\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var _a = complex.x, { ka } = _a, nested = __rest(_a, [\"ka\"]), { y: other } = complex, rest = __rest(complex, [\"x\", \"y\"]);\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_object_rest_assignment_becomes_one_comma_expression() {
        let output = emit_at(
            "({ x, ...fresh } = { x: 1, y: 2 });\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var _a;\n(_a = { x: 1, y: 2 }, { x } = _a, fresh = __rest(_a, [\"x\"]));\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_array_pattern_holding_an_object_rest_binds_its_source_directly() {
        let output = emit_at(
            "var { a: [{ ...nested2 }, ...y], ...rest2 } = overEmit;\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var [_a, ...y] = overEmit.a, nested2 = __rest(_a, []), rest2 = __rest(overEmit, [\"a\"]);\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_object_rest_parameter_is_unpacked_at_the_head_of_the_body() {
        let output = emit_at(
            "function cloneAgain({ a, ...clone }) {\n}\nsuddenly(({ x: a, ...rest }) => rest.y);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "function cloneAgain(_a) {\n    var { a } = _a, clone = __rest(_a, [\"a\"]);\n}\nsuddenly((_a) => {\n    var { x: a } = _a, rest = __rest(_a, [\"x\"]);\n    return rest.y;\n});\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_object_rest_in_a_for_of_head_is_unpacked_in_the_body() {
        let output = emit_at(
            "for (let { x, ...restOf } of array) {\n    [x, restOf];\n}\nfor ({ x: xx, ...rrestOff } of array) {\n    [xx, rrestOff];\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "for (let _a of array) {\n    let { x } = _a, restOf = __rest(_a, [\"x\"]);\n    [x, restOf];\n}\nfor (let _b of array) {\n    ({ x: xx } = _b, rrestOff = __rest(_b, [\"x\"]));\n    [xx, rrestOff];\n}\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_object_rest_catch_binding_is_unpacked_in_the_handler() {
        let output = emit_at("try { }\ncatch ({ a, ...b }) {\n}\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "try { }\ncatch (_a) {\n    var { a } = _a, b = __rest(_a, [\"a\"]);\n}\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_object_spread_folds_into_object_assign_calls() {
        let output = emit_at(
            "let addAfter = { ...o, c: false };\nlet addBefore = { c: false, ...o };\nlet combined = { ...o, ...o2 };\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(
            code,
            "let addAfter = Object.assign(Object.assign({}, o), { c: false });\nlet addBefore = Object.assign({ c: false }, o);\nlet combined = Object.assign(Object.assign({}, o), o2);\n"
        );
    }
    #[test]
    fn json_empty_object_prints_braces_without_prologue_like_require_of_json_file_with_empty_object()
     {
        assert_eq!(
            javascript(&emit_json_at("{\n}\n", ScriptTarget::Es2015)),
            "{}\n"
        );
    }
    #[test]
    fn json_trailing_comma_drops_and_keeps_indent_like_require_of_json_file_with_trailling_comma() {
        assert_eq!(
            javascript(&emit_json_at(
                "{\n    \"a\": true,\n    \"b\": \"hello\",\n}\n",
                ScriptTarget::Es2015
            )),
            "{\n    \"a\": true,\n    \"b\": \"hello\"\n}\n"
        );
    }
    #[test]
    fn json_invalid_content_prints_shorthand_object_like_require_of_json_file_without_resolve_json_module()
     {
        assert_eq!(
            javascript(&emit_json_at("contents Not read", ScriptTarget::Es2015)),
            "{ contents, Not, read }\n"
        );
    }
    #[test]
    fn json_empty_input_prints_empty_without_prologue_like_require_of_json_file_with_no_content() {
        let output = emit_json_at("", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.is_empty(), "{code:?}");
    }
    #[test]
    fn json_values_print_like_require_of_json_file_types() {
        for (source, expected) in [
            ("[\"a\", null, \"string\"]\n", "[\"a\", null, \"string\"]\n"),
            ("\"dConfig\"\n", "\"dConfig\"\n"),
            ("-10\n", "-10\n"),
            ("[-10, 30]\n", "[-10, 30]\n"),
            ("[true, false]\n", "[true, false]\n"),
            (
                "{\n    \"a\": true,\n    \"b\": \"hello\",\n    \"c\": null,\n    \"d\": false\n}\n",
                "{\n    \"a\": true,\n    \"b\": \"hello\",\n    \"c\": null,\n    \"d\": false\n}\n",
            ),
        ] {
            assert_eq!(
                javascript(&emit_json_at(source, ScriptTarget::Es2015)),
                expected,
                "{source:?}"
            );
        }
    }

    #[test]
    fn dense_million_node_file_keeps_authored_preservation_unaliased() {
        // The rewriter's id source is seeded past the parser high-water
        // (and any JSX-desugar consumption), so minted ids are disjoint
        // from authored ids BY CONSTRUCTION — the structural fix for the
        // old constant floor. This pins the observable consequences on a
        // dense million-node file: emit completes, no statements drop,
        // authored single-line preservation holds, and field lowering
        // still mints its descriptors.
        let mut statements = 330_000usize;
        let tail = "function probe() { return 1; }\nclass K { }";
        // Grow the prefix until the parser high-water crosses 1_000_100:
        // node yield per statement amortizes, so calibrate on the real
        // construction rather than a small sample.
        let high_water = loop {
            let probe = format!("{}{tail}", "a;".repeat(statements));
            let water = parse(&probe).id().get();
            if water >= 1_000_400 || statements > 600_000 {
                break water;
            }
            statements += 2_000;
        };
        let mut source = String::with_capacity(2_000_000);
        source.push_str(&"a;".repeat(statements));
        source.push_str("function probe() { return 1; }\n");
        source.push_str("class K { ");
        for i in 0..60 {
            source.push_str(&format!("f{i} = 1; "));
        }
        source.push_str("}\n");
        assert!(
            (1_000_350..=1_004_500).contains(&high_water),
            "calibration drifted: high water {high_water}"
        );
        let output = emit_with_options(
            &source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("function probe() { return 1; }"),
            "authored single-line body lost preservation"
        );
        assert!(
            code.contains("enumerable: true"),
            "descriptor lowering missing"
        );
    }

    #[test]
    fn esnext_keeps_async_and_class_fields() {
        let source = "class C { x = 1; }\nasync function f() { return await 1; }\n";
        let output = emit_at(source, ScriptTarget::EsNext);
        let code = javascript(&output);
        assert!(code.contains("x = 1"), "{code}");
        assert!(code.contains("async function"), "{code}");
        assert!(!code.contains("__awaiter"), "{code}");
    }

    #[test]
    fn es2015_downlevels_class_fields_into_the_constructor() {
        let output = emit_at("class C { x = 1; }\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("constructor"), "{code}");
        assert!(code.contains("this.x = 1"), "{code}");
        assert!(
            !code.lines().any(|line| line.trim() == "x = 1;"),
            "field initializer should move: {code}"
        );
    }
    #[test]
    fn require_locals_follow_the_tsc_slug_shape() {
        // tsc binds `enum_1` for an identifier-starting slug and
        // `_10_lib_1` when a leading digit forces sanitization.
        let mut names = super::RequireNames::new(std::collections::BTreeSet::new());
        assert_eq!(names.allocate("./enum"), "enum_1");
        assert_eq!(names.allocate("./10_lib"), "_10_lib_1");
        assert_eq!(names.allocate("./enum"), "enum_2");
    }

    #[test]
    fn class_expression_without_lowering_stays_inline() {
        // Authority: classExpressionTest2 — a generic class expression with
        // no lowered members emits inline with type parameters stripped
        // (`var m = class C {`), never a temp-IIFE wrap.
        let output = emit_at(
            "function M() {\n    var m = class C<X> { f() { return 1; } };\n    return new m();\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("var m = class C {"), "{code}");
        assert!(!code.contains("(() =>"), "{code}");
    }

    #[test]
    fn derived_class_fields_follow_super_and_literal_names_are_preserved() {
        let output = emit_at(
            r#"class C extends B { "x" = 1; 2 = 3; constructor() { super(); after(); } }
"#,
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let super_at = code
            .find("super()")
            .expect("derived constructor calls super");
        let string_at = code.find(r#"this["x"] = 1"#).expect("string field name");
        let number_at = code.find("this[2] = 3").expect("numeric field name");
        let after_at = code.find("after()").expect("original constructor body");
        assert!(
            super_at < string_at && string_at < number_at && number_at < after_at,
            "{code}"
        );
    }

    #[test]
    fn synthesized_derived_constructor_forwards_arguments_before_fields() {
        let output = emit_at("class C extends B { x = 1; }\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("super(...arguments)"), "{code}");
        assert!(
            code.find("super(...arguments)").unwrap() < code.find("this.x = 1").unwrap(),
            "{code}"
        );
    }
    #[test]
    fn uninitialized_fields_emit_nothing_under_assignment_semantics() {
        // Baseline computedPropertyNames36_ES5(target=es2015).js keeps
        // `class Foo {\n}` for `class Foo { x }`: assignment semantics
        // define nothing for a declaration without an initializer.
        let output = emit_at("class C { x; static y; }\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(!code.contains("constructor"), "{code}");
        assert!(!code.contains("void 0"), "{code}");
        assert!(code.contains("class C {"), "{code}");
    }

    #[test]
    fn uninitialized_fields_define_void_0_under_define_semantics() {
        let output = emit_with_options(
            "class C { x; static y; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("Object.defineProperty(this, \"x\""), "{code}");
        assert!(code.contains("Object.defineProperty(C, \"y\""), "{code}");
        assert!(code.contains("void 0"), "{code}");
        assert!(!code.contains("this.x ="), "{code}");
    }

    #[test]
    fn computed_field_names_are_evaluated_once_at_class_definition() {
        let output = emit_at(
            "class C { [key()] = 1; } new C(); new C();\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert!(code.contains("let _a = key()"), "{code}");
        assert!(code.contains("this[_a] = 1"), "{code}");
    }
    #[test]
    fn computed_keys_preserve_heritage_and_member_evaluation_order() {
        let output = emit_at(
            "class C extends heritage() { [field()] = 1; [method()]() {} [later()] = 2; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let heritage = code.find("heritage()").expect("heritage evaluation");
        let field = code.find("field()").expect("first computed field");
        let method = code.find("method()").expect("computed method");
        let later = code.find("later()").expect("later computed field");
        let class = code.find("class C extends _a").expect("rewritten class");
        assert!(
            heritage < field && field < method && method < later && later < class,
            "{code}"
        );
        assert!(code.contains("this[_b] = 1"), "{code}");
        assert!(code.contains("[_c]()"), "{code}");
        assert!(code.contains("this[_d] = 2"), "{code}");
    }
    #[test]
    fn static_computed_field_runs_key_and_value_and_assigns_the_property() {
        let output = emit_at(
            "class C { static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("value()").count(), 1, "{code}");
        let key = code.find("let _a = key()").expect("key setup");
        let class = code.find("class C").expect("class declaration");
        let assignment = code
            .find("C[_a] = value()")
            .expect("post-class static property assignment");
        assert!(key < class && class < assignment, "{code}");
    }
    #[test]
    fn named_export_wraps_only_the_lowered_class() {
        let output = emit_at(
            "export class C { static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let prelude = code.find("let _a = key()").expect("ordinary key prelude");
        let class = code
            .find("export class C")
            .expect("exported rewritten class");
        let postlude = code
            .find("C[_a] = value()")
            .expect("ordinary static postlude");
        assert!(prelude < class && class < postlude, "{code}");
        assert!(!code.contains("export let _a"), "{code}");
        assert!(!code.contains("export C[_a]"), "{code}");
    }

    #[test]
    fn named_default_export_keeps_class_and_generated_statements_separate() {
        let output = emit_at(
            "export default class C { field = 1; static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let prelude = code.find("let _a = key()").expect("ordinary key prelude");
        let class = code
            .find("export default class C")
            .expect("named default class");
        let postlude = code
            .find("C[_a] = value()")
            .expect("ordinary static postlude");
        assert!(prelude < class && class < postlude, "{code}");
        assert!(code.contains("this.field = 1"), "{code}");
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("value()").count(), 1, "{code}");
        assert!(!code.contains("export default let"), "{code}");
    }

    #[test]
    fn anonymous_default_export_lowers_instance_fields_in_place() {
        let output = emit_at(
            "export default class { field = 1; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("export default class"), "{code}");
        assert!(code.contains("constructor"), "{code}");
        assert!(code.contains("this.field = 1"), "{code}");
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code() == codes::STATIC_FIELD_REQUIRES_CLASS_NAME }),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn anonymous_default_static_field_uses_one_synthetic_class_target() {
        let output = emit_at(
            "export default class { static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let prelude = code.find("let _a = key()").expect("ordinary key prelude");
        let class = code
            .find("export default class _b")
            .expect("synthetically named default class");
        let postlude = code
            .find("_b[_a] = value()")
            .expect("static assignment uses synthetic class name");
        assert!(prelude < class && class < postlude, "{code}");
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("value()").count(), 1, "{code}");
    }
    #[test]
    fn anonymous_default_static_class_restores_imported_name_to_default() {
        let output = emit_at(
            "export default class { static x = 1; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let class = code
            .find("export default class _a")
            .expect("synthetically named default class");
        let restore = code
            .find(r#"Object.defineProperty(_a, "name""#)
            .expect("default name restoration");
        let static_assignment = code.find("_a.x = 1").expect("post-class static assignment");
        assert!(class < restore && restore < static_assignment, "{code}");
        assert!(code.contains(r#"value: "default""#), "{code}");
        assert!(code.contains("configurable: true"), "{code}");
    }

    #[test]
    fn es2015_downlevels_async_to_awaiter() {
        // Authority: es5-importHelpersAsyncFunctions(target=es2015).js emits
        // the awaiter alone — native generators need no __generator.
        let output = emit_at(
            "async function f(x) { return await x; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("__awaiter"), "{code}");
        assert!(code.contains("function*"), "{code}");
        assert!(code.contains("yield"), "{code}");
        assert!(!code.contains("async "), "{code}");
        assert!(
            code.contains("var __awaiter = (this && this.__awaiter) || function"),
            "{code}"
        );
        assert!(!code.contains("__generator"), "{code}");
    }
    #[test]
    fn es5_async_arguments_rename_stops_at_nested_functions() {
        let output = emit_at(
            "async function f() { function g() { return arguments.length; } await 1; return arguments[0]; }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("arguments_1[0]"), "{code}");
        assert!(code.contains("return arguments.length"), "{code}");
        let nested_only = emit_at(
            "async function f() { function g() { return arguments.length; } await 1; }\n",
            ScriptTarget::Es5,
        );
        let nested_code = javascript(&nested_only);
        assert!(!nested_code.contains("arguments_1"), "{nested_code}");
    }

    #[test]
    fn helper_emission_uses_rewriter_demand_not_analysis_prediction() {
        // Authority: es5-importHelpersAsyncFunctions(target=es2015).js.
        let source = "function outer() { return async () => await 1; }\n";
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let options = options_for(ScriptTarget::Es2015);
        let transform_options = options.transform_view();
        let plan = analyze(&file, &transform_options);
        assert!(
            plan.helpers.is_empty(),
            "fixture must remain outside the shallow analysis walk"
        );

        let output = emit_transformed(&file, checked.product(), &transform_options, &names());
        let code = javascript(&output);
        assert!(
            code.contains("var __awaiter = (this && this.__awaiter) || function"),
            "{code}"
        );
        assert!(
            !code.contains("__generator"),
            "native-generator targets emit no __generator: {code}"
        );
    }

    #[test]
    fn es5_downlevels_object_destructuring() {
        let output = emit_at("const { a, b } = o;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(code.contains("a = "), "{code}");
        assert!(code.contains("b = "), "{code}");
        assert!(!code.contains("{ a, b }"), "{code}");
    }

    #[test]
    fn private_fields_below_es2022_are_errors() {
        let output = emit_at("class C { #x = 1; }\n", ScriptTarget::Es2015);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::PRIVATE_FIELD_REQUIRES_ES2022),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn classes_below_es2015_are_errors() {
        let output = emit_at("class C { #x = 1; }\n", ScriptTarget::Es5);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::CLASS_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }
    #[test]
    fn a_block_with_a_resource_disposes_it_on_every_exit() {
        let output = emit_at(
            "{\n    using d1 = a, d2 = b;\n    d1;\n}\n",
            ScriptTarget::Es2022,
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "{\n    const env_1 = { stack: [], error: void 0, hasError: false };\n    try {\n        const d1 = __addDisposableResource(env_1, a, false), d2 = __addDisposableResource(env_1, b, false);\n        d1;\n    }\n    catch (e_1) {\n        env_1.error = e_1;\n        env_1.hasError = true;\n    }\n    finally {\n        __disposeResources(env_1);\n    }\n}"
            ),
            "{code}"
        );
    }

    #[test]
    fn an_awaited_resource_waits_for_its_disposal() {
        let output = emit_at(
            "async function f() {\n    await using d = a;\n}\n",
            ScriptTarget::Es2022,
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "        const d = __addDisposableResource(env_1, a, true);\n    }\n    catch (e_1) {\n        env_1.error = e_1;\n        env_1.hasError = true;\n    }\n    finally {\n        const result_1 = __disposeResources(env_1);\n        if (result_1)\n            await result_1;\n    }"
            ),
            "{code}"
        );
    }

    #[test]
    fn nested_environments_number_outside_in_and_their_catches_inside_out() {
        let output = emit_at(
            "function f() {\n    using outer = a;\n    {\n        using inner = b;\n    }\n}\n",
            ScriptTarget::Es2022,
        );
        let code = javascript(&output);
        let outer = code.find("__addDisposableResource(env_1, a, false)");
        let inner = code.find("__addDisposableResource(env_2, b, false)");
        assert!(outer < inner && outer.is_some(), "{code}");
        assert!(
            code.find("catch (e_1)") < code.find("catch (e_2)")
                && code.contains("env_2.error = e_1;"),
            "{code}"
        );
    }

    #[test]
    fn a_top_level_resource_hoists_the_names_declared_beside_it() {
        let output = emit_at(
            "using d = a;\nfunction f() { }\nclass C {\n}\n",
            ScriptTarget::Es2022,
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "function f() { }\nvar d, C;\nconst env_1 = { stack: [], error: void 0, hasError: false };\ntry {\n    d = __addDisposableResource(env_1, a, false);\n    C = class C {\n    };\n}\ncatch (e_1) {"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_namespace_body_disposes_its_own_resources() {
        let output = emit_at("namespace N {\n    using d = a;\n}\n", ScriptTarget::Es2022);
        let code = javascript(&output);
        assert!(
            code.contains(
                "(function (N) {\n    const env_1 = { stack: [], error: void 0, hasError: false };\n    try {\n        const d = __addDisposableResource(env_1, a, false);\n    }"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_for_of_resource_is_registered_once_per_iteration() {
        let output = emit_at("for (using d of xs) {\n    d;\n}\n", ScriptTarget::Es2022);
        let code = javascript(&output);
        assert!(
            code.contains(
                "for (const d_1 of xs) {\n    const env_1 = { stack: [], error: void 0, hasError: false };\n    try {\n        const d = __addDisposableResource(env_1, d_1, false);\n        d;\n    }"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_for_head_resource_outlives_the_whole_loop() {
        let output = emit_at("for (using d = a;;) {\n    d;\n}\n", ScriptTarget::Es2022);
        let code = javascript(&output);
        let registered = code.find("__addDisposableResource(env_1, a, false)");
        let disposed = code.find("    __disposeResources(env_1);");
        let body = code.find("        d;");
        assert!(
            registered.is_some() && registered < body && body < disposed,
            "{code}"
        );
    }

    #[test]
    fn generated_resource_bindings_are_var_below_es2015() {
        let output = emit_at("{\n    using d = a;\n}\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("    var env_1 = { stack: [], error: void 0, hasError: false };")
                && code.contains("        var d = __addDisposableResource(env_1, a, false);"),
            "{code}"
        );
    }

    #[test]
    fn a_constructor_keeps_its_place_among_native_fields() {
        let source = "class C {\n    x = 1;\n    constructor() { }\n    y = 2;\n}\n";
        assert_eq!(javascript(&emit_at(source, ScriptTarget::Es2022)), source);
    }

    #[test]
    fn static_fields_and_blocks_remain_interleaved() {
        let output = emit_at(
            "class C { static a = one(); static { step(); } static b = two(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let first = code.find("C.a = one()").expect("first static field");
        let block = code.find("step()").expect("static block");
        let second = code.find("C.b = two()").expect("second static field");
        assert!(first < block && block < second, "{code}");
        assert!(!code.contains("static {"), "{code}");
    }

    #[test]
    fn define_mode_uses_complete_data_descriptors() {
        let output = emit_with_options(
            "class C { x = 1; static y = 2; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("Object.defineProperty(this, \"x\""), "{code}");
        assert!(code.contains("Object.defineProperty(C, \"y\""), "{code}");
        let enumerable = code
            .find("enumerable: true")
            .expect("enumerable descriptor");
        let configurable = code
            .find("configurable: true")
            .expect("configurable descriptor");
        let writable = code.find("writable: true").expect("writable descriptor");
        let value = code.find("value: 1").expect("descriptor value");
        assert!(
            enumerable < configurable && configurable < writable && writable < value,
            "{code}"
        );
    }

    #[test]
    fn synthesized_descriptor_object_expands_in_javascript() {
        // Authority: override18(target=es2015).js — the defineProperty
        // descriptor is wholly synthesized and prints multi-line even when
        // the authored source is compact. An untainted mint collapsed it
        // onto one line (sweep-2d76b09 regression).
        let output = emit_with_options(
            "class A { foo?: string; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("Object.defineProperty(this, \"foo\", {\n            enumerable: true,"),
            "{code}"
        );
        assert!(!code.contains("{ enumerable: true, configurable"), "{code}");
    }

    #[test]
    fn declare_and_abstract_fields_have_no_runtime_initializers() {
        let output = emit_at(
            "abstract class C { declare x: number; abstract y: string; z = 1; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(!code.contains("this.x"), "{code}");
        assert!(!code.contains("this.y"), "{code}");
        assert!(code.contains("this.z = 1"), "{code}");
    }

    #[test]
    fn nested_super_sites_receive_fields_after_each_completion() {
        let output = emit_at(
            "class C extends B { x = 1; constructor(flag) { if (flag) super(1); else { super(2); } } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("this.x = 1").count(), 2, "{code}");
        let first_super = code.find("super(1)").expect("first super");
        let first_init = code.find("this.x = 1").expect("first init");
        assert!(first_super < first_init, "{code}");
    }

    #[test]
    fn class_expressions_lower_inside_call_arguments_like_class_expression_with_static_properties1()
    {
        let output = emit_at(
            "consume(class { static x = 1; y = 2; });\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("_a = class {"), "{code}");
        assert!(code.contains("_a.x = 1,"), "{code}");
        assert!(code.contains(",\n    _a))"), "{code}");
        assert!(!code.contains(", _a))"), "{code}");
        assert!(code.contains("this.y = 2"), "{code}");
        assert!(code.contains(".x = 1"), "{code}");
        assert!(!code.contains("static x"), "{code}");
    }

    #[test]
    fn native_declaration_emits_suspending_class_key_prelude_in_order() {
        let output = emit_at(
            "function* g() { const left = before(), C = class { [yield key()]() {} }, right = after(); }\n",
            ScriptTarget::Es2015,
        );
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        let code = javascript(&output);
        let positions = ["before()", "key()", "C =", "after()"].map(|needle| {
            assert_eq!(code.matches(needle).count(), 1, "{needle}: {code}");
            code.find(needle).expect("emitted expression")
        });
        assert!(positions.windows(2).all(|pair| pair[0] < pair[1]), "{code}");
    }

    #[test]
    fn static_this_and_super_are_rebound_to_the_constructor() {
        let output = emit_at(
            "class B { static p() {} } class C extends B { static x = this; static { super.p(); } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("C.x = C"), "{code}");
        assert!(
            code.contains("Reflect.get(Object.getPrototypeOf(C), \"p\", C).call(C)"),
            "{code}"
        );
    }

    #[test]
    fn static_block_only_source_is_detected_as_class_fields() {
        let file = parse("class C { static { run(); } }\n");
        let options = options_for(ScriptTarget::Es2015).transform_view();
        let plan = analyze(&file, &options);
        assert!(plan.features.contains(&LanguageFeature::ClassFields));
        assert!(plan.required.contains(&LanguageFeature::ClassFields));
    }
    #[test]
    fn nested_static_blocks_rewrite_this_through_control_flow() {
        let output = emit_at(
            "class C { static { if (flag) { for (; once(); ) { this.x = this; break; } } try { throw this; } catch (e) { this.y = e; } finally { this.z = this; } } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("C.x = C"), "{code}");
        assert!(code.contains("throw C"), "{code}");
        assert!(code.contains("C.y = e"), "{code}");
        assert!(code.contains("C.z = C"), "{code}");
    }

    #[test]
    fn static_super_writes_use_reflect_with_single_evaluation() {
        let output = emit_at(
            "class B { static get x() { return 1; } static set x(v) {} } class C extends B { static { super.x = rhs(); super[key()] += more(); } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(!code.contains("super.x ="), "{code}");
        assert!(!code.contains("super[key()]"), "{code}");
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("rhs()").count(), 1, "{code}");
        assert_eq!(code.matches("more()").count(), 1, "{code}");
        assert!(code.matches("Reflect.set(").count() >= 2, "{code}");
        assert!(code.contains("Reflect.get("), "{code}");
    }

    #[test]
    fn node_executes_nested_static_super_writes() {
        let source = r#"
const log = [];
function key() { log.push("key"); return "x"; }
function rhs() { log.push("rhs"); return 3; }
class B {
  static get x() { log.push("get"); return this._x ?? 1; }
  static set x(value) { log.push("set"); this._x = value; }
}
class C extends B {
  static {
    if (true) {
      super.x = 2;
      try { super[key()] += rhs(); this.self = this; }
      finally { this.done = true; }
    }
  }
}
console.log(JSON.stringify([C._x, log, C.self === C, C.done]));
"#;
        let output = emit_at(source, ScriptTarget::Es2015);
        let code = javascript(&output);
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-static-super-{nonce}.mjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout).expect("Node stdout"),
            "[5,[\"set\",\"key\",\"get\",\"rhs\",\"set\"],true,true]\n"
        );
    }

    #[test]
    fn analysis_is_deterministic_and_lists_required_features() {
        let file = parse("async function f() { const { a } = x; }\n");
        let options = options_for(ScriptTarget::Es5).transform_view();
        let left = analyze(&file, &options);
        let right = analyze(&file, &options);
        assert_eq!(left, right);
        assert!(left.required.contains(&LanguageFeature::AsyncFunctions));
        assert!(left.required.contains(&LanguageFeature::Destructuring));
    }

    #[test]
    fn strict_prologue_follows_always_strict_and_module_kind() {
        // A top-level external module takes the prologue exactly when it is
        // transpiled to CommonJS; under ES module output it takes none even
        // with alwaysStrict on (673 baselines). Scripts follow alwaysStrict
        // alone, as conformance pairs like arrowFunctionContexts(alwaysstrict=...)
        // show.
        let module = emit_with_options(
            "export const value = 1;\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert!(
            javascript(&module).starts_with("\"use strict\";\n"),
            "a CommonJS external module implies strict: {}",
            javascript(&module)
        );
        let es_module = emit_with_options(
            "export const value = 1;\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::Es2015),
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            !javascript(&es_module).starts_with("\"use strict\";\n"),
            "an ES external module takes no prologue even under alwaysStrict: {}",
            javascript(&es_module)
        );
        let commonjs_script = emit_with_options(
            "const value = 1;\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert!(
            !javascript(&commonjs_script).starts_with("\"use strict\";\n"),
            "a script under CommonJS still follows alwaysStrict: {}",
            javascript(&commonjs_script)
        );
        let script = emit_with_options(
            "const value = 1;\n",
            EmitOptions {
                ..EmitOptions::default()
            },
        );
        assert!(
            !javascript(&script).starts_with("\"use strict\";\n"),
            "a plain script has no prologue: {}",
            javascript(&script)
        );
        let always = emit_with_options(
            "const value = 1;\n",
            EmitOptions {
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            javascript(&always).starts_with("\"use strict\";\n"),
            "alwaysStrict emits the prologue: {}",
            javascript(&always)
        );
        let deduped = emit_with_options(
            "\"use strict\";\nconst value = 1;\n",
            EmitOptions {
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&deduped);
        assert_eq!(
            code.matches("\"use strict\";").count(),
            1,
            "a source directive suppresses the synthetic one: {code}"
        );
    }

    #[test]
    fn ambient_enum_and_module_produce_no_runtime_statements() {
        // Upstream ambientEnumElementInitializer5 (43527a9c) emits only the
        // strict prologue; ambientModules (df2119af) keeps only the trailing
        // member assignment.
        let ambient_enum = emit_at("declare enum E { e = -0xA }\n", ScriptTarget::Es2015);
        assert_eq!(
            javascript(&ambient_enum),
            "",
            "{:?}",
            javascript(&ambient_enum)
        );

        let ambient_module = emit_at(
            "declare namespace Foo.Bar { export var foo; };\nFoo.Bar.foo = 5;\n",
            ScriptTarget::Es2015,
        );
        // The ambient declaration vanishes; the runtime assignment survives,
        // matching upstream ambientModules (df2119af) after the prologue.
        assert!(
            !javascript(&ambient_module).starts_with("declare")
                && !javascript(&ambient_module).contains("export var foo"),
            "the ambient block is erased: {}",
            javascript(&ambient_module)
        );

        let runtime = emit_at("const enum K { A }\nlet kept = 1;\n", ScriptTarget::Es2015);
        assert!(
            javascript(&runtime).contains("kept"),
            "non-ambient code survives: {}",
            javascript(&runtime)
        );
    }

    #[test]
    fn generic_call_type_arguments_are_erased() {
        // Upstream genericCallWithNonGenericArgs1 (e71ae63c): f<any>(null)
        // emits f(null);
        let output = emit_at(
            "function f<T>(x: any) { }\nf<any>(null);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("f(null);"), "{code}");
        assert!(!code.contains("<any>"), "{code}");
    }

    #[test]
    fn commonjs_named_import_and_function_export_match_upstream_shape() {
        // Upstream commonjsSafeImport(target=es2015).js
        // (282283386bc4040f0eba585ac33e142c5c30cfbb67f969b1706c655dc7bee408).
        let export = emit_with_options(
            "export function Foo() {}\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let export_code = javascript(&export);
        assert!(
            export_code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.Foo = Foo;\nfunction Foo()"
            ),
            "{export_code}"
        );

        let import = emit_with_options(
            "import { Foo } from './10_lib';\nFoo();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let import_code = javascript(&import);
        assert!(
            import_code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst _10_lib_1 = require(\"./10_lib\");\n"
            ),
            "{import_code}"
        );
        assert!(
            import_code.contains("(0, _10_lib_1.Foo)();"),
            "{import_code}"
        );
        assert!(!import_code.contains("import "), "{import_code}");
    }

    #[test]
    fn es5_lowers_nested_computed_destructuring_assignment() {
        // Upstream computedPropertiesInDestructuring1.js
        // (50845e031ebf8203c61d4bfb72d37eea703fea245df4e215c7b5772583a8a898).
        let output = emit_at(
            "let foo = 'bar', bar4; [{ [foo]: bar4 }] = [{ bar: 'bar' }];\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code()
                    == codes::DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
        assert!(code.contains("bar4 ="), "{code}");
        assert!(code.contains("[foo]"), "{code}");
        assert!(!code.contains("[{ [foo]: bar4 }] ="), "{code}");
    }

    #[test]
    fn commonjs_export_of_an_ambient_function_claims_no_void_0() {
        let output = emit_with_options(
            "declare function foo(): any;\nexport { foo };\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(!code.contains("void 0"), "{code}");
    }

    #[test]
    fn commonjs_marker_follows_a_source_directive() {
        let output = emit_with_options(
            "\"use strict\";\nexport class Foo {}\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&output),
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.Foo = void 0;\nclass Foo {\n}\nexports.Foo = Foo;\n"
        );
    }

    #[test]
    fn commonjs_class_and_variable_exports_receive_void_0_preamble() {
        let output = emit_with_options(
            "export class A {}\nexport const x = 1;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.x = exports.A = void 0;\n"
            ),
            "{code}"
        );
        let marker = code
            .find("exports.x = exports.A = void 0;")
            .expect("preamble");
        let class_at = code.find("class A").expect("class kept");
        let class_export = code.find("exports.A = A;").expect("class export");
        let variable_export = code.find("exports.x = 1;").expect("variable export");
        assert!(!code.contains("const x"), "{code}");
        assert!(
            marker < class_at && class_at < class_export && class_export < variable_export,
            "{code}"
        );
    }

    #[test]
    fn commonjs_void_0_preamble_chains_names_in_reverse_source_order_in_chunks_of_fifty() {
        let mut source = String::from("export const b = 1;\nexport const a = 2;\n");
        for index in 0..60 {
            source.push_str(&format!("export const n{index} = {index};\n"));
        }
        let output = emit_with_options(
            &source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let preamble: Vec<&str> = code
            .lines()
            .filter(|line| line.ends_with(" = void 0;"))
            .collect();
        assert_eq!(preamble.len(), 2, "{code}");
        assert!(
            preamble[0].starts_with("exports.n47 = exports.n46 =")
                && preamble[0].ends_with("= exports.a = exports.b = void 0;"),
            "{}",
            preamble[0]
        );
        assert_eq!(
            preamble[1],
            format!(
                "{} = void 0;",
                (48..60)
                    .rev()
                    .map(|index| format!("exports.n{index}"))
                    .collect::<Vec<_>>()
                    .join(" = ")
            )
        );
    }

    #[test]
    fn an_empty_enum_body_prints_across_two_lines() {
        let output = emit_with_options(
            "enum E {\n}\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("(function (E) {\n})(E || (E = {}));"),
            "{code}"
        );
    }

    #[test]
    fn commonjs_local_specifier_exports_assign_each_name() {
        // Same `exports.NAME = LOCAL;` identifier-assignment form as the
        // identifier default export in es6ImportDefaultBindingWithExport
        // server.js (adfd4388): `exports.default = a;`.
        let output = emit_with_options(
            "const a = 1, b = 2;\nexport { a, b as c };\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("exports.a = a;"), "{code}");
        assert!(code.contains("exports.c = b;"), "{code}");
        assert!(!code.contains("export {"), "{code}");
    }

    #[test]
    fn a_namespace_fills_its_container_through_a_call() {
        let output = emit_at(
            "namespace A {\n\
             \x20   // a comment\n\
             \x20   export var x = 1, y;\n\
             \x20   var hidden = x;\n\
             \x20   export function f() { return x; }\n\
             \x20   export class C {}\n\
             \x20   export namespace B {\n\
             \x20       export var z = x + 1;\n\
             \x20   }\n\
             }\n\
             namespace A {\n\
             \x20   x = 2;\n\
             \x20   x++;\n\
             \x20   const box = { x };\n\
             \x20   f();\n\
             }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var A;\n\
             (function (A) {\n\
             \x20   // a comment\n\
             \x20   A.x = 1;\n\
             \x20   var hidden = A.x;\n\
             \x20   function f() { return A.x; }\n\
             \x20   A.f = f;\n\
             \x20   class C {\n\
             \x20   }\n\
             \x20   A.C = C;\n\
             \x20   let B;\n\
             \x20   (function (B) {\n\
             \x20       B.z = A.x + 1;\n\
             \x20   })(B = A.B || (A.B = {}));\n\
             })(A || (A = {}));\n\
             (function (A) {\n\
             \x20   A.x = 2;\n\
             \x20   A.x++;\n\
             \x20   const box = { x: A.x };\n\
             \x20   A.f();\n\
             })(A || (A = {}));\n"
        );
    }

    #[test]
    fn an_enum_is_declared_once_and_published_like_a_namespace() {
        let output = emit_at(
            "enum E { A }\n\
             enum E { B = 1 }\n\
             namespace N {\n\
             \x20   export enum F { C }\n\
             \x20   enum G { D }\n\
             }\n\
             function f() {\n\
             \x20   enum H { I }\n\
             }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var E;\n\
             (function (E) {\n\
             \x20   E[E[\"A\"] = 0] = \"A\";\n\
             })(E || (E = {}));\n\
             (function (E) {\n\
             \x20   E[E[\"B\"] = 1] = \"B\";\n\
             })(E || (E = {}));\n\
             var N;\n\
             (function (N) {\n\
             \x20   let F;\n\
             \x20   (function (F) {\n\
             \x20       F[F[\"C\"] = 0] = \"C\";\n\
             \x20   })(F = N.F || (N.F = {}));\n\
             \x20   let G;\n\
             \x20   (function (G) {\n\
             \x20       G[G[\"D\"] = 0] = \"D\";\n\
             \x20   })(G || (G = {}));\n\
             })(N || (N = {}));\n\
             function f() {\n\
             \x20   let H;\n\
             \x20   (function (H) {\n\
             \x20       H[H[\"I\"] = 0] = \"I\";\n\
             \x20   })(H || (H = {}));\n\
             }\n"
        );
    }

    #[test]
    fn dotted_segments_bind_with_var_like_class_and_module_with_same_name_and_common_root() {
        let output = emit_at(
            "namespace X.Y {\n\
             \x20   export var origin = 1;\n\
             }\n\
             namespace Outer {\n\
             \x20   export namespace Inner {\n\
             \x20       export var center = 2;\n\
             \x20   }\n\
             }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var X;\n\
             (function (X) {\n\
             \x20   var Y;\n\
             \x20   (function (Y) {\n\
             \x20       Y.origin = 1;\n\
             \x20   })(Y = X.Y || (X.Y = {}));\n\
             })(X || (X = {}));\n\
             var Outer;\n\
             (function (Outer) {\n\
             \x20   let Inner;\n\
             \x20   (function (Inner) {\n\
             \x20       Inner.center = 2;\n\
             \x20   })(Inner = Outer.Inner || (Outer.Inner = {}));\n\
             })(Outer || (Outer = {}));\n"
        );
    }

    #[test]
    fn class_expression_static_fields_use_a_hoisted_temp_like_class_expression_with_static_properties1()
     {
        let output = emit_at(
            "var v = class C {\n\
             \x20   static a = 1;\n\
             \x20   static b = 2;\n\
             \x20   static c = C.a + C.b;\n\
             };\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var _a;\n\
             var v = (_a = class C {\n\
             \x20   },\n\
             \x20   _a.a = 1,\n\
             \x20   _a.b = 2,\n\
             \x20   _a.c = _a.a + _a.b,\n\
             \x20   _a);\n"
        );
    }
    #[test]
    fn anonymous_class_expression_with_static_fields_has_no_name_restore_like_es64() {
        let output = emit_at("(class { static x = 0; });\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(!code.contains("defineProperty"), "{code}");
        assert!(!code.contains("__setFunctionName"), "{code}");
        assert!(code.contains("_a.x = 0"), "{code}");
    }
    #[test]
    fn anonymous_class_expression_assigned_to_variable_restores_inferred_name() {
        let output = emit_at("var v = class { static x = 1; };\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("value: \"v\""), "{code}");
        let assign = code.find("_a = class").expect("temp assignment: {code}");
        let restore = code.find("value: \"v\"").expect("restore: {code}");
        let field = code.find("_a.x = 1").expect("field: {code}");
        assert!(assign < restore && restore < field, "{code}");
    }
    #[test]
    fn class_expression_computed_keys_keep_class_name_like_computed_with_static() {
        let output = emit_at(
            "(class C2 {\n\
             \x20   static staticProp = 10;\n\
             \x20   get [C2.staticProp]() { return \"hello\"; }\n\
             \x20   [C2.staticProp]() {}\n\
             });\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("[C2.staticProp]"), "{code}");
        assert!(!code.contains("[_a.staticProp]"), "{code}");
        assert!(code.contains("_a.staticProp = 10"), "{code}");
    }

    #[test]
    fn class_declaration_static_fields_assign_through_the_class_name() {
        let output = emit_at(
            "class C {\n\
             \x20   static a = 1;\n\
             }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(javascript(&output), "class C {\n}\nC.a = 1;\n");
    }
    #[test]
    fn plain_sequence_with_multiline_function_keeps_inline_separators() {
        let output = emit_at(
            "var x = (function foo() {\n return 1;\n}, 2);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("}, 2)"), "{code}");
    }
    #[test]
    fn separated_hex_prints_as_decimal_at_es2015_like_overshifts() {
        let output = emit_at("0xFF_FF_FF_FF;\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("4294967295"), "{code}");
        assert!(!code.contains("_"), "{code}");
    }
    #[test]
    fn hex_and_octal_without_separators_keep_at_es2015_like_parse_big_int() {
        let output = emit_at("0xC0B;\n0o567;\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("0xC0B"), "{code}");
        assert!(code.contains("0o567"), "{code}");
    }
    #[test]
    fn legacy_octal_prints_decimal_like_literals() {
        let output = emit_at("015;\n001;\n09;\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("13;"), "{code}");
        assert!(code.contains("1;"), "{code}");
        assert!(code.contains("9;"), "{code}");
        assert!(!code.contains("015"), "{code}");
        assert!(!code.contains("001"), "{code}");
    }
    #[test]
    fn decimal_separators_print_plain_below_es2021_like_numeric_underscored_separator() {
        let output = emit_at("123_456;\n1e2;\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("123456"), "{code}");
        assert!(code.contains("1e2"), "{code}");
        assert!(!code.contains("_"), "{code}");
    }

    #[test]
    fn bigint_literals_normalize_to_decimal_except_lowercase_hex_like_parse_big_int() {
        let output = emit_at(
            "0b101n;\n0o567n;\n0xC0Bn;\n123n;\n0b010_10_1n;\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("5n"), "{code}");
        assert!(code.contains("375n"), "{code}");
        assert!(code.contains("0xc0bn"), "{code}");
        assert!(code.contains("123n"), "{code}");
        assert!(code.contains("21n"), "{code}");
    }

    #[test]
    fn decimal_separators_keep_at_es2021_and_normalize_below_like_parser_numeric_separators_decimal()
     {
        let source = "1_000_000_000;\n1.1_00_01;\n1e1_0;\n1.1e10_0;\n0_.0;\n";
        let es2021_output = emit_at(source, ScriptTarget::Es2021);
        let es2021 = javascript(&es2021_output);
        assert!(es2021.contains("1_000_000_000"), "{es2021}");
        let es5_output = emit_at(source, ScriptTarget::Es5);
        let es5 = javascript(&es5_output);
        assert!(es5.contains("1000000000"), "{es5}");
        assert!(es5.contains("1.10001"), "{es5}");
        assert!(es5.contains("10000000000"), "{es5}");
        assert!(es5.contains("1.1e+100"), "{es5}");
        assert!(!es5.contains("_"), "{es5}");
    }
    #[test]
    fn hex_separators_keep_at_esnext_and_decimalize_below_like_numeric_underscored_separator() {
        let source = "0xA0_B0_C0;\n";
        let esnext_output = emit_at(source, ScriptTarget::EsNext);
        let esnext = javascript(&esnext_output);
        assert!(esnext.contains("0xA0_B0_C0"), "{esnext}");
        let es2015_output = emit_at(source, ScriptTarget::Es2015);
        let es2015 = javascript(&es2015_output);
        assert!(!es2015.contains("_"), "{es2015}");
        assert!(!es2015.contains("0x"), "{es2015}");
    }

    #[test]
    fn numeric_property_names_normalize_like_numeric_underscored_separator() {
        let output = emit_at("var x = { 0xFF_FF: 1, 0b10_1: 2 };\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("65535"), "{code}");
        assert!(code.contains("5:"), "{code}");
        assert!(!code.contains("0xFF_FF"), "{code}");
        assert!(!code.contains("0b10_1"), "{code}");
    }
    #[test]
    fn class_expression_temp_is_function_scoped_like_class_block_scoping() {
        let output = emit_at(
            "function f(b: boolean) {\n\
             \x20   let Foo: any;\n\
             \x20   if (b) {\n\
             \x20       Foo = class Foo {\n\
             \x20           static y = new Foo();\n\
             \x20       };\n\
             \x20   }\n\
             }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let fn_pos = code.find("function f").expect("function: {code}");
        let var_pos = code.find("var _a").expect("temp declaration: {code}");
        assert!(fn_pos < var_pos, "{code}");
        assert!(
            !code.lines().next().unwrap_or("").contains("var _a"),
            "{code}"
        );
    }
    #[test]
    fn nested_class_expression_temp_is_inner_function_scoped_like_static_block18() {
        let output = emit_at(
            "function foo() {\n\
             \x20   return class {\n\
             \x20       static foo = 1;\n\
             \x20       static {\n\
             \x20           const c = class {\n\
             \x20               static bar = 2;\n\
             \x20           };\n\
             \x20       }\n\
             \x20   };\n\
             }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let foo_pos = code.find("function foo").expect("foo");
        assert!(
            foo_pos < code.find("var _a").unwrap_or(usize::MAX),
            "{code}"
        );
        let b_pos = code.find("var _b").unwrap_or(usize::MAX);
        assert!(b_pos != usize::MAX, "missing var _b in:\n{code}");
        assert!(
            code.find("var _a").unwrap() < b_pos,
            "inner temp follows outer:\n{code}"
        );
        let iife_pos = code
            .find("() =>")
            .or_else(|| code.find("function ("))
            .unwrap_or(usize::MAX);
        assert!(
            iife_pos != usize::MAX,
            "missing static block function in:\n{code}"
        );
        assert!(
            iife_pos < b_pos,
            "inner temp inside static block function:\n{code}"
        );
    }

    #[test]
    fn unexported_nested_namespaces_stay_local_like_nested_module_private_access() {
        let output = emit_at(
            "namespace a {\n\
             \x20   var x: number;\n\
             \x20   namespace b {\n\
             \x20       var y = x;\n\
             \x20   }\n\
             }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var a;\n\
             (function (a) {\n\
             \x20   var x;\n\
             \x20   let b;\n\
             \x20   (function (b) {\n\
             \x20       var y = x;\n\
             \x20   })(b || (b = {}));\n\
             })(a || (a = {}));\n"
        );
    }

    #[test]
    fn nested_containers_bind_with_var_below_es2015_like_comments_external_modules() {
        let output = emit_at(
            "namespace M {\n\
             \x20   export namespace N {\n\
             \x20       export var c = 3;\n\
             \x20   }\n\
             }\n",
            ScriptTarget::Es5,
        );
        assert_eq!(
            javascript(&output),
            "var M;\n\
             (function (M) {\n\
             \x20   var N;\n\
             \x20   (function (N) {\n\
             \x20       N.c = 3;\n\
             \x20   })(N = M.N || (M.N = {}));\n\
             })(M || (M = {}));\n"
        );
    }

    #[test]
    fn an_exported_enum_publishes_its_container() {
        let source = "export enum E { A }\nexport const enum F { B }\n";
        let esm = emit_at(source, ScriptTarget::Es2015);
        assert_eq!(
            javascript(&esm),
            "export var E;\n(function (E) {\n    E[E[\"A\"] = 0] = \"A\";\n})(E || (E = {}));\n"
        );
        let cjs = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&cjs),
            "\"use strict\";\n\
             Object.defineProperty(exports, \"__esModule\", { value: true });\n\
             exports.E = void 0;\n\
             var E;\n\
             (function (E) {\n\
             \x20   E[E[\"A\"] = 0] = \"A\";\n\
             })(E || (exports.E = E = {}));\n"
        );
    }

    #[test]
    fn an_alias_is_declared_only_where_it_holds_a_value() {
        // Upstream aliasBug, unusedImports10 and
        // usingModuleWithExportImportInValuePosition.
        let output = emit_at(
            "namespace A { export var x = 1; export interface I {} }\n\
             import top = A;\n\
             namespace B { import unused = A; export var y = 1; }\n\
             namespace C { import read = A; export var z = read.x; }\n\
             namespace D { export import published = A; }\n\
             namespace E { export import shape = A.I; export var w = 1; }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var A;\n\
             (function (A) {\n\
             \x20   A.x = 1;\n\
             })(A || (A = {}));\n\
             var top = A;\n\
             var B;\n\
             (function (B) {\n\
             \x20   B.y = 1;\n\
             })(B || (B = {}));\n\
             var C;\n\
             (function (C) {\n\
             \x20   var read = A;\n\
             \x20   C.z = read.x;\n\
             })(C || (C = {}));\n\
             var D;\n\
             (function (D) {\n\
             \x20   D.published = A;\n\
             })(D || (D = {}));\n\
             var E;\n\
             (function (E) {\n\
             \x20   E.w = 1;\n\
             })(E || (E = {}));\n"
        );
    }

    #[test]
    fn a_namespace_member_is_rewritten_wherever_it_is_used() {
        let output = emit_at(
            "namespace N {\n\
             \x20   export var x = 1;\n\
             \x20   export class C {\n\
             \x20       constructor(public p = x) {}\n\
             \x20       m(q = x) { return () => x + q; }\n\
             \x20   }\n\
             \x20   for (x of [1]) {}\n\
             \x20   for (x in {}) {}\n\
             \x20   function shadowed(x: number) { return x; }\n\
             }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        for expected in [
            "constructor(p = N.x)",
            "m(q = N.x)",
            "return () => N.x + q;",
            "for (N.x of [1])",
            "for (N.x in {})",
            "function shadowed(x) { return x; }",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn a_name_is_rewritten_in_loop_heads_and_binding_patterns() {
        let output = emit_at(
            "namespace N {\n\
             \x20   export var n = 3;\n\
             \x20   for (let i = n; i > 0; i--) {}\n\
             \x20   for (const { a = n } of []) {}\n\
             \x20   for (const k in { [n]: 1 }) {}\n\
             \x20   function f({ a = n }, [b = n]) {}\n\
             \x20   const { c = n, [n]: d } = {};\n\
             }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        for expected in [
            "for (let i = N.n; i > 0; i--)",
            "for (const { a = N.n } of [])",
            "[N.n]: 1",
            "function f({ a = N.n }, [b = N.n])",
            "const { c = N.n, [N.n]: d } = {};",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn an_unknown_name_in_a_binding_pattern_is_reported() {
        let source = "const { a = missing } = {};\nconst [b = alsoMissing] = [];\n";
        let checked = checker::check(&Recovered::clean(parse(source)));
        let unknown = checked
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code() == crate::checker::CANNOT_FIND_NAME)
            .count();
        assert_eq!(unknown, 2, "{:?}", checked.diagnostics());
    }

    #[test]
    fn a_const_enum_member_is_inlined() {
        let output = emit_at(
            "const enum K { A = 1 }\nconsole.log(K.A);\nconsole.log(K['A']);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(!code.contains("K.A)"), "{code}");
        assert!(!code.contains("K['A']"), "{code}");
        assert!(code.contains("console.log(1"), "{code}");
    }

    #[test]
    fn a_published_alias_is_read_from_its_container() {
        let output = emit_at(
            "namespace A { export var x = 1; }\n\
             namespace C { export var v = b; export import b = A.x; export var w = b; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        for expected in ["C.v = C.b;", "C.b = A.x;", "C.w = C.b;"] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn a_namespace_without_a_value_emits_nothing() {
        let output = emit_at(
            "namespace T { export interface I {} }\n\
             namespace U { import a = T; }\n\
             namespace V { export const enum E { A } }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(javascript(&output), "");
    }

    #[test]
    fn a_namespace_merged_into_a_class_uses_its_binding() {
        let output = emit_at(
            "class C {}\nnamespace C { export var x = 1; }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "class C {\n}\n(function (C) {\n    C.x = 1;\n})(C || (C = {}));\n"
        );
    }

    #[test]
    fn a_namespace_whose_body_shadows_its_name_renames_the_parameter() {
        let output = emit_at(
            "namespace M { export var M = 1; export var y = M; }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var M;\n(function (M_1) {\n    M_1.M = 1;\n    M_1.y = M_1.M;\n})(M || (M = {}));\n"
        );
    }

    #[test]
    fn an_exported_pattern_assigns_each_name_onto_the_container() {
        // Upstream declarationEmitDestructuringArrayPattern3 and
        // downlevelLetConst13: one read needs no temporary.
        let output = emit_at(
            "namespace M {\n\
             \x20   export var [a, b] = [1, 2];\n\
             \x20   export let [c] = [1];\n\
             \x20   export const { d: e } = { d: 1 };\n\
             }\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "var M;\n\
             (function (M) {\n\
             \x20   var _a;\n\
             \x20   _a = [1, 2], M.a = _a[0], M.b = _a[1];\n\
             \x20   M.c = [1][0];\n\
             \x20   M.e = { d: 1 }.d;\n\
             })(M || (M = {}));\n"
        );
    }

    #[test]
    fn an_exported_pattern_collects_its_rest() {
        let output = emit_at(
            "namespace M {\n\
             \x20   export var [a, ...b] = [1, 2, 3];\n\
             \x20   export var { c, ...d } = { c: 1, e: 2 };\n\
             }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        for expected in [
            "_a = [1, 2, 3], M.a = _a[0], M.b = _a.slice(1);",
            "_b = { c: 1, e: 2 }, M.c = _b.c, M.d = __rest(_b, [\"c\"]);",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn an_exported_namespace_publishes_its_container() {
        let source = "export namespace M { export var x = 1; }\n";
        let esm = emit_at(source, ScriptTarget::Es2015);
        assert_eq!(
            javascript(&esm),
            "export var M;\n(function (M) {\n    M.x = 1;\n})(M || (M = {}));\n"
        );
        let cjs = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&cjs),
            "\"use strict\";\n\
             Object.defineProperty(exports, \"__esModule\", { value: true });\n\
             exports.M = void 0;\n\
             var M;\n\
             (function (M) {\n\
             \x20   M.x = 1;\n\
             })(M || (exports.M = M = {}));\n"
        );
    }

    #[test]
    fn commonjs_keeps_an_exported_variable_on_exports() {
        // Upstream downlevelLetConst13 and internalAliasVarInsideTopLevelModuleWithExport.
        let output = emit_with_options(
            "export var a = 1, b;\n\
             export let [c] = [1];\n\
             a = 2;\n\
             a++;\n\
             const box = { a };\n\
             a();\n\
             function f(a: number) { return a; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let body = code
            .split_once("void 0;\n")
            .map(|(_, body)| body)
            .expect("the preamble declares the exports");
        assert_eq!(
            body,
            "exports.a = 1;\n\
             exports.c = [1][0];\n\
             exports.a = 2;\n\
             exports.a++;\n\
             const box = { a: exports.a };\n\
             (0, exports.a)();\n\
             function f(a) { return a; }\n"
        );
        for name in ["exports.a", "exports.b", "exports.c"] {
            let preamble = code.split("void 0;").next().expect("split yields a head");
            assert!(preamble.contains(name), "{code}");
        }
    }

    #[test]
    fn commonjs_export_specifiers_read_what_the_name_became() {
        let output = emit_with_options(
            "import { x } from './m';\n\
             import y from './n';\n\
             export var a = 1;\n\
             const local = 2;\n\
             export { a as b, x, y, local };\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for expected in [
            "exports.b = exports.a;",
            "Object.defineProperty(exports, \"x\", { enumerable: true, get: function () { return m_1.x; } });",
            "exports.y = n_1.default;",
            "exports.local = local;",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn commonjs_keeps_a_named_default_reexport_live() {
        let output = emit_with_options(
            "import { default as y } from './n';\nexport { y };\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "Object.defineProperty(exports, \"y\", { enumerable: true, get: function () { return n_1.default; } });"
            ),
            "{code}"
        );
    }

    fn emit_system(source: &str) -> EmitOutput {
        emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::System),
                ..EmitOptions::default()
            },
        )
    }

    #[test]
    fn system_module_publishes_an_exported_variable_from_execute() {
        let output = emit_system("export var x = 1;\n");
        assert_eq!(
            javascript(&output),
            "System.register([], function (exports_1, context_1) {\n    \"use strict\";\n    var x;\n    var __moduleName = context_1 && context_1.id;\n    return {\n        setters: [],\n        execute: function () {\n            exports_1(\"x\", x = 1);\n        }\n    };\n});\n"
        );
    }

    #[test]
    fn system_module_fills_imports_in_setters_and_republishes_them() {
        let output = emit_system(
            "import n, {x} from 'file1'\nimport n2 = require('file2');\nexport {x}\nexport {x as y}\nexport {n}\nexport {n2 as n3}\n",
        );
        let code = javascript(&output);
        for expected in [
            "System.register([\"file1\", \"file2\"], function (exports_1, context_1) {",
            "    var file1_1, n2;\n",
            "            function (file1_1_1) {\n                file1_1 = file1_1_1;\n            },\n            function (n2_1) {\n                n2 = n2_1;\n            }\n",
            "            exports_1(\"n\", file1_1.default);\n            exports_1(\"x\", file1_1.x);\n            exports_1(\"y\", file1_1.x);\n            exports_1(\"n3\", n2);\n",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn system_reexport_decision_drops_only_type_only_bindings() {
        let source = "interface OnlyType {}\ntype Alias = string;\nclass WithValue {}\ninterface Merged {}\nconst Merged = 1;\nimport type { Imported } from './m';\nconst local = 1;\n";
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let model = checked.product();
        let options = EmitOptions {
            target: ScriptTarget::Es2015,
            module: Some(crate::emitter::ModuleKind::System),
            ..EmitOptions::default()
        };
        let view = options.transform_view();
        let type_imports = super::type_import_names(&file, &view);
        let module_scope = model.module_scope();
        let binding = |name: &str| {
            model
                .scope(module_scope)
                .type_binding(name)
                .or_else(|| model.scope(module_scope).value(name))
        };
        let decide = |target, name: &str| {
            super::system_module::import_reexport_is_type_only(model, target, name, &type_imports)
        };
        assert!(decide(binding("OnlyType"), "OnlyType"));
        assert!(decide(binding("Alias"), "Alias"));
        assert!(decide(None, "Imported"));
        assert!(decide(binding("OnlyType"), "local"));
        assert!(!decide(binding("WithValue"), "WithValue"));
        assert!(!decide(binding("Merged"), "Merged"));
        assert!(!decide(binding("local"), "local"));
        assert!(!decide(binding("Missing"), "Missing"));
    }

    #[test]
    fn system_module_skips_a_reexport_of_an_erased_import_binding() {
        let output = emit_with_options(
            "import { A, I as EI } from 'file1';\nconsole.log(EI);\nexport { A };\nexport { EI };\nexport { EI as EI1 };\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::System),
                erased_imports: Arc::new(
                    [("file1".to_owned(), "I".to_owned())].into_iter().collect(),
                ),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(!code.contains("exports_1(\"EI\""), "{code}");
        assert!(code.contains("exports_1(\"A\", file1_1.A)"), "{code}");
    }

    #[test]
    fn system_module_leaves_a_namespace_beside_a_default_import_unrewritten() {
        let output = emit_system("import e, * as ns2 from 'file5';\ne();\nns2.f();\n");
        let code = javascript(&output);
        assert!(
            code.contains("            file5_1.default();\n            ns2.f();\n"),
            "{code}"
        );
    }

    #[test]
    fn commonjs_reads_a_published_alias_from_exports() {
        let output = emit_with_options(
            "export namespace a { export var x = 10; }\n\
             export import b = a.x;\n\
             export var c = b;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("exports.b = a.x;"), "{code}");
        assert!(code.contains("exports.c = exports.b;"), "{code}");
    }

    #[test]
    fn commonjs_imports_stay_in_source_order_among_statements() {
        let output = emit_with_options(
            "// leading\n\
             import './s';\n\
             globalThis.a = 1;\n\
             import { q } from './m';\n\
             console.log(q);\n\
             export * from './n';\n\
             import './t';\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let order = [
            "// leading",
            "require(\"./s\");",
            "globalThis.a = 1;",
            "const m_1 = require(\"./m\");",
            "console.log(m_1.q);",
            "__exportStar(require(\"./n\"), exports);",
            "require(\"./t\");",
        ];
        let positions: Vec<usize> = order
            .iter()
            .map(|line| code.find(line).unwrap_or_else(|| panic!("{line}: {code}")))
            .collect();
        assert!(positions.is_sorted(), "{code}");
    }

    #[test]
    fn commonjs_keeps_an_exported_local_in_step_with_exports() {
        let output = emit_with_options(
            "export { x };\n\
             let x = 1, y = 2, z = 3;\n\
             export { y as w, z };\n\
             x = 5;\n\
             y += 1;\n\
             ++z;\n\
             z++;\n\
             const old = z--;\n\
             [x] = [7];\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let declared = code.find("let x = 1").expect("declaration");
        for line in ["exports.x = x;", "exports.w = y;", "exports.z = z;"] {
            let published = code.find(line).unwrap_or_else(|| panic!("{line}: {code}"));
            assert!(published > declared, "{line}: {code}");
        }
        for line in [
            "exports.x = x = 5;",
            "exports.w = y += 1;",
            "exports.z = ++z;",
            "exports.z = (z++, z);",
            ", exports.x = x, ",
        ] {
            assert!(code.contains(line), "{line}: {code}");
        }
        assert!(code.contains("exports.z = (_"), "{code}");
    }

    #[test]
    fn export_assignment_closes_the_module_and_an_ambient_publishes_nothing() {
        let commonjs = EmitOptions {
            target: ScriptTarget::Es2022,
            module: Some(crate::emitter::ModuleKind::CommonJs),
            ..EmitOptions::default()
        };
        let output = emit_with_options("export = C;\nclass C {}\n", commonjs.clone());
        let code = javascript(&output);
        assert!(code.ends_with("module.exports = C;\n"), "{code}");
        let ambient = emit_with_options(
            "declare const q: number;\nexport { q };\n",
            commonjs.clone(),
        );
        let code = javascript(&ambient);
        assert!(code.contains("exports.q = void 0;"), "{code}");
        assert!(!code.contains("exports.q = q"), "{code}");
        let parameter = emit_with_options(
            "import { x } from './m';\nclass C { constructor(public a = x) {} }\nnew C();\n",
            commonjs,
        );
        let code = javascript(&parameter);
        assert!(code.contains("a = m_1.x"), "{code}");
    }

    #[test]
    fn export_assignment_replaces_commonjs_exports() {
        let output = emit_with_options(
            "const K = 1;\nexport = K;\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&output),
            "\"use strict\";\nconst K = 1;\nmodule.exports = K;\n"
        );
    }

    #[test]
    fn string_export_names_quote_their_decoded_text() {
        let output = emit_with_options(
            "import { \"a b\" as ab } from './m';\n\
             const v = ab;\n\
             export { v as 'quo\"te', v as \"back\\\\slash\", v as \"x²\" };\n\
             export { q as \"c d\" } from './n';\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for line in [
            "const v = m_1[\"a b\"];",
            "exports[\"quo\\\"te\"] = v;",
            "exports[\"back\\\\slash\"] = v;",
            "exports[\"x²\"] = v;",
            "Object.defineProperty(exports, \"c d\", {",
        ] {
            assert!(code.contains(line), "{line}: {code}");
        }
    }

    #[test]
    fn verbatim_module_syntax_keeps_type_only_imports_loading() {
        let output = emit_with_options(
            "import { type I } from './a';\n\
             import {} from './b';\n\
             export { type T } from './c';\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::EsNext),
                verbatim_module_syntax: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for line in [
            "import {} from './a';",
            "import {} from './b';",
            "export {} from './c';",
        ] {
            assert!(code.contains(line), "{line}: {code}");
        }
    }

    #[test]
    fn a_require_local_is_always_an_identifier() {
        let mut names = super::RequireNames::new(std::collections::BTreeSet::new());
        for (module, expected) in [
            ("./m.js", "m_js_1"),
            ("./m.js", "m_js_2"),
            ("@scope/my-lib", "my_lib_1"),
            ("./10-lib", "_10_lib_1"),
            ("enum", "enum_1"),
        ] {
            assert_eq!(names.allocate(module), expected);
        }
    }

    #[test]
    fn commonjs_function_exports_precede_every_require() {
        let output = emit_with_options(
            "import './setup';\n\
             export * from './lib';\n\
             export function f() {}\n\
             function g() {}\n\
             export { g as h };\n\
             const c = 1;\n\
             export { c };\n\
             export default function d() {}\n\
             export declare function ambient(): void;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let order = [
            "exports.c = void 0;",
            "exports.f = f;",
            "exports.h = g;",
            "exports.default = d;",
            "require(\"./setup\");",
            "__exportStar(require(\"./lib\"), exports);",
            "function f() { }",
        ];
        let positions: Vec<usize> = order
            .iter()
            .map(|line| code.find(line).unwrap_or_else(|| panic!("{line}: {code}")))
            .collect();
        assert!(positions.is_sorted(), "{code}");
        assert!(!code.contains("ambient"), "{code}");
    }

    #[test]
    fn an_es_module_with_nothing_left_stays_a_module() {
        let esm = EmitOptions {
            target: ScriptTarget::Es2015,
            module: Some(crate::emitter::ModuleKind::EsNext),
            ..EmitOptions::default()
        };
        for source in [
            "export interface I {}\n",
            "interface I {}\nexport { I };\n",
            "export {};\n",
            "import type { T } from './t';\nconst x = 1;\nexport type { T };\n",
        ] {
            let output = emit_with_options(source, esm.clone());
            let code = javascript(&output);
            assert!(code.ends_with("export {};\n"), "{source}: {code}");
        }
        for source in ["export const x = 1;\n", "import './a';\n", "const x = 1;\n"] {
            let output = emit_with_options(source, esm.clone());
            assert!(!javascript(&output).contains("export {}"), "{source}");
        }
        let commonjs = emit_with_options(
            "export interface I {}\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert!(!javascript(&commonjs).contains("export {}"));
    }

    #[test]
    fn an_import_survives_only_through_a_value_read() {
        let esm = EmitOptions {
            target: ScriptTarget::Es2022,
            module: Some(crate::emitter::ModuleKind::EsNext),
            ..EmitOptions::default()
        };
        for (source, expected) in [
            (
                "import { I, v } from './m';\nlet a: I;\nv;\n",
                "import { v } from './m';",
            ),
            ("import { unused } from './m';\n", "export {};"),
            ("import d from './m';\nlet a: d;\n", "export {};"),
            ("import * as n from './m';\nlet a: n.T;\n", "export {};"),
            ("import {} from './m';\n", "export {};"),
            (
                "import { x } from './m';\nexport { x };\n",
                "import { x } from './m';",
            ),
            (
                "import { d } from './m';\n@d class C {}\n",
                "import { d } from './m';",
            ),
            (
                "import { d } from './m';\nclass C { @d m() {} }\n",
                "import { d } from './m';",
            ),
            (
                "import { c } from './m';\ntry {} catch ({ a = c }) {}\n",
                "import { c } from './m';",
            ),
            (
                "import { x } from './m';\nfunction f(a = x) { var x = 2; return a; }\n",
                "import { x } from './m';",
            ),
            (
                "import { x } from './m';\n{ function x() {} }\nconsole.log(x);\n",
                "import { x } from './m';",
            ),
            (
                "import { x } from './m';\nnamespace N { import q = x.v; export const w = q; }\n",
                "import { x } from './m';",
            ),
            (
                "import { x } from './m';\nexport import w = x.v;\n",
                "import { x } from './m';",
            ),
            ("import './m';\n", "import './m';"),
        ] {
            let output = emit_with_options(source, esm.clone());
            let code = javascript(&output);
            assert!(code.contains(expected), "{source}: {code}");
            if expected == "export {};" {
                assert!(!code.contains("import"), "{source}: {code}");
            }
        }
        let verbatim = emit_with_options(
            "import { unused } from './m';\n",
            EmitOptions {
                verbatim_module_syntax: true,
                ..esm.clone()
            },
        );
        assert!(javascript(&verbatim).contains("import { unused }"));
        let commonjs = emit_with_options(
            "import { I } from './m';\nlet a: I;\nexport { a };\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..esm
            },
        );
        assert!(!javascript(&commonjs).contains("require"));
    }

    #[test]
    fn a_catch_pattern_reads_through_its_namespace() {
        let output = emit_with_options(
            "namespace N {\n\
             export var n = 3;\n\
             try { throw {}; } catch ({ a = n }) { a; }\n\
             }\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("catch ({ a = N.n })"), "{code}");
    }

    #[test]
    fn a_value_read_keeps_an_import_whatever_another_file_seems_to_say() {
        let output = emit_with_options(
            "import { Foo, Bar } from './m';\nconsole.log(Foo);\nexport { Bar };\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::EsNext),
                erased_imports: std::sync::Arc::new(
                    [
                        ("./m".to_owned(), "Foo".to_owned()),
                        ("./m".to_owned(), "Bar".to_owned()),
                    ]
                    .into_iter()
                    .collect(),
                ),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("import { Foo } from './m';"), "{code}");
        assert!(!code.contains("Bar"), "{code}");
    }

    #[test]
    fn an_async_return_type_keeps_its_import_only_when_generators_lower() {
        let source = "import { Task } from './m';\n\
                      async function f(): Task<void> {}\n";
        let commonjs = |target| EmitOptions {
            target,
            module: Some(crate::emitter::ModuleKind::CommonJs),
            ..EmitOptions::default()
        };
        let es5 = emit_with_options(source, commonjs(ScriptTarget::Es5));
        let es5 = javascript(&es5);
        assert!(es5.contains("require(\"./m\")"), "{es5}");
        assert!(es5.contains("m_1.Task"), "{es5}");
        let es2015 = emit_with_options(source, commonjs(ScriptTarget::Es2015));
        assert!(
            !javascript(&es2015).contains("require"),
            "{}",
            javascript(&es2015)
        );
    }

    #[test]
    fn something_reading_imports_unseen_keeps_them_all() {
        let options = EmitOptions {
            target: ScriptTarget::Es2022,
            module: Some(crate::emitter::ModuleKind::EsNext),
            ..EmitOptions::default()
        };
        let pragma = emit_with_options(
            "/** @jsx h */\nimport { h } from './m';\nexport {};\n",
            options.clone(),
        );
        assert!(javascript(&pragma).contains("import { h }"));
        let metadata = emit_with_options(
            "import { T } from './m';\nlet a: T;\n",
            EmitOptions {
                keeps_imports: true,
                ..options
            },
        );
        assert!(javascript(&metadata).contains("import { T }"));
    }

    #[test]
    fn commonjs_export_import_require_lives_on_exports() {
        let output = emit_with_options(
            "export import ns = require('./m');\nconsole.log(ns);\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("exports.ns = require(\"./m\");"), "{code}");
        assert!(code.contains("console.log(exports.ns);"), "{code}");
    }

    #[test]
    fn a_type_has_no_runtime_export() {
        const SOURCE: &str = "import type { Q } from './types';\n\
             import { type R } from './types';\n\
             interface I {}\n\
             type T = 1;\n\
             const v = 1;\n\
             export { I, T, Q, R, v };\n";
        let commonjs_output = emit_with_options(
            SOURCE,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let commonjs = javascript(&commonjs_output);
        assert!(commonjs.contains("exports.v = void 0;"), "{commonjs}");
        assert!(commonjs.contains("exports.v = v;"), "{commonjs}");
        for name in ["I", "T", "Q", "R"] {
            assert!(!commonjs.contains(&format!("exports.{name}")), "{commonjs}");
        }
        let module_output = emit_with_options(
            SOURCE,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::EsNext),
                ..EmitOptions::default()
            },
        );
        let module = javascript(&module_output);
        assert!(module.contains("export { v };"), "{module}");
    }

    #[test]
    fn commonjs_reexports_are_not_left_as_module_syntax() {
        let output = emit_with_options(
            "export * from './a';\n\
             export * as ns from './b';\n\
             export { x, y as z } from './c';\n\
             export type { T } from './d';\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(!code.contains("export "), "{code}");
        assert!(!code.contains("./d"), "{code}");
        for expected in [
            "__exportStar(require(\"./a\"), exports);",
            "exports.ns = __importStar(require(\"./b\"));",
            "var c_1 = require(\"./c\");",
            "Object.defineProperty(exports, \"x\", { enumerable: true, get: function () { return c_1.x; } });",
            "Object.defineProperty(exports, \"z\", { enumerable: true, get: function () { return c_1.y; } });",
            "var __exportStar = (this && this.__exportStar) ||",
            "var __importStar = (this && this.__importStar) ||",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn amd_module_lists_its_dependencies_and_receives_them_as_parameters() {
        let output = emit_with_options(
            "import a = require('./a');\nimport * as ns from './n';\nimport './side';\nexport var x = a.v + ns.w;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let expected = "define([\"require\", \"exports\", \"./a\", \"./n\", \"./side\"], function (require, exports, a, ns) {\n    \"use strict\";\n    Object.defineProperty(exports, \"__esModule\", { value: true });\n    exports.x = void 0;\n    ns = __importStar(ns);\n    exports.x = a.v + ns.w;\n});\n";
        assert!(code.ends_with(expected), "{code}");
    }

    #[test]
    fn amd_module_assigns_interop_helpers_before_the_body_and_returns_export_assignments() {
        let output = emit_with_options(
            "import d from './d';\nexport = d;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let expected = "define([\"require\", \"exports\", \"./d\"], function (require, exports, d_1) {\n    \"use strict\";\n    d_1 = __importDefault(d_1);\n    return d_1.default;\n});\n";
        assert!(code.ends_with(expected), "{code}");
    }

    #[test]
    fn amd_directives_name_the_module_and_add_dependencies() {
        let output = emit_with_options(
            "///<amd-module name='Named'/>\n///<amd-dependency path='bar' name='b'/>\n\nimport m2 = require('m2');\nm2.f();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("define(\"Named\", [\"require\", \"exports\", \"bar\", \"m2\"], function (require, exports, b, m2) {"),
            "{code}"
        );
    }

    #[test]
    fn amd_directives_are_read_after_other_leading_comments() {
        let output = emit_with_options(
            "// copyright\n/* block\n   comment */\n///<amd-module name='Named'/>\n\nimport m2 = require('m2');\nm2.f();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("define(\"Named\", [\"require\", \"exports\", \"m2\"], function (require, exports, m2) {"),
            "{code}"
        );
    }

    #[test]
    fn amd_directives_after_the_first_statement_are_ignored() {
        let output = emit_with_options(
            "import m2 = require('m2');\n///<amd-module name='Late'/>\nm2.f();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("define([\"require\", \"exports\", \"m2\"]"),
            "{code}"
        );
    }

    #[test]
    fn amd_bundle_names_the_module_in_the_wrapper() {
        let output = emit_with_options(
            "import a = require('./a');\nexport var x = a.v;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                bundle_module_name: Some(Arc::from("ref/m1")),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "define(\"ref/m1\", [\"require\", \"exports\", \"./a\"], function (require, exports, a) {",
            ),
            "{code}"
        );
    }
    #[test]
    fn amd_bundle_name_with_quote_cannot_break_the_wrapper() {
        let output = emit_with_options(
            "import a = require('./a');\nexport var x = a.v;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                bundle_module_name: Some(Arc::from("x\";globalThis.PWNED=1;//")),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("x\\\";globalThis.PWNED=1;//"),
            "quote is escaped: {code}"
        );
        assert!(
            !code.contains("define(\"x\";"),
            "raw quote must not terminate the literal: {code}"
        );
        let directed = emit_with_options(
            "///<amd-dependency path='a\"b' name='e'/>\nimport a = require('./a');\nexport var x = a.v;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let directed_code = javascript(&directed);
        assert!(
            directed_code.contains("a\\\"b"),
            "directive path quote is escaped: {directed_code}"
        );
        assert!(
            !directed_code.contains("\"a\"b\""),
            "raw directive quote must not terminate the literal: {directed_code}"
        );
    }

    #[test]
    fn system_bundle_names_the_module_in_the_wrapper() {
        let output = emit_with_options(
            "import a from './a';\nexport var x = a;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::System),
                bundle_module_name: Some(Arc::from("ref/m1")),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("System.register(\"ref/m1\", ["),
            "bundle name reaches System.register: {code}"
        );
        let directed = emit_with_options(
            "///<amd-module name='Named'/>\nimport a from './a';\nexport var x = a;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::System),
                bundle_module_name: Some(Arc::from("ref/m1")),
                ..EmitOptions::default()
            },
        );
        let directed_code = javascript(&directed);
        assert!(
            directed_code.contains("System.register(\"Named\", ["),
            "directive wins over the bundle name: {directed_code}"
        );
    }

    #[test]
    fn amd_bundle_leaves_a_script_unwrapped() {
        let output = emit_with_options(
            "var a1 = 10;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                bundle_module_name: Some(Arc::from("m1")),
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert_eq!(code, "\"use strict\";\nvar a1 = 10;\n");
    }

    #[test]
    fn umd_module_wraps_the_commonjs_body_and_lists_its_dependencies() {
        let output = emit_with_options(
            "import a from './a';\nexport var x = a;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Umd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let expected = "(function (factory) {\n    if (typeof module === \"object\" && typeof module.exports === \"object\") {\n        var v = factory(require, exports);\n        if (v !== undefined) module.exports = v;\n    }\n    else if (typeof define === \"function\" && define.amd) {\n        define([\"require\", \"exports\", \"./a\"], factory);\n    }\n})(function (require, exports) {\n    \"use strict\";\n    Object.defineProperty(exports, \"__esModule\", { value: true });\n    exports.x = void 0;\n    const a_1 = __importDefault(require(\"./a\"));\n    exports.x = a_1.default;\n});\n";
        assert!(code.ends_with(expected), "{code}");
    }

    #[test]
    fn commonjs_import_helpers_call_through_one_tslib_binding() {
        let output = emit_with_options(
            "import d from './d';\nexport async function f() { return d; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                import_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        let expected = "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.f = f;\nconst tslib_1 = require(\"tslib\");\nconst d_1 = tslib_1.__importDefault(require(\"./d\"));\nfunction f() {\n    return tslib_1.__awaiter(this, void 0, void 0, function* () { return d_1.default; });\n}\n";
        assert!(code.ends_with(expected), "{code}");
    }

    #[test]
    fn commonjs_import_helpers_leave_a_script_with_inline_helpers() {
        let output = emit_with_options(
            "async function f() {}\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                import_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("var __awaiter = (this && this.__awaiter)"),
            "{code}"
        );
        assert!(!code.contains("tslib"), "{code}");
    }

    #[test]
    fn amd_leaves_a_script_unwrapped() {
        let output = emit_with_options(
            "var x = 1;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Amd),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(!code.contains("define("), "{code}");
    }

    #[test]
    fn commonjs_imports_stay_plain_when_es_module_interop_is_off() {
        // Authority: importHelpersWithImportOrExportDefault under
        // esmoduleinterop=false prints no interop helper.
        let output = emit_with_options(
            "import d from './b';\nimport * as ns from './c';\nexport * as all from './d';\nexport var x = d + ns.a;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                es_module_interop: false,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for expected in [
            "const b_1 = require(\"./b\");",
            "const ns = require(\"./c\");",
            "exports.all = require(\"./d\");",
            "exports.x = b_1.default + ns.a;",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
        assert!(!code.contains("__importDefault"), "{code}");
        assert!(!code.contains("__importStar"), "{code}");
    }

    #[test]
    fn a_reexported_default_reads_through_import_default() {
        // Authority: importHelpersWithImportOrExportDefault(esmoduleinterop=true,
        // module=commonjs): `tslib_1.__importDefault(a_1).default` in each getter.
        let output = emit_with_options(
            "export { default } from './a';\nexport { default as a } from './a';\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for expected in [
            "var a_1 = require(\"./a\");",
            "Object.defineProperty(exports, \"default\", { enumerable: true, get: function () { return __importDefault(a_1).default; } });",
            "var a_2 = require(\"./a\");",
            "Object.defineProperty(exports, \"a\", { enumerable: true, get: function () { return __importDefault(a_2).default; } });",
            "var __importDefault = (this && this.__importDefault) ||",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn commonjs_imports_follow_the_esmoduleinterop_forms() {
        // Authority: allowSyntheticDefaultImports1 and
        // es6ImportDefaultBindingFollowedWithNamedImport1InEs5 (default alone
        // through __importDefault); es6ImportDefaultBindingFollowedWith
        // NamespaceBindingInEs5 (a namespace takes its own name).
        let output = emit_with_options(
            "import d from './b';\n\
             import * as ns from './c';\n\
             import f, { g } from './e';\n\
             import { default as h } from './f';\n\
             import { i } from './g';\n\
             export var x = d + ns.a + f + g + h + i;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for expected in [
            "const b_1 = __importDefault(require(\"./b\"));",
            "const ns = __importStar(require(\"./c\"));",
            "const e_1 = __importStar(require(\"./e\"));",
            "const f_1 = __importDefault(require(\"./f\"));",
            "const g_1 = require(\"./g\");",
            "exports.x = b_1.default + ns.a + e_1.default + e_1.g + f_1.default + g_1.i;",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
        let create = code.find("var __createBinding").expect("createBinding");
        let default_module = code
            .find("var __setModuleDefault")
            .expect("setModuleDefault");
        let star = code.find("var __importStar").expect("importStar");
        let default = code.find("var __importDefault").expect("importDefault");
        assert!(
            create < default_module && default_module < star && star < default,
            "{code}"
        );
    }

    #[test]
    fn commonjs_rewrites_an_import_wherever_it_is_read() {
        let output = emit_with_options(
            "import { a } from './m';\n\
             const list = [a, ...a];\n\
             const box = { a, b: a, [a]: 1, c() { return a; } };\n\
             const text = `${a}`;\n\
             a.b = 1;\n\
             a.b++;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        for expected in [
            "const list = [m_1.a, ...m_1.a];",
            "a: m_1.a",
            "b: m_1.a",
            "[m_1.a]: 1",
            "return m_1.a;",
            "`${m_1.a}`",
            "m_1.a.b = 1;",
            "m_1.a.b++;",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn commonjs_side_effect_imports_stay_as_require() {
        let output = emit_with_options(
            "import './polyfill';\nrun();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("require(\"./polyfill\");"), "{code}");
        assert!(!code.contains("import "), "{code}");
    }

    #[test]
    fn node_executes_lowered_computed_destructuring_assignment() {
        // computedPropertiesInDestructuring1 (50845e03) pins the preserved
        // ES6 forms; this snapshot carries no ES5 blob, so the ES5 lowering
        // contract is pinned behaviorally: values, and one evaluation per
        // key/default in source order.
        let source = r#"
const log = [];
let foo = "bar";
let bar = 0, bar3 = 0, bar4 = 0;
function key() { log.push("key"); return foo; }
function rhs() { log.push("rhs"); return { bar: "set" }; }
({ [key()]: bar } = rhs());
[{ [key()]: bar4 }] = [{ bar: "nested" }];
console.log(JSON.stringify([bar, bar4, log]));
"#;
        let output = emit_at(source, ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code()
                    == codes::DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
        // 3 = function definition `function key()` + 2 call sites (one per destructuring)
        assert_eq!(code.matches("key()").count(), 3, "{code}");
        // 2 = function definition `function rhs()` + 1 call site
        assert_eq!(code.matches("rhs()").count(), 2, "{code}");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-cpd-{nonce}.cjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout)
                .expect("Node stdout")
                .trim(),
            // Per spec, RHS evaluates before computed keys in destructuring assignment:
            // rhs() → key() → key()
            r#"["set","nested",["rhs","key","key"]]"#
        );
    }

    #[test]
    fn computed_destructuring_keys_evaluate_once_into_a_temp() {
        // Upstream computedPropertiesInDestructuring1 (50845e03) lowers
        // `let {[foo2()]: bar3} = ...` to a temp declaration plus a
        // bracket read, with the key evaluated exactly once.
        let output = emit_at(
            "const key = \"k\";\nconst { [key]: value } = { k: 1 };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        // ES5 temps are `var` (a `let` inside cloned machine bodies is a
        // SyntaxError at ES5); ES2015+ keeps the tighter `let` binding.
        assert!(code.contains("var _a"), "ES5 temp kind: {code}");
        assert!(!code.contains("let _a"), "ES5 temp kind: {code}");
        let key_read_at = code.find(" = key").expect("key temp declared");
        let temp_name: String = code[..key_read_at]
            .chars()
            .rev()
            .take_while(|character| character.is_ascii_alphanumeric() || *character == '_')
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        assert_eq!(temp_name, "_b", "key temp name: {code}");
        assert_eq!(
            code.matches(" = key").count(),
            1,
            "key evaluates once into a temp: {code}"
        );
        assert!(
            code.contains(&format!("[{temp_name}]")),
            "binding reads through the temp: {code}"
        );
    }

    #[test]
    fn derived_constructor_keeps_prologue_before_super() {
        // Upstream constructorWithSuperAndPrologue.es5 (1e40213a): the
        // "ngInject" directive stays in the body ahead of the super call and
        // the super call becomes `return _super.call(this) || this;`.
        let output = emit_at(
            "class B extends A {\n    constructor() {\n        \"ngInject\";\n        console.log(\"B\");\n        super();\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let directive = code.find("ngInject").expect("directive survives");
        let super_call = code.find("super(").expect("super call survives");
        assert!(directive < super_call, "{code}");
    }
    #[test]
    fn a_parameter_property_is_assigned_after_the_super_call() {
        let output = emit_at(
            "class B extends A {\n    constructor(public y: number) {\n        log();\n        super();\n        log();\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        assert_eq!(
            javascript(&output),
            "class B extends A {\n    constructor(y) {\n        log();\n        super();\n        this.y = y;\n        log();\n    }\n}\n"
        );
    }

    #[test]
    fn a_private_field_lives_in_a_weak_map() {
        let output = emit_at(
            "class A {\n    #name: string;\n    constructor(name: string) {\n        this.#name = name;\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var _A_name;\nclass A {\n    constructor(name) {\n        _A_name.set(this, void 0);\n        __classPrivateFieldSet(this, _A_name, name, \"f\");\n    }\n}\n_A_name = new WeakMap();\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_private_method_leaves_the_class_behind_a_brand_check() {
        let output = emit_at(
            "class A1 {\n    #method(param: string): string {\n        return \"\";\n    }\n    constructor() {\n        this.#method(\"\");\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var _A1_instances, _A1_method;\nclass A1 {\n    constructor() {\n        _A1_instances.add(this);\n        __classPrivateFieldGet(this, _A1_instances, \"m\", _A1_method).call(this, \"\");\n    }\n}\n_A1_instances = new WeakSet(), _A1_method = function _A1_method(param) {\n    return \"\";\n};\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_private_accessor_passes_its_getter_or_setter() {
        let output = emit_at(
            "class A1 {\n    get #prop() { return \"\"; }\n    set #prop(param: string) { }\n    constructor() {\n        this.#prop = \"\";\n        console.log(this.#prop);\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "        __classPrivateFieldSet(this, _A1_instances, \"\", \"a\", _A1_prop_set);\n        console.log(__classPrivateFieldGet(this, _A1_instances, \"a\", _A1_prop_get));\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_static_private_field_is_a_value_record_behind_the_class_alias() {
        let output = emit_at(
            "class A {\n    static #myField = \"hello world\";\n    constructor() {\n        console.log(A.#myField);\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.ends_with(
                "var _a, _A_myField;\nclass A {\n    constructor() {\n        console.log(__classPrivateFieldGet(_a, _a, \"f\", _A_myField));\n    }\n}\n_a = A;\n_A_myField = { value: \"hello world\" };\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_compound_private_write_copies_a_receiver_other_than_this() {
        let output = emit_at(
            "class A {\n    #field = 0;\n    constructor() {\n        this.#field += 2;\n        A.getInstance().#field += 2;\n    }\n    static getInstance() {\n        return new A();\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.contains(
                "    constructor() {\n        var _a;\n        _A_field.set(this, 0);\n        __classPrivateFieldSet(this, _A_field, __classPrivateFieldGet(this, _A_field, \"f\") + 2, \"f\");\n        __classPrivateFieldSet(_a = A.getInstance(), _A_field, __classPrivateFieldGet(_a, _A_field, \"f\") + 2, \"f\");\n    }\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn a_private_in_check_asks_the_storage() {
        let output = emit_at(
            "class Foo {\n    #field = 1;\n    check(v: any) {\n        #field in v;\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.contains("        __classPrivateFieldIn(_Foo_field, v);\n"),
            "{code}"
        );
    }
    #[test]
    fn private_destructured_array_evaluates_rhs_before_receiver() {
        let output = emit_at(
            "class C {\n    #x = 0;\n    m(holder: any, rhs: any) {\n        [holder.c.#x] = [rhs()];\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.contains("__classPrivateFieldSet("),
            "private write routes through the setter: {code}"
        );
        assert!(
            !code.contains("__classPrivateFieldSet(holder.c,"),
            "composite receiver is captured, not inlined: {code}"
        );
        assert!(
            !code.contains("#x"),
            "no raw private name survives lowering: {code}"
        );
        let rhs = code.find("rhs()").unwrap_or_else(|| panic!("rhs call emits: {code}"));
        let receiver = code.find("holder.c").unwrap_or_else(|| panic!("receiver emits: {code}"));
        assert!(
            rhs < receiver,
            "right-hand side runs before the receiver capture: {code}"
        );
    }

    #[test]
    fn private_destructured_object_keeps_outer_this() {
        let output = emit_at(
            "class C {\n    #x = 0;\n    m(rhs: any) {\n        ({ a: this.#x } = rhs());\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            !code.contains("__classPrivateFieldSet(this,"),
            "`this` must be captured outside the setter body: {code}"
        );
        assert!(
            code.contains("__classPrivateFieldSet("),
            "private write routes through the setter: {code}"
        );
        assert!(
            !code.contains("#x"),
            "no raw private name survives lowering: {code}"
        );
        let rhs = code.find("rhs()").unwrap_or_else(|| panic!("rhs call emits: {code}"));
        let receiver = code.find("= this").unwrap_or_else(|| panic!("this capture emits: {code}"));
        assert!(
            rhs < receiver,
            "right-hand side runs before the receiver capture: {code}"
        );
    }

    #[test]
    fn private_destructured_nested_parenthesized_target_lowers() {
        let output = emit_at(
            "class C {\n    #x = 0;\n    m(holder: any, rhs: any) {\n        [{ a: (holder.p.#x) }] = [rhs()];\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(
            code.contains("__classPrivateFieldSet("),
            "parenthesized target still lowers: {code}"
        );
        assert!(
            !code.contains("__classPrivateFieldSet(holder.p,"),
            "composite receiver is captured, not inlined: {code}"
        );
        assert!(
            !code.contains("#x"),
            "no raw private name survives lowering: {code}"
        );
        let rhs = code.find("rhs()").unwrap_or_else(|| panic!("rhs call emits: {code}"));
        let receiver = code.find("holder.p").unwrap_or_else(|| panic!("receiver emits: {code}"));
        assert!(
            rhs < receiver,
            "right-hand side runs before the receiver capture: {code}"
        );
    }

    #[test]
    fn private_field_helpers_print_in_first_use_order() {
        let written_first = emit_at(
            "class A {\n    #f = 0;\n    m() {\n        this.#f = 1;\n        return this.#f;\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let read_first = emit_at(
            "class A {\n    #f = 0;\n    m() {\n        this.#f;\n        this.#f = 1;\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let set_then_get = javascript(&written_first);
        let get_then_set = javascript(&read_first);
        assert!(
            set_then_get.find("var __classPrivateFieldSet")
                < set_then_get.find("var __classPrivateFieldGet"),
            "{set_then_get}"
        );
        assert!(
            get_then_set.find("var __classPrivateFieldGet")
                < get_then_set.find("var __classPrivateFieldSet"),
            "{get_then_set}"
        );
    }
    #[test]
    fn transformed_output_is_byte_stable() {
        let source = "class C { x = 1; static y = 2; }\n";
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let options = options_for(ScriptTarget::Es2015).transform_view();
        let names = names();
        assert_eq!(
            emit_transformed(&file, checked.product(), &options, &names),
            emit_transformed(&file, checked.product(), &options, &names)
        );
    }

    #[test]
    fn es5_downlevels_exponentiation_to_math_pow() {
        // Upstream exponentiationOperatorWithAnyAndNumber: every `**`
        // becomes `Math.pow(left, right)` below ES2016, and the nested
        // right-associative form nests the calls.
        let output = emit_at(
            "var a: any;\nvar b: number;\nvar r1 = a ** b;\nvar r2 = b ** 2;\nvar r3 = a ** b ** 2;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow(a, b)"), "{code}");
        assert!(code.contains("Math.pow(b, 2)"), "{code}");
        assert!(code.contains("Math.pow(a, Math.pow(b, 2))"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_downlevels_compound_exponentiation_identifiers() {
        // Upstream compoundExponentiationAssignmentLHSIsReference: identifier
        // targets become `x = Math.pow(x, value)` without temps.
        let output = emit_at(
            "var x = 2;\nvar value = 3;\nx **= value;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("x = Math.pow(x, value)"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_compound_exponentiation_property_lhs_evaluates_base_once() {
        let output = emit_at(
            "var obj = { v: 2 };\nfunction pick() { return obj; }\npick().v **= 3;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("(_a = pick()).v = Math.pow(_a.v, 3)"),
            "{code}"
        );
        assert_eq!(code.matches("_a = pick()").count(), 1, "{code}");
        // Declaration plus the pick return; the lowering never re-evaluates it.
        assert_eq!(code.matches("obj").count(), 2, "{code}");
    }

    #[test]
    fn es5_compound_exponentiation_captures_computed_keys() {
        let output = emit_at(
            "var obj = { a: 2 };\nobj[\"a\"] **= 3;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("(_a = obj)[_b = __propKey(\"a\")] = Math.pow(_a[_b], 3)"),
            "{code}"
        );
    }

    #[test]
    fn es5_declares_compound_exponentiation_temps_in_the_enclosing_function() {
        let output = emit_at(
            "var obj = { v: 2 };\nfunction f() { obj.v **= 3; }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("var _a;"), "{code}");
        assert!(code.contains("(_a = obj).v = Math.pow(_a.v, 3)"), "{code}");
    }

    /// ES5 for-of lowers to the index form and still loops: the
    /// binding lands inside the body, the index bound is the iterable
    /// length, and one pass collects every element.
    #[test]
    fn node_executes_lowered_for_of_collects_every_element() {
        let output = emit_at(
            "var out = [];\nfor (const k of [1, 2, 3]) { out.push(k); }\nfor (const k in { a: 1 }) { out.push(k); }\nconsole.log(out.join(\",\"));\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(!code.contains("of "), "for-of must lower at es5:\n{code}");
        assert!(
            code.contains("var k in"),
            "for-in keeps native form:\n{code}"
        );
        assert!(
            !code.contains("const k"),
            "head bindings convert to var:\n{code}"
        );
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-forof-{nonce}.cjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert!(
            String::from_utf8_lossy(&result.stdout).contains("1,2,3,a"),
            "the loop must collect every element and key:\n{code}"
        );
    }

    #[test]
    fn es5_for_of_assignment_target_keeps_rewritten_iterable() {
        let output = emit_at(
            "async function f() { let x; for (x of await values) {} }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(!code.contains("await values"), "{code}");
        assert!(!code.contains(" of "), "{code}");
        assert!(code.contains("/*yield*/, values]"), "{code}");
        assert!(code.contains("x = _a[_i]"), "{code}");
    }

    #[test]
    fn computed_destructuring_keys_evaluate_after_earlier_properties() {
        let output = emit_at(
            "var { a = first(), [second()]: b, c = third() } = source();\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let position = |needle: &str| {
            code.find(needle)
                .unwrap_or_else(|| panic!("{needle}: {code}"))
        };
        assert!(position("source()") < position("first()"), "{code}");
        assert!(position("first()") < position("second()"), "{code}");
        assert!(position("second()") < position("third()"), "{code}");
    }

    #[test]
    fn node_executes_lowered_compound_exponentiation_with_single_evaluations() {
        let output = emit_at(
            "var calls = 0;\nvar target = { v: 2 };\nfunction base() { calls += 1; return target; }\nfunction key() { calls += 10; return \"v\"; }\nbase()[key()] **= 3;\nconsole.log(calls + \":\" + target.v);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(!code.contains("**"), "{code}");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-exponentiation-{nonce}.cjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        // The base runs once, the key runs once, and `2 ** 3` is `8`.
        assert!(
            String::from_utf8_lossy(&result.stdout).contains("11:8"),
            "{code}"
        );
    }

    #[test]
    fn es2016_preserves_exponentiation_operators() {
        let source = "var r = a ** 2;\na **= 2;\n";
        let es2016_output = emit_at(source, ScriptTarget::Es2016);
        let es2016 = javascript(&es2016_output);
        assert!(es2016.contains("**"), "{es2016}");
        assert!(es2016.contains("**="), "{es2016}");
        assert!(!es2016.contains("Math.pow"), "{es2016}");
        let es2015_output = emit_at(source, ScriptTarget::Es2015);
        let es2015 = javascript(&es2015_output);
        assert!(es2015.contains("Math.pow(a, 2)"), "{es2015}");
        assert!(!es2015.contains("**"), "{es2015}");
    }

    #[test]
    fn es5_lowers_exponentiation_nested_in_expressions() {
        let output = emit_at(
            "var r = flag ? call(a ** 2) : obj[b ** 3];\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow(a, 2)"), "{code}");
        assert!(code.contains("Math.pow(b, 3)"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn analysis_detects_exponentiation_nested_in_expressions() {
        let file = parse("var r = flag ? call(a ** 2) : b **= 3;\n");
        let options = options_for(ScriptTarget::Es5).transform_view();
        let plan = analyze(&file, &options);
        assert!(
            plan.features.contains(&LanguageFeature::Exponentiation),
            "{plan:?}"
        );
        assert!(
            plan.required.contains(&LanguageFeature::Exponentiation),
            "{plan:?}"
        );
        let plain = analyze(&parse("var r = a * b;\n"), &options);
        assert!(!plain.features.contains(&LanguageFeature::Exponentiation));
    }

    #[test]
    fn es5_rewrites_exponentiation_inside_synchronous_arrows() {
        let output = emit_at(
            "var expression = () => 2 ** 3;\n\
             var block = () => { var x = 2; x **= 3; return x; };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("Math.pow").count(), 2, "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_object_literal_members_after_a_computed_name_assign_through_a_temp() {
        let output = emit_at(
            "declare var k: string;\n\
             var o = { a: 1, [k]: 2, m() { return 3; }, get z() { return 0; }, set z(v) { } };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        for expected in [
            "var _a;",
            "var o = (_a = { a: 1 }, _a[k] = 2, _a.m = function () { return 3; }, ",
            r#"Object.defineProperty(_a, "z", { get: function () { return 0; }, set: function (v) { }, enumerable: false, configurable: true }), _a);"#,
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn es5_multi_line_computed_object_literal_prints_one_element_per_line() {
        let output = emit_at("var o = {\n    [\"\" || 0]: 0\n};\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("var _a;\nvar o = (_a = {},\n    _a[\"\" || 0] = 0,\n    _a);\n"),
            "{code}"
        );
    }

    #[test]
    fn es5_shorthand_properties_and_methods_become_plain_properties() {
        let output = emit_at(
            "var x = 1;\nvar o = { x, m() { return x; } };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("var o = { x: x, m: function () { return x; } };"),
            "{code}"
        );
    }

    #[test]
    fn es5_arrows_become_function_expressions() {
        let output = emit_at(
            "var f = (x) => x + 1;\nvar g = () => { return 1; };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("var f = function (x) { return x + 1; };"),
            "{code}"
        );
        assert!(
            code.contains("var g = function () { return 1; };"),
            "{code}"
        );
        assert!(!code.contains("=>"), "{code}");
    }

    #[test]
    fn es5_arrow_reads_this_and_arguments_from_captures_in_the_enclosing_function() {
        let output = emit_at(
            "function outer() {\n    var a = () => () => this.x;\n    var b = () => arguments[0];\n    var c = function () { return () => this; };\n}\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        for expected in [
            "function outer() {\n    var _this = this;\n    var _arguments = arguments;\n",
            "var a = function () { return function () { return _this.x; }; };",
            "var b = function () { return _arguments[0]; };",
            "var c = function () {\n        var _this = this;\n        return function () { return _this; };\n    };",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn es5_arrow_at_the_top_level_captures_this_before_everything() {
        let output = emit_at("var h = () => this;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("var _this = this;\nvar h = function () { return _this; };"),
            "{code}"
        );
    }

    #[test]
    fn es2015_keeps_arrows() {
        let output = emit_at("var f = (x) => x + this.y;\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("var f = (x) => x + this.y;"), "{code}");
    }

    #[test]
    fn es5_class_becomes_a_constructor_function_with_prototype_members() {
        let output = emit_at(
            "class C {\n    static foo() { }\n    get x() {\n        return 1;\n    }\n    bar() { }\n}\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let expected = "var C = /** @class */ (function () {\n    function C() {\n    }\n    C.foo = function () { };\n    Object.defineProperty(C.prototype, \"x\", {\n        get: function () {\n            return 1;\n        },\n        enumerable: false,\n        configurable: true\n    });\n    C.prototype.bar = function () { };\n    return C;\n}());\n";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_derived_class_calls_super_through_this_returned_by_the_super_call() {
        let output = emit_at(
            "class C { static bar() { } baz() { } }\nclass D extends C {\n    static foo() {\n        super.bar();\n    }\n    constructor() {\n        super();\n        super.baz();\n    }\n}\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let expected = "var D = /** @class */ (function (_super) {\n    __extends(D, _super);\n    function D() {\n        var _this = _super.call(this) || this;\n        _super.prototype.baz.call(_this);\n        return _this;\n    }\n    D.foo = function () {\n        _super.bar.call(this);\n    };\n    return D;\n}(C));\n";
        assert!(code.contains(expected), "{code}");
        assert!(code.contains("var __extends = "), "{code}");
    }

    #[test]
    fn es5_derived_class_without_a_constructor_forwards_its_arguments() {
        let output = emit_at("class B { }\nclass E extends B { }\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("    function E() {\n        return _super !== null && _super.apply(this, arguments) || this;\n    }\n"),
            "{code}"
        );
    }

    #[test]
    fn es5_parameter_properties_and_field_initializers_assign_in_the_constructor() {
        let output = emit_at(
            "class B { constructor(public x: number) { } }\nclass D extends B {\n    z = 1;\n    w = () => this.z;\n    constructor(a: number, public y: number) { super(a); }\n}\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("    function B(x) {\n        this.x = x;\n    }\n"),
            "{code}"
        );
        assert!(
            code.contains("        var _this = _super.call(this, a) || this;\n        _this.y = y;\n        _this.z = 1;\n        _this.w = function () { return _this.z; };\n        return _this;\n"),
            "{code}"
        );
    }

    #[test]
    fn es5_base_class_arrows_in_field_initializers_capture_this_in_the_constructor() {
        let output = emit_at("class F { v = () => this.v; }\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("    function F() {\n        var _this = this;\n        this.v = function () { return _this.v; };\n    }\n"),
            "{code}"
        );
    }

    #[test]
    fn es5_static_members_follow_the_methods_inside_the_class_function() {
        let output = emit_at(
            "class F { m() { } static t = 1; static { F.t++; } }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("    F.prototype.m = function () { };\n    F.t = 1;\n    (function () { F.t++; })();\n    return F;\n"),
            "{code}"
        );
    }

    #[test]
    fn es5_class_expressions_and_default_exports_name_their_constructor() {
        let output = emit_at(
            "var G = class { };\nexport class X { }\nexport default class { }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        for expected in [
            "var G = /** @class */ (function () {\n    function class_1() {\n    }\n    return class_1;\n}());\n",
            "export var X = /** @class */ (function () {\n    function X() {\n    }\n    return X;\n}());\n",
            "var default_1 = /** @class */ (function () {\n    function default_1() {\n    }\n    return default_1;\n}());\nexport default default_1;\n",
        ] {
            assert!(code.contains(expected), "missing {expected}: {code}");
        }
    }

    #[test]
    fn es2015_keeps_class_syntax() {
        let output = emit_at(
            "class C extends B { m() { return super.m(); } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("class C extends B {"), "{code}");
        assert!(code.contains("return super.m();"), "{code}");
    }

    #[test]
    fn es2015_keeps_object_literal_syntax() {
        let output = emit_at(
            "var x = 1, k = 2;\nvar o = { x, [k]: 1, m() { } };\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("{ x, [k]: 1, m() { } }"), "{code}");
    }

    #[test]
    fn es5_rewrites_exponentiation_inside_parameter_initializers() {
        let output = emit_at(
            "function f(x = 2 ** 3) { return x; }\n\
             var g = (x = 3 ** 2) => x;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("Math.pow").count(), 2, "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_captures_computed_identifier_keys_before_getters() {
        let output = emit_at(
            "var key = \"a\";\n\
             var obj = { get a() { key = \"b\"; return 2; } };\n\
             obj[key] **= 3;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("(_a = obj)[_b = __propKey(key)] = Math.pow(_a[_b], 3)"),
            "{code}"
        );
    }

    #[test]
    fn es5_compound_exponentiation_coerces_computed_key_once() {
        let output = emit_at(
            "var coercions = 0;\n\
             var property = Symbol(\"x\");\n\
             var key = {};\n\
             key[Symbol.toPrimitive] = function (hint) {\n\
                 coercions += 1;\n\
                 if (hint !== \"string\") throw new Error(\"wrong hint\");\n\
                 return property;\n\
             };\n\
             var obj = {};\n\
             obj[property] = 2;\n\
             obj[key] **= 3;\n\
             console.log(coercions + \":\" + obj[property]);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "1:8\n", "{code}");
    }

    #[test]
    fn es5_property_key_conversion_reads_ordinary_method_once() {
        let output = emit_at(
            "var reads = 0;\n\
             var calls = 0;\n\
             var key = {};\n\
             Object.defineProperty(key, \"toString\", {\n\
                 get: function () {\n\
                     reads += 1;\n\
                     return function () { calls += 1; return \"x\"; };\n\
                 }\n\
             });\n\
             var obj = { x: 2 };\n\
             obj[key] **= 2;\n\
             console.log(reads + \":\" + calls + \":\" + obj.x);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "1:1:4\n", "{code}");
    }

    #[test]
    fn es5_property_key_conversion_without_symbol_uses_ordinary_methods() {
        let output = emit_at(
            "var Symbol = void 0;\n\
             var key = {};\n\
             var obj = { \"[object Object]\": 2 };\n\
             obj[key] **= 3;\n\
             console.log(obj[\"[object Object]\"]);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "8\n", "{code}");
    }

    #[test]
    fn imported_helpers_keep_exact_property_key_conversion_inline() {
        let mut options = options_for(ScriptTarget::Es5);
        options.import_helpers = true;
        options.module = Some(ModuleKind::CommonJs);
        let output = emit_with_options(
            "var property = Symbol(\"x\");\n\
             var key = {};\n\
             key[Symbol.toPrimitive] = function () { return property; };\n\
             var obj = {};\n\
             obj[property] = 2;\n\
             obj[key] **= 3;\n\
             console.log(obj[property]);\n",
            options,
        );
        let code = javascript(&output);
        assert!(code.contains("function __propKey"), "{code}");
        assert!(!code.contains("require(\"tslib\").__propKey"), "{code}");
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "8\n", "{code}");
    }

    #[test]
    fn es2015_static_super_exponentiation_uses_math_pow() {
        let output = emit_at(
            "class Base { static x = 2; }\n\
             class Derived extends Base { static m() { super.x **= 3; } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }
    #[test]
    fn es2015_static_block_super_exponentiation_uses_math_pow() {
        let output = emit_at(
            "class Base { static x = 2; }\n\
             class Derived extends Base { static { super.x **= 3; } }\n\
             console.log(Derived.x);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow"), "{code}");
        assert!(!code.contains("**"), "{code}");
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "8\n", "{code}");
    }

    #[test]
    fn es5_parameter_compound_exponentiation_is_reentrant() {
        let output = emit_at(
            "var depth = 0;\n\
             var outer = { x: 2 };\n\
             var inner = { x: 5 };\n\
             function update(target, key, value = target[key] **= 2) { return value; }\n\
             var reentrant = {};\n\
             reentrant[Symbol.toPrimitive] = function () {\n\
                 if (depth++ === 0) update(inner, \"x\");\n\
                 return \"x\";\n\
             };\n\
             console.log(update(outer, reentrant) + \":\" + outer.x + \":\" + inner.x);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&result.stdout),
            "4:4:25\n",
            "{code}"
        );
    }

    #[test]
    fn import_equals_qualified_alias_is_not_a_module_and_gets_use_strict() {
        let source = "import I = A.B.C;\n";
        let file = parse(source);
        assert!(
            !crate::checker::source_is_module(&file),
            "import I = A.B.C (qualified alias) must not make the file a module"
        );
        let output = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.starts_with("\"use strict\";\n"),
            "a script with alwaysStrict must start with use strict: {code}"
        );
    }

    #[test]
    fn import_equals_require_is_a_module_and_takes_no_prologue_under_es2015() {
        let source = "import I = require(\"m\");\n";
        let file = parse(source);
        assert!(
            crate::checker::source_is_module(&file),
            "import I = require(\"m\") must make the file a module"
        );
        let output = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Es2015),
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            !code.starts_with("\"use strict\";\n"),
            "an ES2015 module takes no strict prologue even under alwaysStrict: {code}"
        );
    }

    #[test]
    fn cjs_plan_for_qualified_alias_emits_no_require_or_esmodule_marker() {
        let source = "import I = A.B.C;\n";
        let output = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            !code.contains("__esModule"),
            "a qualified alias must not trigger the __esModule marker: {code}"
        );
        assert!(
            !code.contains("require("),
            "a qualified alias must not emit a require call: {code}"
        );
    }

    #[test]
    fn es5_lowers_nullish_coalescing_identifier_to_the_conditional_form() {
        // Rule: `a ?? b` lowers below ES2020 to `a !== null && a !== void 0 ? a : b`.
        // Proven by baseline `nullishCoalescingOperator1.js` (default ES5
        // target): `const aa1 = a1 !== null && a1 !== void 0 ? a1 : 'whatever';`.
        // Counterexample-side check: `optionalChainingInArrow(target=es2015).js`
        // keeps the lowered form at ES2015, so the gate is ES2020, not ES2015.
        // This test fails without the production change: the pre-change
        // rewriter passed `??` through verbatim.
        let output = emit_at("const out = a1 ?? 'whatever';\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("a1 !== null && a1 !== void 0 ? a1 : 'whatever'"),
            "{code}"
        );
        assert!(!code.contains("??"), "{code}");
    }

    #[test]
    fn es2020_keeps_nullish_coalescing_native() {
        // Same rule's at-and-above-threshold side: `LanguageFeature::
        // NullishCoalescing::since()` is `ScriptTarget::Es2020`, so at ES2020
        // the native `??` survives unchanged (tsc gates emitNullishCoalescing
        // on `languageVersion >= ES2020`).
        let output = emit_at("const out = a1 ?? 'whatever';\n", ScriptTarget::Es2020);
        let code = javascript(&output);
        assert!(code.contains("a1 ?? 'whatever'"), "{code}");
        assert!(!code.contains("a1 !== null"), "{code}");
    }

    #[test]
    fn es5_nullish_coalescing_captures_non_identifier_operands_once() {
        // A non-identifier left operand must evaluate exactly once, captured
        // through an expression temp — tsc emits
        // `var _t; (_t = f()) !== null && _t !== void 0 ? _t : rhs`.
        let output = emit_at("const out = f() ?? 'x';\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert_eq!(code.matches("f()").count(), 1, "f() must run once: {code}");
        assert!(code.contains("!== null &&"), "{code}");
        assert!(!code.contains("??"), "{code}");
    }

    #[test]
    fn es5_lowers_nullish_assignment_to_the_conditional_assignment_form() {
        // Rule: `a ??= b` lowers below ES2021 to
        // `a !== null && a !== void 0 ? a : (a = b)`.
        // Proven by baseline
        // `equalityWithtNullishCoalescingAssignment(strict=false).js`:
        // `a !== null && a !== void 0 ? a : (a = true);`.
        let output = emit_at("let a = false;\na ??= true;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("a !== null && a !== void 0 ? a : (a = true)"),
            "{code}"
        );
        assert!(!code.contains("??="), "{code}");
    }

    #[test]
    fn es5_lowers_or_and_and_assignment_to_expanded_logical_form() {
        // Rule: `a ||= b` → `a || (a = b)` and `a &&= b` → `a && (a = b)`
        // below ES2021 (tsc's emitLogicalAssignment expansion).
        let output = emit_at("let a = 0;\na ||= 1;\na &&= 2;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(code.contains("a || (a = 1)"), "{code}");
        assert!(code.contains("a && (a = 2)"), "{code}");
        assert!(!code.contains("||="), "{code}");
        assert!(!code.contains("&&="), "{code}");
    }

    #[test]
    fn es2021_keeps_logical_assignment_native() {
        // `LanguageFeature::LogicalAssignment::since()` is Es2021: at ES2021
        // the operators survive verbatim.
        let output = emit_at("let a = 0;\na ||= 1;\n", ScriptTarget::Es2021);
        let code = javascript(&output);
        assert!(code.contains("a ||= 1"), "{code}");
    }

    #[test]
    fn es5_member_target_logical_assignment_captures_the_base_once() {
        // Member targets base-capture through an expression temp so the
        // object evaluates once: tsc's form is
        // `(_t = obj).p || ((_t.p) = rhs)` with the capture in the READ
        // position (JS evaluates a logical chain's left operand first).
        let output = emit_at("let o = { p: 0 };\no.p ||= 1;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(code.contains("(_a = o).p || (_a.p = 1)"), "{code}");
        assert!(!code.contains("||="), "{code}");
    }

    #[test]
    fn es2020_keeps_optional_chaining_native_but_es5_lowers_it() {
        // Rule: `a?.b` lowers below ES2020 to
        // `a === null || a === void 0 ? void 0 : a.b`.
        // Proven by baseline `optionalChainingInArrow(target=es5).js`:
        // `names === null || names === void 0 ? void 0 : names.filter(...)`;
        // the `target=esnext` variant of the same case
        // (`optionalChainingInParameterBindingPattern(target=esnext).js`)
        // exists on the at-threshold side.
        let lowered = emit_at("const v = names?.filter(f);\n", ScriptTarget::Es5);
        let lowered_code = javascript(&lowered);
        assert!(
            lowered_code.contains("names === null || names === void 0 ? void 0 :"),
            "{lowered_code}"
        );
        assert!(
            !lowered_code.contains("?.") || lowered_code.contains("\"use strict\""),
            "{lowered_code}"
        );
        let native = emit_at("const v = names?.filter(f);\n", ScriptTarget::Es2020);
        assert!(
            javascript(&native).contains("names?.filter(f)"),
            "{native:?}"
        );
    }

    fn commonjs_at(source: &str, target: ScriptTarget) -> String {
        let output = emit_with_options(
            source,
            EmitOptions {
                target,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        javascript(&output).to_owned()
    }

    #[test]
    fn a_lowered_write_to_an_exported_variable_goes_to_exports() {
        // A variable exported where it is declared has no local: upstream's module
        // transform runs after these lowerings and rewrites what they produce.
        for (source, lowered) in [
            ("a ||= 1;", "exports.a || (exports.a = 1);"),
            ("a &&= 1;", "exports.a && (exports.a = 1);"),
            (
                "a ??= 1;",
                "exports.a !== null && exports.a !== void 0 ? exports.a : (exports.a = 1);",
            ),
            ("a **= 2;", "exports.a = Math.pow(exports.a, 2);"),
        ] {
            let code = commonjs_at(
                &format!("export var a: any = 0;\n{source}\n"),
                ScriptTarget::Es5,
            );
            assert!(code.contains(lowered), "{code}");
        }
    }

    #[test]
    fn lowered_destructuring_writes_an_exported_variable_through_exports() {
        let code = commonjs_at(
            "export var a: any = 0;\nvar o: any = {};\nexport var s: any = [1];\n[a] = [2];\n({ a } = { a: 3 });\n[o.x] = [4];\n[o.y] = s;\n",
            ScriptTarget::Es5,
        );
        assert!(!code.contains("\na = "), "{code}");
        assert!(code.contains("exports.a = _"), "{code}");
        assert!(!code.contains("= s;"), "{code}");
    }

    #[test]
    fn lowered_destructuring_publishes_a_local_exported_by_a_specifier() {
        let code = commonjs_at(
            "var a: any = 0;\nexport { a, a as b };\n[a] = [2];\n",
            ScriptTarget::Es5,
        );
        assert!(code.contains("exports.b = exports.a = a = _"), "{code}");
    }

    #[test]
    fn a_lowered_write_to_a_namespace_member_goes_to_the_namespace() {
        let code = commonjs_at(
            "export namespace N {\n    export var a: any = 0;\n    a ||= 1;\n    a **= 2;\n}\n",
            ScriptTarget::Es5,
        );
        assert!(code.contains("N.a || (N.a = 1);"), "{code}");
        assert!(code.contains("N.a = Math.pow(N.a, 2);"), "{code}");
    }

    /// What Node prints for the CommonJS output of `source`, then `report`.
    fn node_prints(source: &str, target: ScriptTarget, report: &str) -> String {
        let code = commonjs_at(source, target);
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-cjs-{nonce}.cjs"));
        std::fs::write(&path, format!("{code}\n{report}\n")).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        String::from_utf8(result.stdout)
            .expect("Node stdout")
            .trim()
            .to_owned()
    }

    const EMIT_TARGETS: [ScriptTarget; 3] = [
        ScriptTarget::Es5,
        ScriptTarget::Es2015,
        ScriptTarget::Es2020,
    ];

    #[test]
    fn node_executes_lowered_writes_to_exported_variables() {
        let source = r#"
export var a: any = 0;
export let b: any = 1;
var c: any = 0;
export { c };
export var s: any = [20, 21];
var o: any = {};
export { o };
a ||= 5;
b &&= 6;
c ??= 7;
a **= 2;
[b] = [8];
({ c } = { c: 9 });
var d: any;
[d, o.e] = s;
"#;
        let report =
            "console.log(JSON.stringify([exports.a, exports.b, exports.c, exports.o, d]));";
        for target in EMIT_TARGETS {
            assert_eq!(
                node_prints(source, target, report),
                r#"[25,8,9,{"e":21},20]"#
            );
        }
    }

    #[test]
    fn node_executes_a_for_of_that_writes_exported_variables() {
        let source = r#"
export var a: any = 0;
export var b: any = 0;
for (a of [1, 2]) {}
for ([b] of [[3], [4]]) {}
"#;
        let report = "console.log(JSON.stringify([exports.a, exports.b]));";
        for target in EMIT_TARGETS {
            assert_eq!(node_prints(source, target, report), "[2,4]");
        }
    }

    /// tsc 7.0.2 prints a loop head that writes a local of `export { c }` as it stands,
    /// so `exports.c` keeps its value. Parity keeps that gap.
    #[test]
    fn a_loop_head_does_not_publish_a_local_exported_by_a_specifier() {
        let source = "var c: any = 0;\nexport { c };\nfor (c of [5, 6]) {}\n";
        for target in [ScriptTarget::Es2015, ScriptTarget::Es2020] {
            assert!(
                commonjs_at(source, target).contains("for (c of [5, 6]) { }"),
                "{target:?}"
            );
            let report = "console.log(JSON.stringify(exports.c));";
            assert_eq!(node_prints(source, target, report), "0");
        }
    }

    #[test]
    fn node_executes_the_rest_of_an_array_assignment() {
        let source = r#"
export var a: any, b: any, c: any, d: any, e: any, f: any;
[a, ...b] = [1, 2, 3];
[, ...c] = [4, 5];
[d, ...[e]] = [6, 7, 8];
[...f] = [9];
"#;
        let report = "console.log(JSON.stringify([exports.a, exports.b, exports.c, exports.d, exports.e, exports.f]));";
        for target in EMIT_TARGETS {
            assert_eq!(node_prints(source, target, report), "[1,[2,3],[5],6,7,[9]]");
        }
    }

    #[test]
    fn a_string_named_constructor_is_the_constructor() {
        // quotedConstructors.js: a string with the value `constructor` makes the
        // constructor, whatever its escapes, and a computed name is a method.
        let code = javascript(&emit_at(
            "class C {\n    \"constructor\"() { }\n}\nclass D {\n    '\\x63onstructor'() { }\n}\nclass E {\n    ['constructor']() { }\n}\nclass F {\n    'constructors'() { }\n}\n",
            ScriptTarget::Es2015,
        ))
        .to_owned();
        assert_eq!(code.matches("    constructor() { }").count(), 2, "{code}");
        assert!(code.contains("]() { }"), "{code}");
        assert!(code.contains("'constructors'() { }"), "{code}");
    }

    #[test]
    fn node_esm_import_assignment_prints_the_create_require_prelude_once() {
        let output = emit_with_options(
            "import a = require(\"a\");\nimport b = require(\"b\");\na;\nb;\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::EsNext),
                node_module_mode: true,
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&output),
            "import { createRequire as _createRequire } from \"module\";\n\
             const __require = _createRequire(import.meta.url);\n\
             const a = __require(\"a\");\n\
             const b = __require(\"b\");\n\
             a;\n\
             b;\n"
        );
    }

    #[test]
    fn node_esm_export_import_assignment_publishes_the_binding() {
        let output = emit_with_options(
            "export import fs2 = require(\"fs\");\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::EsNext),
                node_module_mode: true,
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&output),
            "import { createRequire as _createRequire } from \"module\";\n\
             const __require = _createRequire(import.meta.url);\n\
             const fs2 = __require(\"fs\");\n\
             export { fs2 };\n"
        );
    }

    #[test]
    fn node_esm_unused_import_assignment_prints_no_prelude() {
        let output = emit_with_options(
            "import fs = require(\"fs\");\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::EsNext),
                node_module_mode: true,
                ..EmitOptions::default()
            },
        );
        assert_eq!(javascript(&output), "export {};\n");
    }

    #[test]
    fn node_esm_require_names_stay_clear_of_authored_names() {
        let output = emit_with_options(
            "const __require = null;\nconst _createRequire = null;\n\
             import fs = require(\"fs\");\nfs.readFile;\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::EsNext),
                node_module_mode: true,
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&output),
            "import { createRequire as _createRequire_1 } from \"module\";\n\
             const __require_1 = _createRequire_1(import.meta.url);\n\
             const __require = null;\n\
             const _createRequire = null;\n\
             const fs = __require_1(\"fs\");\n\
             fs.readFile;\n"
        );
    }

    #[test]
    fn node_cjs_format_file_keeps_plain_require() {
        let output = emit_with_options(
            "import fs = require(\"fs\");\nfs.readFile;\n",
            EmitOptions {
                target: ScriptTarget::Es2022,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                node_module_mode: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("const fs = require(\"fs\");"), "{code}");
        assert!(!code.contains("_createRequire"), "{code}");
        assert!(!code.contains("__require"), "{code}");
    }

    #[test]
    fn node_esm_es5_target_declares_the_require_binding_with_var() {
        let output = emit_with_options(
            "import foo = require(\"foo\");\nfoo;\n",
            EmitOptions {
                target: ScriptTarget::Es5,
                module: Some(crate::emitter::ModuleKind::EsNext),
                node_module_mode: true,
                ..EmitOptions::default()
            },
        );
        assert_eq!(
            javascript(&output),
            "import { createRequire as _createRequire } from \"module\";\n\
             var __require = _createRequire(import.meta.url);\n\
             var foo = __require(\"foo\");\n\
             foo;\n"
        );
    }
