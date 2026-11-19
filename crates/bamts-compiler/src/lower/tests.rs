    use super::{
        BigIntTextError, CaptureKey, ConstEnumOperation, ContainerKind, IteratorCloseMode,
        LowerError, LowerErrorKind, LowerOptions, UnsupportedConstruct, canonical_bigint_text,
        lower, lower_checked, value_read_names,
    };
    use crate::checker::{ProgramCheckInput, ResolvedModuleEdge, check, check_program};
    use crate::literal::cook_escapes;
    use crate::parser::parse;
    use crate::scanner::scan;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;
    fn repository_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("repository root is readable")
    }
    fn script_kind(path: &str) -> ScriptKind {
        if path.ends_with(".d.ts")
            || path.ends_with(".ts")
            || path.ends_with(".mts")
            || path.ends_with(".cts")
        {
            ScriptKind::TypeScript
        } else if path.ends_with(".tsx") {
            ScriptKind::TypeScriptReact
        } else if path.ends_with(".js") || path.ends_with(".mjs") || path.ends_with(".cjs") {
            ScriptKind::JavaScript
        } else if path.ends_with(".jsx") {
            ScriptKind::JavaScriptReact
        } else {
            panic!("declared corpus source has unsupported extension: {path}");
        }
    }
    fn declared_corpus_sources(root: &Path) -> Vec<String> {
        let manifest = fs::read_to_string(root.join("corpus/manifest.toml"))
            .expect("corpus manifest is readable");
        let mut sources = BTreeSet::new();
        for line in manifest.lines() {
            if let Some(value) = quoted_value(line, "entrypoint") {
                sources.insert(value);
            }
        }
        let specs = root.join("corpus/specs");
        for entry in fs::read_dir(&specs).expect("corpus specs directory is readable") {
            let path = entry.expect("spec directory entry").path();
            if path.extension().and_then(|extension| extension.to_str()) != Some("toml") {
                continue;
            }
            let text = fs::read_to_string(&path).expect("corpus spec is UTF-8");
            let start = text
                .find("source_files")
                .unwrap_or_else(|| panic!("{} has no source_files", path.display()));
            let array = &text[start..];
            let open = array
                .find('[')
                .expect("source_files has an opening bracket");
            let close = array[open + 1..]
                .find(']')
                .map(|index| open + 1 + index)
                .expect("source_files has a closing bracket");
            let contents = &array[open + 1..close];
            for item in contents.split(',') {
                let item = item.trim();
                if item.is_empty() {
                    continue;
                }
                let value = item
                    .strip_prefix('"')
                    .and_then(|item| item.strip_suffix('"'))
                    .unwrap_or_else(|| {
                        panic!(
                            "{} has malformed source_files item `{item}`",
                            path.display()
                        )
                    });
                sources.insert(value.to_owned());
            }
        }
        for local_case in [
            "corpus/cases/derived-construction.ts",
            "corpus/cases/event-loop.ts",
            "corpus/cases/explicit-resource.ts",
            "corpus/cases/for-await-iterator.ts",
            "corpus/cases/import-meta.ts",
            "corpus/cases/lexical-environment.ts",
            "corpus/cases/top-level-throw.ts",
        ] {
            assert!(
                sources.contains(local_case),
                "local corpus case {local_case} is a declared corpus member"
            );
        }
        assert_eq!(
            sources.len(),
            70,
            "the checked corpus contract is 70 sources: upstream entrypoints and \
             spec-declared project files plus the seven named local cases"
        );
        sources.into_iter().collect()
    }
    fn quoted_value(line: &str, key: &str) -> Option<String> {
        let line = line.trim();
        let value = line
            .strip_prefix(key)?
            .trim_start()
            .strip_prefix('=')?
            .trim();
        Some(value.strip_prefix('"')?.strip_suffix('"')?.to_owned())
    }
    #[test]
    fn cooking_preserves_lone_surrogate_units() {
        assert_eq!(cook_escapes("\\uD800").as_units(), [0xD800]);
        assert_eq!(cook_escapes("\\uD83D\\uDE03").as_units(), [0xD83D, 0xDE03]);
        assert_eq!(cook_escapes("\\u{1F603}").as_units(), [0xD83D, 0xDE03]);
    }
    #[test]
    fn all_declared_corpus_sources_lower_to_verified_modules() {
        let root = repository_root();
        let sources = declared_corpus_sources(&root);
        let mut failures = Vec::new();
        for (index, relative) in sources.iter().enumerate() {
            let path = root.join(relative);
            let text = fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("{} is unreadable: {error}", path.display()));
            let source =
                Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
            let scanned = scan(SourceId::new(index as u32), script_kind(relative), source);
            let parsed = parse(scanned);
            match lower(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                    ..LowerOptions::default()
                },
            ) {
                Ok(module) => {
                    assert!(
                        module.certificate(module.entry()).is_some(),
                        "{relative}: entry is verified"
                    );
                }
                Err(error) => failures.push(format!("{relative}: {error}")),
            }
        }
        assert!(
            failures.is_empty(),
            "{}/{} declared corpus sources failed lowering:\n{}",
            failures.len(),
            sources.len(),
            failures.join("\n")
        );
    }
    use bamts_bytecode::{
        BinaryOp, Constant, ConstantId, DecodeLimits, Function, Instruction, IntrinsicErrorKind,
        IteratorKind, Module, Pc, RESUME_RETURN, RESUME_THROW, Register, UnaryOp, Verified,
        decode_verified,
    };
    fn lower_js_result(src: &str) -> Result<Module<Verified>, LowerError> {
        let source = Arc::new(
            SourceText::new(src.to_owned()).expect("test source fits the per-file budget"),
        );
        let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
        let parsed = parse(scanned);
        lower(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
        )
    }
    fn lower_js(src: &str) -> Module<Verified> {
        lower_js_result(src).expect("snippet lowers to a verified module")
    }
    #[test]
    fn a_parenthesized_name_or_member_lowers_for_every_assignment_operator() {
        lower_js(
            "var x = 1, o = { a: 1 }; (x) += 1; ((x)) **= 2; (o.a) *= 2; (o['a']) ??= 1; (x) &&= 3;",
        );
    }
    #[test]
    fn a_call_target_lowers_to_the_call_and_a_reference_error() {
        for (statement, message) in [
            ("f() = 1;", "Invalid left-hand side in assignment"),
            ("f() += 1;", "Invalid left-hand side in assignment"),
            ("(f()) = 1;", "Invalid left-hand side in assignment"),
            ("(f()) += 1;", "Invalid left-hand side in assignment"),
            (
                "++f();",
                "Invalid left-hand side expression in prefix operation",
            ),
            (
                "f()--;",
                "Invalid left-hand side expression in postfix operation",
            ),
            ("for (f() in {}) {}", "Invalid left-hand side in for-loop"),
            ("for (f() of []) {}", "Invalid left-hand side in for-loop"),
            ("(a?.b)() = 1;", "Invalid left-hand side in assignment"),
        ] {
            let module = lower_js(&format!("function f() {{}} {statement}"));
            assert!(
                module.constants().iter().any(
                    |constant| matches!(constant, Constant::String(text) if text.eq_ascii(message))
                ),
                "{statement}"
            );
        }
        for statement in [
            "f() &&= 1;",
            "f() ??= 1;",
            "f?.() = 1;",
            "1 = 2;",
            "a?.b() = 1;",
            "a?.b() += 1;",
            "a?.b()++;",
            "++a?.b();",
            "for (a?.b() of []) {}",
            "a?.b.c() = 1;",
            "a?.b()() = 1;",
        ] {
            assert!(
                lower_js_result(&format!("function f() {{}} {statement}")).is_err(),
                "{statement}"
            );
        }
    }
    #[test]
    fn strict_global_writes_test_the_binding_without_reading_it() {
        let global_ops = |src: &str, name: &str| {
            let source = Arc::new(SourceText::new(src.to_owned()).expect("small test source"));
            let parsed = parse(scan(SourceId::new(0), ScriptKind::JavaScript, source));
            let module = lower(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                    ..LowerOptions::default()
                },
            )
            .expect("snippet lowers to a verified module");
            let constants = module.constants();
            let named = |id: ConstantId| matches!(&constants[id.get() as usize], Constant::String(text) if text.eq_ascii(name));
            module.functions()[module.entry().get() as usize]
                .code()
                .iter()
                .filter_map(|instruction| match *instruction {
                    Instruction::LoadGlobal { name, .. } if named(name) => Some("load"),
                    Instruction::RequireGlobalBinding { name } if named(name) => Some("require"),
                    Instruction::StoreGlobal { name, .. } if named(name) => Some("store"),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            global_ops("'use strict'; x = 1;", "x"),
            ["require", "store"]
        );
        assert_eq!(
            global_ops("'use strict'; y += 1;", "y"),
            ["load", "require", "store"]
        );
        assert_eq!(global_ops("q = 5;", "q"), ["store"]);
    }
    #[test]
    fn language_errors_never_read_a_global_error_constructor() {
        for (src, kind, message) in [
            (
                "class C {} C();",
                IntrinsicErrorKind::TypeError,
                "Class constructor C cannot be invoked without 'new'",
            ),
            (
                "class B {} class D extends B { m() { delete super.x; } }",
                IntrinsicErrorKind::ReferenceError,
                "Unsupported reference to 'super'",
            ),
            (
                "function f() {} f() = 1;",
                IntrinsicErrorKind::ReferenceError,
                "Invalid left-hand side in assignment",
            ),
        ] {
            let module = lower_js(src);
            let constants = module.constants();
            let names = |id: ConstantId, wanted: &[&str]| matches!(&constants[id.get() as usize], Constant::String(text) if wanted.iter().any(|name| text.eq_ascii(name)));
            let code = || {
                module
                    .functions()
                    .iter()
                    .flat_map(|function| function.code())
            };
            assert!(
                !code().any(|instruction| matches!(*instruction, Instruction::LoadGlobal { name, .. } if names(name, &["TypeError", "ReferenceError"]))),
                "{src}"
            );
            assert!(
                code().any(|instruction| matches!(*instruction, Instruction::ThrowIntrinsicError { kind: thrown, message: text } if thrown == kind && names(text, &[message]))),
                "{src}"
            );
        }
    }
    #[test]
    fn class_call_messages_name_only_statically_named_classes() {
        let plural = "Class constructors cannot be invoked without 'new'";
        for (src, message) in [
            ("(class {})();", plural),
            ("({['c' + 'k']: class {}}).ck();", plural),
            ("({['ck']: class {}}).ck();", plural),
            ("const o: any = {}; o.p = class {}; o.p();", plural),
            ("[class {}][0]();", plural),
            (
                "({ck: class {}}).ck();",
                "Class constructor ck cannot be invoked without 'new'",
            ),
            (
                "const K = class {}; K();",
                "Class constructor K cannot be invoked without 'new'",
            ),
            (
                "export default class {}",
                "Class constructor default cannot be invoked without 'new'",
            ),
            (
                "export default (class {});",
                "Class constructor default cannot be invoked without 'new'",
            ),
        ] {
            let module = lower_js(src);
            let constants = module.constants();
            let messages: Vec<String> = module
                .functions()
                .iter()
                .flat_map(|function| function.code())
                .filter_map(|instruction| match *instruction {
                    Instruction::ThrowIntrinsicError { message, .. } => {
                        match &constants[message.get() as usize] {
                            Constant::String(text) => Some(text.to_utf8_lossy().to_string()),
                            _ => None,
                        }
                    }
                    _ => None,
                })
                .collect();
            assert_eq!(messages, [message], "{src}");
        }
    }
    #[test]
    fn class_decorators_lower_in_reverse_and_bind_the_final_class_once() {
        let module = lower_js(
            "function first() {} function second() { return class Replacement {} } @second @first class C {}",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::Call { callee, .. } if is_decorator_application_call(code, index) => {
                    Some((index, callee))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            calls.len(),
            2,
            "both class decorator applications occur at class definition time"
        );
        assert!(
            code[..calls[0].0]
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadConst { .. })),
            "decorator expressions are evaluated before application"
        );
        assert!(calls[0].0 < calls[1].0, "decorators apply in reverse order");
        let constants = module.constants();
        let store_globals: Vec<_> = code
            .iter()
            .filter(|instruction| match instruction {
                Instruction::StoreGlobal { name, .. } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value) if value.eq_ascii("C")
                ),
                _ => false,
            })
            .collect();
        assert_eq!(
            store_globals.len(),
            1,
            "the class declaration binds the final decorated constructor once"
        );
        assert!(
            any_instruction(&module, |instruction| matches!(
                instruction,
                Instruction::CreateCell { .. }
            )),
            "the class keeps its TDZ cell"
        );
    }
    #[test]
    fn a_this_parameter_takes_no_argument() {
        let module = lower_js("function f(this: any, a: number) { return a; }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.parameter_count() > 0)
            .expect("the function has a parameter");
        assert_eq!(function.parameter_count(), 1);
    }
    #[test]
    fn checker_diagnosed_super_misuse_lowers_to_inert_values() {
        // The checker rejects every one of these (BAMTS-C024..C027); lowering
        // must still produce a verified module for diagnosed sources instead
        // of failing.
        for src in [
            "function f() { super(); }",
            "super;",
            "let x = super;",
            "class A { constructor() { super(); } }",
            "class A extends Object { constructor() { super(); const g = () => super(); } }",
            "class A extends Object { m() { super(); } }",
            "class A extends Object { f = () => super(); constructor() { super(); } }",
        ] {
            lower_js(src);
        }
    }
    #[test]
    fn parameter_decorators_are_rejected() {
        let error = lower_js_result(
            "function marker() {} class C { constructor(@marker first, @marker second) {} }",
        )
        .expect_err("parameter decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ParameterDecorator)
        );
        let error = lower_js_result("function marker() {} function f(@marker x) { return x; }")
            .expect_err("function parameter decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ParameterDecorator)
        );
        let error =
            lower_js_result("function marker() {} class C { method(@marker x) { return x; } }")
                .expect_err("method parameter decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ParameterDecorator)
        );
        let error = lower_js_result("function marker() {} class C { @marker constructor() {} }")
            .expect_err("constructor decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ConstructorDecorator)
        );
    }
    #[test]
    fn decorated_class_expressions_return_the_replacement() {
        let module = lower_js(
            "function replace() { return class Replacement {} } const C = @replace class Named {} new C();",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let call_count = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .count();
        assert_eq!(call_count, 1, "the expression class decorator applies once");
        assert!(
            any_instruction(&module, |instruction| matches!(
                instruction,
                Instruction::Construct { .. }
            )),
            "the decorated expression result is constructed"
        );
    }
    #[test]
    fn decorated_fields_apply_in_source_order_with_one_computed_key() {
        let module = lower_js(
            "function key() { return 'x'; } function dec(target, key) { return target[key]; } class C { @dec static [key()] = 1; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(code, *index) == Some(0)
                    && call_loads_global(code, constants, *index, "key")
            })
            .map(|(index, _)| index)
            .collect();
        let apply_calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(key_calls.len(), 1, "computed key expression evaluates once");
        assert_eq!(
            apply_calls.len(),
            1,
            "field decorator application occurs once"
        );
        let (raw_ctor, _) = class_raw_ctor_and_prototype(code, constants);
        let installation = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::SetProperty { object, .. }
                    if *object == raw_ctor && index > apply_calls[0] =>
                {
                    Some(index)
                }
                _ => None,
            })
            .expect("decorated static field installs its captured key");
        assert!(
            key_calls[0] < apply_calls[0],
            "key evaluation precedes decorator application"
        );
        assert!(
            apply_calls[0] < installation,
            "decorator application precedes static field installation"
        );
    }
    #[test]
    fn decorated_instance_field_uses_the_same_captured_key_and_receives_no_replacement() {
        let module = lower_js(
            "function key() { return 'x'; } function dec(target, key) { return target[key]; } class C { @dec\n[key()]; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(code, *index) == Some(0)
                    && call_loads_global(code, constants, *index, "key")
            })
            .count();
        let apply_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .count();
        assert_eq!(key_calls, 1, "computed-key expression evaluates once");
        assert_eq!(
            apply_calls, 1,
            "instance field decorator application occurs once at class definition time"
        );
        let entry_index = module.entry().get() as usize;
        let constructor = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, function)| {
                *index != entry_index
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .map(|(_, function)| function)
            .expect("instance field still initializes in the constructor");
        assert!(
            !constructor
                .code()
                .iter()
                .enumerate()
                .any(|(index, instruction)| {
                    matches!(instruction, Instruction::Call { .. })
                        && is_decorator_application_call(constructor.code(), index)
                }),
            "decorator application remains class-definition time"
        );
    }
    #[test]
    fn decorated_auto_accessor_key_evaluates_once_before_installation() {
        let module = lower_js(
            "function key() { return 'x'; } function dec(target, key) { return target[key]; } class C { @dec accessor [key()] = 1; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(code, *index) == Some(0)
                    && call_loads_global(code, constants, *index, "key")
            })
            .count();
        let apply_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .count();
        assert_eq!(key_calls, 1, "key expression evaluates once");
        assert_eq!(
            apply_calls, 1,
            "auto-accessor decorator application occurs once"
        );
    }
    #[test]
    fn field_decorator_initializer_flag_is_definite_on_every_merge_path() {
        let module = lower_js(
            "function dec(_value, _context) { return undefined; } class C { @dec x = 1; }",
        );
        assert!(
            module.functions()[module.entry().get() as usize]
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Call { .. })),
            "field decorator application occurs in the entry function"
        );
    }
    #[test]
    fn add_initializer_helper_seeds_its_return_register_before_branching() {
        let module = lower_js("function dec() {} class C { @dec m() {} }");
        let helper = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 2
                    && function.parameter_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. }))
            })
            .expect("member context emits an addInitializer helper");
        let Instruction::Return { value } = helper.code().last().expect("trailing return") else {
            panic!("addInitializer ends with Return");
        };
        let return_reg = *value;
        let seeded_before_branch = helper
            .code()
            .iter()
            .take_while(|instruction| {
                !matches!(
                    instruction,
                    Instruction::JumpIfFalse { .. }
                        | Instruction::JumpIfTrue { .. }
                        | Instruction::Jump { .. }
                )
            })
            .any(|instruction| {
                matches!(
                    instruction,
                    Instruction::LoadConst { dst, .. } | Instruction::Move { dst, .. }
                        if *dst == return_reg
                )
            });
        assert!(
            seeded_before_branch,
            "addInitializer return register must be seeded before the open/closed split"
        );
    }
    #[test]
    fn member_decorator_stages_drain_before_class_decorators_in_pinned_order() {
        let module = lower_js(
            "function static_method() {} \
             function instance_method() {} \
             function static_field() {} \
             function instance_field() {} \
             function class_decorator() {} \
             @class_decorator class C { \
                 @static_method static m() {} \
                 @static_field static x = 1; \
                 @instance_method m() {} \
                 @instance_field x = 1; \
             }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let application_calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(
            application_calls.len(),
            5,
            "four member decorators and one class decorator apply at class definition time"
        );
        let expected = [
            "static_method",
            "instance_method",
            "static_field",
            "instance_field",
            "class_decorator",
        ];
        for (call_index, &expected_name) in application_calls.iter().zip(expected.iter()) {
            assert!(
                call_loads_global(code, constants, *call_index, expected_name),
                "decorator application call at index {call_index} must load global \
                 `{expected_name}`"
            );
        }
    }
    #[test]
    fn mixed_source_order_member_decorator_and_key_staging() {
        let module = lower_js(
            "function a() { return 'a'; }             function b() { return 'b'; }             function c() { return 'c'; }             function dec(_value, _context) {}             class C {                 [a()] = 0;                 @dec
[b()] = 0;                 static [c()] = 0;             }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_call = |name: &str| -> usize {
            code.iter()
                .enumerate()
                .find_map(|(index, instruction)| {
                    matches!(instruction, Instruction::Call { .. })
                        .then_some(())
                        .filter(|_| call_arity(code, index) == Some(0))
                        .filter(|_| call_loads_global(code, constants, index, name))
                        .map(|_| index)
                })
                .unwrap_or_else(|| panic!("missing key call for {name}"))
        };
        let a = key_call("a");
        let b = key_call("b");
        let c = key_call("c");
        assert!(
            a < b && b < c,
            "computed keys evaluate in source order: a < b < c"
        );
        let apply = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    .then_some(index)
                    .filter(|&index| is_decorator_application_call(code, index))
            })
            .expect("decorated member applies once");
        assert!(
            c < apply,
            "all key evaluations precede decorator application"
        );
    }
    #[test]
    fn plain_computed_field_key_evaluated_once_at_class_definition() {
        let module = lower_js("function key() { return 'x'; } class C { [key()] = 1 } new C();");
        let entry_index = module.entry().get() as usize;
        let entry = module.functions()[entry_index].code();
        let constants = module.constants();
        let entry_key_calls = entry
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(entry, *index) == Some(0)
                    && call_loads_global(entry, constants, *index, "key")
            })
            .count();
        assert_eq!(
            entry_key_calls, 1,
            "plain computed key evaluates once at class definition"
        );
        let constructor = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, function)| {
                *index != entry_index
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .map(|(_, function)| function)
            .expect("plain instance field initializes in the constructor");
        assert!(
            !constructor
                .code()
                .iter()
                .enumerate()
                .any(|(index, instruction)| {
                    matches!(instruction, Instruction::Call { .. })
                        && call_arity(constructor.code(), index) == Some(0)
                        && call_loads_global(constructor.code(), constants, index, "key")
                }),
            "constructor must reuse the staged key instead of re-evaluating it"
        );
        assert!(
            constructor
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::SetProperty { .. })),
            "constructor still assigns the plain field"
        );
    }
    #[test]
    fn constructor_captures_accessor_initializer_not_stored_key() {
        let module = lower_js("function outer() { let x = 1; return class { accessor y = x; }; }");
        let constructor = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() >= 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .expect("accessor constructor captures outer state and class elements");
        assert_eq!(
            constructor.capture_count(),
            2,
            "constructor captures initializer free var and class_elements"
        );
        let set_property = constructor
            .code()
            .iter()
            .position(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            .expect("accessor writes backing field");
        assert!(
            constructor.code()[..set_property]
                .iter()
                .any(|instruction| { matches!(instruction, Instruction::GetProperty { .. }) }),
            "captured initializer loads through a cell before the backing-field write"
        );
    }
    fn function_has_name(module: &Module<Verified>, function: &Function, expected: &str) -> bool {
        let Some(name) = function.name() else {
            return false;
        };
        matches!(
            &module.constants()[name.get() as usize],
            Constant::String(value) if value.eq_ascii(expected)
        )
    }
    fn global_load_call_index(code: &[Instruction], constants: &[Constant], name: &str) -> usize {
        let load_pc = code
            .iter()
            .position(|instruction| match instruction {
                Instruction::LoadGlobal { name: global, .. } => matches!(
                    &constants[global.get() as usize],
                    Constant::String(value) if value.eq_ascii(name)
                ),
                _ => false,
            })
            .unwrap_or_else(|| panic!("missing LoadGlobal for {name}"));
        let Instruction::LoadGlobal { dst, .. } = code[load_pc] else {
            unreachable!();
        };
        code.iter()
            .enumerate()
            .skip(load_pc + 1)
            .find_map(|(index, instruction)| match instruction {
                Instruction::Call { callee, .. } if *callee == dst => Some(index),
                _ => None,
            })
            .unwrap_or_else(|| panic!("missing direct call of {name}"))
    }
    fn is_empty_variadic_call(code: &[Instruction], call_index: usize) -> bool {
        let Some(Instruction::Call {
            callee, arguments, ..
        }) = code.get(call_index)
        else {
            return false;
        };
        let Some(Instruction::CreateArray { dst: arguments_reg }) =
            call_index.checked_sub(1).and_then(|index| code.get(index))
        else {
            return false;
        };
        if arguments_reg != arguments {
            return false;
        }
        let Some(Instruction::GetProperty {
            dst: callee_reg, ..
        }) = call_index.checked_sub(2).and_then(|index| code.get(index))
        else {
            return false;
        };
        callee_reg == callee
    }
    fn call_arity(code: &[Instruction], call_index: usize) -> Option<usize> {
        let Instruction::Call { arguments, .. } = code.get(call_index)? else {
            return None;
        };
        let mut arity = 0usize;
        for index in (0..call_index).rev() {
            match &code[index] {
                Instruction::ArrayPush { array, .. } if array == arguments => arity += 1,
                Instruction::CreateArray { dst } if dst == arguments => return Some(arity),
                Instruction::CreateArray { .. } | Instruction::Call { .. } => return None,
                _ => {}
            }
        }
        None
    }
    fn is_decorator_application_call(code: &[Instruction], call_index: usize) -> bool {
        call_arity(code, call_index) == Some(2)
    }
    fn call_loads_global(
        code: &[Instruction],
        constants: &[Constant],
        call_index: usize,
        name: &str,
    ) -> bool {
        let Some(Instruction::Call { callee, .. }) = code.get(call_index) else {
            return false;
        };
        code[..call_index]
            .iter()
            .rev()
            .any(|instruction| match instruction {
                Instruction::LoadGlobal { dst, name: global } if dst == callee => matches!(
                    &constants[global.get() as usize],
                    Constant::String(value) if value.eq_ascii(name)
                ),
                _ => false,
            })
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct QueuedInitializerDrain {
        call_index: usize,
        queue: Register,
    }
    fn queued_initializer_drains(code: &[Instruction]) -> Vec<QueuedInitializerDrain> {
        code.iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                if !matches!(instruction, Instruction::Call { .. }) {
                    return None;
                }
                if !is_empty_variadic_call(code, index) {
                    return None;
                }
                let Instruction::GetProperty { object: queue, .. } = code[index - 2] else {
                    return None;
                };
                Some(QueuedInitializerDrain {
                    call_index: index,
                    queue,
                })
            })
            .collect()
    }
    fn class_extra_initializer_queue_register(code: &[Instruction]) -> Register {
        code.iter()
            .enumerate()
            .rev()
            .find_map(|(index, instruction)| {
                let Instruction::CreateArray { dst: queue } = instruction else {
                    return None;
                };
                if !matches!(code.get(index + 1), Some(Instruction::CreateCell { .. })) {
                    return None;
                }
                if index > 0 && matches!(code[index - 1], Instruction::CreateArray { .. }) {
                    return None;
                }
                Some(*queue)
            })
            .expect("class decoration allocates an extra-initializer queue")
    }
    fn drains_for_queue<'a>(
        drains: &'a [QueuedInitializerDrain],
        queue: Register,
    ) -> impl Iterator<Item = &'a QueuedInitializerDrain> + 'a {
        drains.iter().filter(move |drain| drain.queue == queue)
    }
    fn key_name(code: &[Instruction], constants: &[Constant], register: Register) -> String {
        let id = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::LoadConst { dst, constant } if *dst == register => Some(constant),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no LoadConst defines key register {register:?}"));
        match &constants[id.get() as usize] {
            Constant::String(value) => value
                .to_utf8_strict()
                .expect("compiler-interned property key is well-formed UTF-16"),
            other => panic!("expected a string constant for the key, got {other:?}"),
        }
    }
    fn class_raw_ctor_and_prototype(
        code: &[Instruction],
        constants: &[Constant],
    ) -> (Register, Register) {
        let (raw_ctor, prototype, constructor_key) = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::DefineDataProperty { object, key, value }
                    if key_name(code, constants, *key) == "constructor" =>
                {
                    Some((*value, *object, *key))
                }
                _ => None,
            })
            .expect("class lowering emits tag48 for prototype.constructor");
        assert_eq!(
            key_name(code, constants, constructor_key),
            "constructor",
            "tag48 key register must evaluate to the string \"constructor\""
        );
        assert!(
            code.iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::DefineDataProperty { object, key, value }
                        if *object == raw_ctor
                            && *value == prototype
                            && key_name(code, constants, *key) == "prototype"
                )
            }),
            "the same raw ctor installs `.prototype` pointing at that object"
        );
        (raw_ctor, prototype)
    }
    fn assert_class_prototype_constructor_links_raw_ctor(module: &Module<Verified>) {
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let tag48 = code
            .iter()
            .find(|instruction| match instruction {
                Instruction::DefineDataProperty { key, .. } => {
                    key_name(code, constants, *key) == "constructor"
                }
                _ => false,
            })
            .expect("entry function contains tag48 prototype.constructor");
        let (prototype, constructor_key, raw_ctor) = match tag48 {
            Instruction::DefineDataProperty { object, key, value } => (*object, *key, *value),
            _ => unreachable!("filter matched DefineDataProperty"),
        };
        assert_eq!(
            key_name(code, constants, constructor_key),
            "constructor",
            "resolved tag48 key constant is \"constructor\""
        );
        assert!(
            !code.iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::SetProperty { object, key, .. }
                        if *object == prototype
                            && key_name(code, constants, *key) == "constructor"
                )
            }),
            "class prototype.constructor must not use ordinary SetProperty"
        );
        let (discovered_raw, discovered_proto) = class_raw_ctor_and_prototype(code, constants);
        assert_eq!(
            (discovered_raw, discovered_proto),
            (raw_ctor, prototype),
            "helper object/value flow matches the located tag48"
        );
        assert_eq!(
            discovered_raw, raw_ctor,
            "prototype.constructor value is the raw source constructor"
        );
    }
    #[test]
    fn named_class_prototype_constructor_refers_to_raw_ctor() {
        assert_class_prototype_constructor_links_raw_ctor(&lower_js("class C {}"));
    }
    #[test]
    fn anonymous_class_prototype_constructor_refers_to_raw_ctor() {
        assert_class_prototype_constructor_links_raw_ctor(&lower_js("const C = class {};"));
    }
    #[test]
    fn decorated_class_prototype_constructor_refers_to_raw_ctor_not_replacement() {
        let module = lower_js(
            "function replace() { return class R {}; } @replace class C { static x = this; }",
        );
        assert_class_prototype_constructor_links_raw_ctor(&module);
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let (raw_ctor, _) = class_raw_ctor_and_prototype(code, constants);
        let final_class = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::StoreGlobal { name, value } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value_name) if value_name.eq_ascii("C")
                )
                .then_some(*value),
                _ => None,
            })
            .expect("the decorated class declaration binds the replacement constructor");
        assert_ne!(
            raw_ctor, final_class,
            "class replacement must leave raw ctor and final class in distinct registers"
        );
    }
    #[test]
    fn named_class_constructor_carries_source_name_metadata() {
        let module = lower_js("class C {}");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "C")),
            "named class constructor metadata uses the source class name"
        );
        let anonymous = lower_js("(0, class {});");
        assert!(
            anonymous
                .functions()
                .iter()
                .all(|function| function.name().is_none()),
            "a class with nothing to name it keeps empty function metadata"
        );
        let inferred = lower_js("const C = class {};");
        assert!(
            inferred
                .functions()
                .iter()
                .any(|function| function_has_name(&inferred, function, "C")),
            "a class initializing a binding takes the binding's name"
        );
        let expression = lower_js("const C = class Named {};");
        assert!(
            expression
                .functions()
                .iter()
                .any(|function| function_has_name(&expression, function, "Named")),
            "named class expressions thread the expression name into constructor metadata"
        );
    }
    #[test]
    fn decorated_named_class_keeps_raw_constructor_name_metadata() {
        let module =
            lower_js("function replace() { return class Replacement {} } @replace class Named {}");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "Named")),
            "class decorators still see the non-empty raw constructor name"
        );
        assert!(
            module.functions().iter().any(|function| function_has_name(
                &module,
                function,
                "Replacement"
            )),
            "replacement constructors keep their own source names"
        );
    }
    #[test]
    fn static_initializers_capture_final_class_as_lexical_this() {
        let module = lower_js("class C { static x = this; static { this; } }");
        let entry = &module.functions()[module.entry().get() as usize];
        assert!(
            !entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "static field and block this lower through final_class, not LoadThis"
        );
        assert!(
            entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::SetProperty { .. })),
            "static field still installs on the class"
        );
    }
    #[test]
    fn class_extra_initializers_run_after_static_inits_in_source_order() {
        let module = lower_js(
            "function runClassExtra() {} \
             function runStaticField() {} \
             function runStaticBlock() {} \
             function dec(_value, context) { context.addInitializer(runClassExtra); } \
             @dec class C { \
               static x = (runStaticField(), 0); \
               static { runStaticBlock(); } \
             }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let static_field_call = global_load_call_index(code, constants, "runStaticField");
        let static_block_call = global_load_call_index(code, constants, "runStaticBlock");
        let class_queue = class_extra_initializer_queue_register(code);
        let drains = queued_initializer_drains(code);
        let mut drains_by_queue: std::collections::BTreeMap<Register, Vec<usize>> =
            std::collections::BTreeMap::new();
        for drain in &drains {
            drains_by_queue
                .entry(drain.queue)
                .or_default()
                .push(drain.call_index);
        }
        for (queue, call_indices) in &drains_by_queue {
            assert_eq!(
                call_indices.len(),
                1,
                "initializer queue {queue:?} must drain exactly once, got {call_indices:?}"
            );
        }
        let class_drains: Vec<_> = drains_for_queue(&drains, class_queue).collect();
        assert_eq!(
            class_drains.len(),
            1,
            "class-level addInitializer runs exactly one queued callback"
        );
        let class_extra_call = class_drains[0].call_index;
        for member_drain in drains.iter().filter(|drain| drain.queue != class_queue) {
            assert!(
                member_drain.call_index < static_block_call,
                "member extra-initializer drains must precede static blocks"
            );
        }
        assert!(
            static_field_call < static_block_call,
            "static field initializers precede static blocks"
        );
        assert!(
            static_block_call < class_extra_call,
            "static blocks precede class-level extra initializers"
        );
        assert!(
            static_field_call < class_extra_call,
            "all static initializers precede class-level extra initializers"
        );
    }
    #[test]
    fn decorated_replacement_static_this_uses_final_class_capture() {
        let module = lower_js(
            "function replace() { return class R {}; } @replace class C { static x = this; }",
        );
        let entry = &module.functions()[module.entry().get() as usize];
        assert!(
            !entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "replaced-class static initializers still capture lexical this from final_class"
        );
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "C")),
            "raw decorated constructor metadata remains named"
        );
    }
    #[test]
    fn decorated_replacement_static_field_installs_on_raw_ctor_but_this_is_final_class() {
        let module = lower_js(
            "function replace() { return class R {}; } @replace class C { static x = this; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let (raw_ctor, _) = class_raw_ctor_and_prototype(code, constants);
        let final_class = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::StoreGlobal { name, value } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value_name) if value_name.eq_ascii("C")
                )
                .then_some(*value),
                _ => None,
            })
            .expect("the decorated class declaration binds the replacement constructor");
        assert_ne!(
            raw_ctor, final_class,
            "class replacement must leave raw ctor and final class in distinct registers"
        );
        let (install_index, install_object) = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::SetProperty { object, key, .. }
                    if *object == raw_ctor && key_name(code, constants, *key) == "x" =>
                {
                    Some((index, *object))
                }
                _ => None,
            })
            .expect("static field x installs after decoration");
        assert_eq!(
            install_object, raw_ctor,
            "decorated replacement static fields own the raw constructor object"
        );
        assert!(
            code[..install_index].iter().any(|instruction| matches!(
                instruction,
                Instruction::Call { this_value, .. } if *this_value == final_class
            )),
            "static initializer-chain Call uses final_class as this before field install"
        );
    }
    #[test]
    fn instance_method_this_still_loads_activation_this() {
        let module = lower_js("class C { m() { return this; } }");
        assert!(
            module.functions().iter().any(|function| {
                function.name().is_none()
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::LoadThis { .. }))
            }),
            "instance this stays activation-loaded"
        );
    }
    #[test]
    fn export_default_named_class_keeps_raw_constructor_metadata() {
        let module = lower_js("export default class Named {}");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "Named")),
            "export default class C still threads AST class.name into constructor metadata"
        );
    }
    #[test]
    fn computed_keys_and_decorator_expressions_keep_enclosing_this() {
        let computed = lower_js("class C { static [this] = 1; }");
        let computed_entry = &computed.functions()[computed.entry().get() as usize];
        assert!(
            computed_entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "computed keys evaluate with enclosing this, not final_class"
        );
        let decorated = lower_js("function d(v) { return (x) => x; } @d(this) class C {}");
        let decorated_entry = &decorated.functions()[decorated.entry().get() as usize];
        assert!(
            decorated_entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "decorator expressions evaluate with enclosing this, not final_class"
        );
        let static_this = lower_js("class C { static x = this; }");
        let static_entry = &static_this.functions()[static_this.entry().get() as usize];
        assert!(
            !static_entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "deferred static field this still captures final_class only"
        );
    }
    #[test]
    fn raise_type_error_is_a_bare_throw_without_constructor_lookup() {
        let module = lower_js("function dec() { return 42; } @dec class C {}");
        let constants = module.constants();
        let code = module.functions()[module.entry().get() as usize].code();
        let loads_type_error = |instructions: &[Instruction]| {
            instructions.iter().any(|instruction| match instruction {
                Instruction::LoadGlobal { name, .. } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value) if value.eq_ascii("TypeError")
                ),
                _ => false,
            })
        };
        assert!(
            !loads_type_error(code),
            "decorator type errors must not resolve the TypeError global"
        );
        let function_type = code
            .iter()
            .position(|instruction| match instruction {
                Instruction::LoadConst { constant, .. } => matches!(
                    &constants[constant.get() as usize],
                    Constant::String(value) if value.eq_ascii("function")
                ),
                _ => false,
            })
            .expect("callable validation loads \"function\"");
        let error_path = &code[function_type..];
        let throw_pc = error_path
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .expect("type error path calls the non-callable offender");
        let error_prefix = &error_path[..=throw_pc];
        assert!(
            !error_prefix
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Construct { .. })),
            "type error lowering must not construct a user-visible TypeError"
        );
        assert!(
            !loads_type_error(error_prefix),
            "type error lowering must not read the TypeError name"
        );
        assert!(
            !error_prefix
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Throw { .. })),
            "type error lowering uses a bare engine throw, not an explicit Throw of a constructed value"
        );
    }
    #[test]
    fn escaped_add_initializer_after_close_takes_type_error_path_not_append() {
        let module = lower_js(
            "let escaped; function dec(_value, context) { escaped = context.addInitializer; } @dec class C {}",
        );
        let constants = module.constants();
        let entry = module.functions()[module.entry().get() as usize].code();
        let helper = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 2
                    && function.parameter_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. }))
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::JumpIfFalse { .. }))
            })
            .expect("class context emits an addInitializer helper");
        let code = helper.code();
        let gate = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::JumpIfFalse { .. }))
            .expect("open/closed gate");
        let Instruction::JumpIfFalse { target, .. } = code[gate] else {
            unreachable!();
        };
        let open_entry = target.get() as usize;
        let closed_arm = &code[gate + 1..open_entry];
        let open_arm = &code[open_entry..];
        assert!(
            closed_arm
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Call { .. })),
            "closed arm calls a non-callable to throw an engine-origin TypeError"
        );
        assert!(
            !closed_arm
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Construct { .. })),
            "closed arm must not construct a user-visible TypeError"
        );
        assert!(
            !closed_arm.iter().any(|instruction| matches!(
                instruction,
                Instruction::ArrayPush {
                    array,
                    ..
                } if array.get() == 0
            )),
            "closed arm must not append to the captured initializer queue (r0)"
        );
        assert!(
            !closed_arm.iter().any(|instruction| matches!(
                instruction,
                Instruction::Unary {
                    op: UnaryOp::TypeOf,
                    ..
                }
            )),
            "closed state throws before callable validation"
        );
        assert!(
            open_arm.iter().any(|instruction| matches!(
                instruction,
                Instruction::Unary {
                    op: UnaryOp::TypeOf,
                    ..
                }
            )),
            "open arm still validates that the callback is callable"
        );
        assert!(
            open_arm
                .iter()
                .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. })),
            "open arm appends a callable callback"
        );
        let (cell, create_pc) = entry
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::CreateCell { dst } => {
                    let pushed = entry.iter().any(|candidate| {
                        matches!(
                            candidate,
                            Instruction::ArrayPush { value, .. } if value == dst
                        )
                    });
                    let closed = entry.iter().any(|candidate| match candidate {
                        Instruction::SetProperty { object, value, .. } if object == dst => {
                            entry.iter().any(|prior| {
                                matches!(
                                    prior,
                                    Instruction::LoadConst {
                                        dst: load_dst,
                                        constant,
                                    } if load_dst == value
                                        && matches!(
                                            &constants[constant.get() as usize],
                                            Constant::Boolean(true)
                                        )
                                )
                            })
                        }
                        _ => false,
                    });
                    (pushed && closed).then_some((*dst, index))
                }
                _ => None,
            })
            .expect("decoration state cell is captured and later closed");
        let push_pc = entry
            .iter()
            .position(|instruction| {
                matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell)
            })
            .expect("state cell is pushed into the helper captures array");
        let close_pc = entry
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, instruction)| match instruction {
                Instruction::SetProperty { object, value, .. } if *object == cell => entry
                    .iter()
                    .any(|prior| {
                        matches!(
                            prior,
                            Instruction::LoadConst { dst, constant }
                                if dst == value
                                    && matches!(
                                        &constants[constant.get() as usize],
                                        Constant::Boolean(true)
                                    )
                        )
                    })
                    .then_some(index),
                _ => None,
            })
            .expect("state cell is closed with true");
        let decorator_call = entry[create_pc..close_pc]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .map(|offset| create_pc + offset)
            .expect("class decorator applies while the queue is open");
        assert!(
            create_pc < push_pc && push_pc < decorator_call && decorator_call < close_pc,
            "shared state cell is captured before application and closed after it"
        );
    }

    #[test]
    fn class_decoration_state_cell_stores_false_before_decorator_call_and_true_after() {
        let module = lower_js(
            "let escaped; function dec(_value, context) { escaped = context.addInitializer; } @dec class C {}",
        );
        let constants = module.constants();
        let entry = module.functions()[module.entry().get() as usize].code();
        let store_positions = |cell: Register, expected: bool| {
            entry
                .iter()
                .enumerate()
                .filter_map(|(index, instruction)| match instruction {
                    Instruction::SetProperty { object, value, .. }
                        if *object == cell
                            && entry.iter().any(|candidate| {
                                matches!(
                                    candidate,
                                    Instruction::LoadConst { dst, constant }
                                        if *dst == *value
                                            && matches!(
                                                &constants[constant.get() as usize],
                                                Constant::Boolean(actual) if *actual == expected
                                            )
                                )
                            }) =>
                    {
                        Some(index)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let candidates: Vec<(Register, usize)> = entry
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::CreateCell { dst } => {
                    let captured = entry.iter().any(|candidate| {
                        matches!(candidate, Instruction::ArrayPush { value, .. } if value == dst)
                    });
                    (captured && !store_positions(*dst, true).is_empty()).then_some((*dst, index))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            candidates.len(),
            1,
            "the empty class has one captured, subsequently closed decoration state cell"
        );
        let (cell, create_pc) = candidates[0];
        let open_store = *store_positions(cell, false)
            .first()
            .expect("state cell is seeded open with false before any decorator runs");
        let close_store = *store_positions(cell, true)
            .last()
            .expect("state cell is closed with true");
        let capture_push = entry
            .iter()
            .position(|instruction| {
                matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell)
            })
            .expect("state cell is captured by the addInitializer helper");
        let decorator_call = entry[capture_push..close_store]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .map(|offset| capture_push + offset)
            .expect("class decorator is called while the state cell is open");
        assert!(
            create_pc < open_store && open_store < capture_push,
            "state cell is seeded after allocation and before helper capture"
        );
        assert!(
            open_store < decorator_call && decorator_call < close_store,
            "state cell is open for class decoration and closes afterwards"
        );
    }

    #[test]
    fn using_captures_disposer_before_binding_and_disposes_on_normal_exit() {
        let module = lower_js("{ using value = acquire(); consume(value); }");
        let code = module.functions()[0].code();
        let acquire = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .expect("initializer evaluates once");
        let capture_offset = code[acquire..]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("capture follows evaluation");
        let captured = acquire + capture_offset;
        let (method, kind, src) = match code[captured] {
            Instruction::DisposeCapture {
                method,
                kind,
                src,
                hint: bamts_bytecode::DisposeHint::Sync,
            } => (method, kind, src),
            _ => unreachable!(),
        };
        let body_call = code[captured + 1..]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .map(|offset| captured + 1 + offset)
            .expect("body runs after capture");
        let disposal = code[body_call + 1..]
            .windows(2)
            .position(|window| {
                matches!(
                    &window[1],
                    Instruction::Call {
                        callee,
                        this_value,
                        ..
                    } if callee == &method && this_value == &src
                ) && matches!(&window[0], Instruction::CreateArray { .. })
            })
            .map(|offset| body_call + 1 + offset + 1)
            .expect("normal exit calls the captured method on the bound value");
        let skip = code[..disposal]
            .windows(2)
            .enumerate()
            .find_map(|(index, window)| match window {
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        left,
                        ..
                    },
                    Instruction::JumpIfTrue { condition, target },
                ] if left == &kind => Some((index + 1, *condition, target.get() as usize)),
                _ => None,
            })
            .expect("nullish kind equality feeds a JumpIfTrue skip");
        let (_jump_pc, _condition, target) = skip;
        assert!(
            target > disposal,
            "nullish kind jumps past the disposal call (polarity fixed)"
        );
        assert!(
            module.functions()[0]
                .handlers()
                .iter()
                .any(|handler| handler.start.get() <= (body_call as u32)
                    && handler.end.get() > body_call as u32),
            "body completion is captured for disposal"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn using_disposes_multiple_resources_in_lifo_order() {
        let module = lower_js("{ using outer = acquireOuter(); using inner = acquireInner(); }");
        let code = module.functions()[0].code();
        let captures = code
            .iter()
            .enumerate()
            .filter_map(|(pc, instruction)| match instruction {
                Instruction::DisposeCapture { method, src, .. } => Some((pc, *method, *src)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(captures.len(), 2, "each initializer captures one record");
        let outer_call = code
            .iter()
            .enumerate()
            .skip(captures[0].0 + 1)
            .filter(|(_, instruction)| {
                matches!(instruction, Instruction::Call { callee, this_value, .. }
                    if callee == &captures[0].1 && this_value == &captures[0].2)
            })
            .map(|(pc, _)| pc)
            .next()
            .expect("outer disposal is emitted");
        let inner_call = code
            .iter()
            .enumerate()
            .skip(captures[1].0 + 1)
            .filter(|(_, instruction)| {
                matches!(instruction, Instruction::Call { callee, this_value, .. }
                    if callee == &captures[1].1 && this_value == &captures[1].2)
            })
            .map(|(pc, _)| pc)
            .next()
            .expect("inner disposal is emitted");
        assert!(inner_call < outer_call, "records close innermost first");
        assert_round_trips(&module);
    }
    #[test]
    fn missing_sync_disposer_fails_during_capture_before_the_binding_is_used() {
        let module = lower_js("{ using missing = {}; trace(missing); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("missing disposer is validated eagerly by capture");
        let use_call = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .filter(|(_, instruction)| matches!(instruction, Instruction::Call { .. }))
            .map(|(pc, _)| pc)
            .next()
            .expect("the body would observe the binding if capture succeeded");
        assert!(
            capture < use_call,
            "capture runs before any body use, so its TypeError is declaration-time"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn await_using_in_async_function_captures_async_and_awaits_disposal() {
        let module =
            lower_js("async function f() { await using value = acquire(); consume(value); }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_async)
            .expect("async function is present");
        let code = function.code();
        let capture = code
            .iter()
            .position(|instruction| {
                matches!(
                    instruction,
                    Instruction::DisposeCapture {
                        hint: bamts_bytecode::DisposeHint::Async,
                        ..
                    }
                )
            })
            .expect("await using captures with DisposeHint::Async");
        let (method, kind, src) = match code[capture] {
            Instruction::DisposeCapture {
                method,
                kind,
                src,
                hint: bamts_bytecode::DisposeHint::Async,
            } => (method, kind, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Call {
                    callee, this_value, ..
                } if callee == &method && this_value == &src => Some(pc),
                _ => None,
            })
            .expect("async disposal still emits Call for non-nullish kinds");
        let await_pc = code
            .iter()
            .enumerate()
            .skip(disposal)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Await { .. } => Some(pc),
                _ => None,
            })
            .expect("async disposal awaits");
        let handler = function
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= disposal && handler.end.get() as usize > await_pc
            })
            .expect("handler covers Call + Await");
        assert!(handler.start.get() as usize <= disposal);
        assert!(handler.end.get() as usize > await_pc);
        let _ = kind;
        assert_round_trips(&module);
    }

    #[test]
    fn await_using_in_sync_function_is_rejected() {
        let error = lower_js_result("function f() { await using value = acquire(); }")
            .expect_err("await using requires async capability");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::UsingDeclaration)
        );
    }

    #[test]
    fn await_using_at_module_top_level_captures_async() {
        let module = lower_js("await using value = acquire();");
        let code = module.functions()[0].code();
        assert!(
            code.iter().any(|instruction| matches!(
                instruction,
                Instruction::DisposeCapture {
                    hint: bamts_bytecode::DisposeHint::Async,
                    ..
                }
            )),
            "module top-level await using captures async"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn for_using_of_captures_per_iteration_and_disposes_before_next_step() {
        let module = lower_js("for (using value of xs) { consume(value); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| {
                matches!(
                    instruction,
                    Instruction::DisposeCapture {
                        hint: bamts_bytecode::DisposeHint::Sync,
                        ..
                    }
                )
            })
            .expect("loop-head using captures per iteration");
        let next = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::IteratorNext { .. }))
            .expect("for-of steps the iterator");
        let jump_to_head = code
            .iter()
            .enumerate()
            .rev()
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Jump { target } if target.get() as usize <= next => Some(pc),
                _ => None,
            })
            .expect("loop jumps back to the head");
        assert!(
            capture < jump_to_head,
            "capture is inside the per-iteration body"
        );
        let disposal_call = code[capture..jump_to_head]
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Call { .. }));
        assert!(
            disposal_call,
            "per-iteration disposal runs before the next iterator step"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn for_await_using_of_in_async_function_uses_async_capture() {
        let module =
            lower_js("async function f(xs) { for (await using value of xs) { consume(value); } }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_async)
            .expect("async function");
        assert!(
            function.code().iter().any(|instruction| matches!(
                instruction,
                Instruction::DisposeCapture {
                    hint: bamts_bytecode::DisposeHint::Async,
                    ..
                }
            )),
            "loop-head await using captures with Async hint"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn for_await_using_of_in_sync_function_is_rejected() {
        let error = lower_js_result("function f(xs) { for (await using value of xs) {} }")
            .expect_err("loop-head await using requires async capability");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::UsingDeclaration)
        );
    }

    #[test]
    fn async_disposal_awaits_undefined_on_nullish_and_sync_fallback_kinds() {
        let module = lower_js("async function f() { await using value = acquire(); }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_async)
            .expect("async function");
        let code = function.code();
        let capture = code
            .iter()
            .position(|instruction| {
                matches!(
                    instruction,
                    Instruction::DisposeCapture {
                        hint: bamts_bytecode::DisposeHint::Async,
                        ..
                    }
                )
            })
            .expect("async capture");
        let kind = match code[capture] {
            Instruction::DisposeCapture { kind, .. } => kind,
            _ => unreachable!(),
        };
        let kind_equals: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(pc, instruction)| match instruction {
                Instruction::Binary {
                    op: BinaryOp::StrictEqual,
                    left,
                    ..
                } if left == &kind => Some(pc),
                _ => None,
            })
            .collect();
        assert!(
            kind_equals.len() >= 2,
            "async disposal compares capture_kind for nullish skip-call and sync-fallback skip-copy"
        );
        let awaits_after_capture = code[capture..]
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Await { .. }))
            .count();
        assert_eq!(
            awaits_after_capture, 1,
            "formal pattern emits a single Await of the selected awaited register"
        );
        // Ensure kind==2 compare uses JumpIfTrue skip polarity (skip copy).
        let skip_copy = code.windows(2).any(|window| {
            matches!(
                window,
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        left,
                        ..
                    },
                    Instruction::JumpIfTrue { .. }
                ] if left == &kind
            )
        });
        assert!(skip_copy, "kind comparisons use JumpIfTrue skip polarity");
        assert_round_trips(&module);
    }

    #[test]
    fn using_close_disposal_sits_after_the_protected_body() {
        let module = lower_js("{ using value = acquire(); if (value) { trace(value); } }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("resource is captured");
        let (method, src) = match code[capture] {
            Instruction::DisposeCapture { method, src, .. } => (method, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .filter(|(_, instruction)| {
                matches!(instruction, Instruction::Call { callee, this_value, .. }
                if callee == &method && this_value == &src)
            })
            .map(|(pc, _)| pc)
            .next()
            .expect("disposal call is emitted once");
        assert!(
            module.functions()[0].handlers().iter().any(|handler| {
                handler.start.get() > capture as u32 && handler.end.get() as usize <= disposal
            }),
            "the protected body ends before disposal and its handler is disjoint"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn using_disposal_skips_nullish_kind_with_jump_if_true_polarity() {
        let module = lower_js("{ using value = acquire(); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("resource is captured");
        let kind = match code[capture] {
            Instruction::DisposeCapture { kind, .. } => kind,
            _ => unreachable!(),
        };
        let (method, src) = match code[capture] {
            Instruction::DisposeCapture { method, src, .. } => (method, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Call {
                    callee, this_value, ..
                } if callee == &method && this_value == &src => Some(pc),
                _ => None,
            })
            .expect("non-nullish path still emits the disposer call");
        let (eq_pc, jump_pc, target) = code[..disposal]
            .windows(2)
            .enumerate()
            .find_map(|(index, window)| match window {
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        dst,
                        left,
                        ..
                    },
                    Instruction::JumpIfTrue { condition, target },
                ] if left == &kind && condition == dst => {
                    Some((index, index + 1, target.get() as usize))
                }
                _ => None,
            })
            .expect("capture_kind == 0 is tested with JumpIfTrue");
        assert!(eq_pc < jump_pc && jump_pc < disposal);
        assert!(
            target > disposal,
            "kind 0 must skip the disposer call, not enter it"
        );
        assert!(
            !matches!(code[jump_pc], Instruction::JumpIfFalse { .. }),
            "inverted JumpIfFalse polarity is the D1 bug"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn using_disposal_wraps_disposer_call_in_handler_and_emits_suppress_error() {
        let module = lower_js("{ using value = acquire(); consume(value); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("resource is captured");
        let (method, src) = match code[capture] {
            Instruction::DisposeCapture { method, src, .. } => (method, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Call {
                    callee, this_value, ..
                } if callee == &method && this_value == &src => Some(pc),
                _ => None,
            })
            .expect("disposal call is emitted");
        let dispose_handler = module.functions()[0]
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= disposal && handler.end.get() as usize > disposal
            })
            .expect("disposer Call is covered by an ExceptionHandler");
        assert!(
            dispose_handler.handler.get() as usize > disposal,
            "handler body is emitted after the disposer region"
        );
        let handler_pc = dispose_handler.handler.get() as usize;
        let catch_register = dispose_handler.catch_register;
        let suppress = code[handler_pc..]
            .iter()
            .enumerate()
            .find_map(|(offset, instruction)| match instruction {
                Instruction::SuppressError {
                    error, suppressed, ..
                } if error == &catch_register => Some((handler_pc + offset, *suppressed)),
                _ => None,
            })
            .expect("disposer failure path emits SuppressError");
        let (suppress_pc, suppressed) = suppress;
        assert_ne!(
            catch_register, suppressed,
            "SuppressError keeps the prior completion distinct from the disposer error"
        );
        let throw_guard = code[handler_pc..suppress_pc].windows(2).any(|window| {
            matches!(
                window,
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        ..
                    },
                    Instruction::JumpIfFalse { .. }
                ]
            )
        });
        assert!(
            throw_guard,
            "SuppressError is gated on the finally completion kind being THROW"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn debugger_statement_lowers_to_no_runtime_instruction() {
        let module = lower_js("debugger;");
        assert_eq!(module.functions()[0].code(), &[Instruction::Halt]);
    }
    #[test]
    fn invalid_labeled_jumps_fail_at_the_control_target_boundary() {
        for (source, operation) in [
            ("block: { break; }", "break target is not live"),
            (
                "block: { continue block; }",
                "continue target is not an iteration statement",
            ),
        ] {
            let error = lower_js_result(source).expect_err("invalid jump must not lower");
            assert_eq!(
                error.kind,
                LowerErrorKind::InvalidControlFlow { operation },
                "{source}"
            );
        }
    }
    #[test]
    fn lowering_preserves_lone_surrogate_escapes() {
        let module = lower_js("const lone = '\\uD800'; const face = '\\u{1F603}';");
        let strings: Vec<_> = module
            .constants()
            .iter()
            .filter_map(|constant| match constant {
                Constant::String(value) => Some(value.as_units()),
                _ => None,
            })
            .collect();
        assert!(strings.iter().any(|units| *units == [0xD800]));
        assert!(strings.iter().any(|units| *units == [0xD83D, 0xDE03]));
    }
    #[test]
    fn non_decimal_bigint_literals_lower_to_decimal_constants() {
        let module = lower_js(
            "const hex = 0x100000000000000000000000000000001n; \
             const octal = 0o20n; \
             const binary = 0b1_0000n;",
        );
        let bigints: Vec<_> = module
            .constants()
            .iter()
            .filter_map(|constant| match constant {
                Constant::BigInt(value) => Some(value.as_str()),
                _ => None,
            })
            .collect();
        assert!(bigints.contains(&"340282366920938463463374607431768211457"));
        assert!(bigints.contains(&"16"));
    }
    #[test]
    fn malformed_non_decimal_bigint_separator_fails_lowering() {
        let source = Arc::new(
            SourceText::new("const value = 0x1_n;".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
        let parsed = parse(scanned);
        let error = lower(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
        )
        .expect_err("a trailing BigInt separator is invalid");
        assert_eq!(error.kind, LowerErrorKind::InvalidBigIntLiteral);
    }
    #[test]
    fn non_decimal_bigint_conversion_honors_output_limit() {
        assert_eq!(
            canonical_bigint_text("0xffn", 3, usize::MAX).as_deref(),
            Ok("255")
        );
        assert_eq!(
            canonical_bigint_text("0xffn", 2, usize::MAX),
            Err(BigIntTextError::Bytes)
        );
    }
    #[test]
    fn non_decimal_bigint_conversion_honors_work_limit() {
        assert_eq!(
            canonical_bigint_text("0xffffn", 5, 4).as_deref(),
            Ok("65535")
        );
        assert_eq!(
            canonical_bigint_text("0xffffn", 5, 3),
            Err(BigIntTextError::Work)
        );
    }
    #[test]
    fn non_decimal_bigint_conversion_matches_small_integer_values() {
        for value in 0_u32..4096 {
            let expected = value.to_string();
            for lexeme in [
                format!("0x{value:x}n"),
                format!("0o{value:o}n"),
                format!("0b{value:b}n"),
            ] {
                assert_eq!(
                    canonical_bigint_text(&lexeme, 16, usize::MAX).as_deref(),
                    Ok(expected.as_str()),
                    "{lexeme}"
                );
            }
        }
    }
    fn any_instruction(
        module: &Module<Verified>,
        predicate: impl Fn(&Instruction) -> bool,
    ) -> bool {
        module
            .functions()
            .iter()
            .flat_map(|function| function.code())
            .any(predicate)
    }
    #[test]
    fn checked_lowering_inlines_a_local_const_enum_member() {
        let source = Arc::new(
            SourceText::new("const enum K { X = 2, Y = X + 3 } K.Y;".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("checked const enum lowers");
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::LoadGlobal { .. } | Instruction::GetProperty { .. }
        )));
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::Number(value) if value.to_f64() == 5.0
        )));
    }
    #[test]
    fn checked_lowering_inlines_const_enum_members_in_every_expression_context() {
        for (context, expression) in [
            ("bare member", "K.Y;"),
            ("binary operand", "K.Y + 1;"),
            ("call argument", "((value: number) => value)(K.Y);"),
            ("parenthesized member", "((K.Y));"),
        ] {
            let source = Arc::new(
                SourceText::new(format!("const enum K {{ X = 2, Y = X + 3 }} {expression}"))
                    .expect("test source fits the per-file budget"),
            );
            let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
            let checked = check(&parsed);
            let module = lower_checked(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                    ..LowerOptions::default()
                },
                checked.product().enum_facts(),
                checked.product().namespace_facts(),
            )
            .expect("checked const enum lowers in every expression context");
            assert!(
                !any_instruction(&module, |instruction| matches!(
                    instruction,
                    Instruction::LoadGlobal { .. } | Instruction::GetProperty { .. }
                )),
                "{context} must not access `K` at runtime"
            );
            assert!(module.constants().iter().any(|constant| matches!(
                constant,
                Constant::Number(value) if value.to_f64() == 5.0
            )));
        }
        let source = Arc::new(
            SourceText::new("enum E { Literal = `literal`, Interpolated = `${1}` }".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("checked runtime enum lowers");
        let mappings = module
            .functions()
            .iter()
            .flat_map(|function| function.code())
            .filter(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            .count();
        assert_eq!(
            mappings, 2,
            "each string template member emits only a forward mapping"
        );
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::String(value) if value.as_units() == [108, 105, 116, 101, 114, 97, 108]
        )));
    }
    #[test]
    fn checked_lowering_inlines_const_enum_reads_but_rejects_member_callees() {
        let source = Arc::new(
            SourceText::new("const enum K { X = 2 } K.X; (K.X as number);".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("const enum reads lower");
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::LoadGlobal { .. } | Instruction::GetProperty { .. }
        )));
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::Number(value) if value.to_f64() == 2.0
        )));
        for (context, expression, operation) in [
            ("ordinary call", "K.X();", ConstEnumOperation::Read),
            ("parenthesized call", "(K.X)();", ConstEnumOperation::Read),
            (
                "asserted call",
                "(K.X as number)();",
                ConstEnumOperation::Read,
            ),
            (
                "optional call",
                "K.X?.();",
                ConstEnumOperation::OptionalAccess,
            ),
            (
                "parenthesized optional call",
                "(K.X as number)?.();",
                ConstEnumOperation::OptionalAccess,
            ),
            ("ordinary construct", "new K.X();", ConstEnumOperation::Read),
            (
                "parenthesized construct",
                "new (K.X)();",
                ConstEnumOperation::Read,
            ),
            (
                "asserted construct",
                "new (K.X as number)();",
                ConstEnumOperation::Read,
            ),
        ] {
            let source = Arc::new(
                SourceText::new(format!("const enum K {{ X = 2 }} {expression}"))
                    .expect("test source fits the per-file budget"),
            );
            let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
            let checked = check(&parsed);
            let error = lower_checked(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                    ..LowerOptions::default()
                },
                checked.product().enum_facts(),
                checked.product().namespace_facts(),
            )
            .expect_err("const enum member cannot be called or constructed");
            assert_eq!(
                error.kind,
                LowerErrorKind::ConstEnumOperation { operation },
                "{context}: {expression}"
            );
        }
    }
    #[test]
    fn checked_lowering_rejects_const_enum_member_write_and_delete() {
        for (source, operation) in [
            ("const enum K { X = 2 } K.X = 3;", ConstEnumOperation::Write),
            (
                "const enum K { X = 2 } delete K.X;",
                ConstEnumOperation::Delete,
            ),
            (
                "const enum K { X = 2 } K?.X;",
                ConstEnumOperation::OptionalAccess,
            ),
        ] {
            let source_text = Arc::new(
                SourceText::new(source.to_owned()).expect("test source fits the per-file budget"),
            );
            let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source_text));
            let checked = check(&parsed);
            let error = lower_checked(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                    ..LowerOptions::default()
                },
                checked.product().enum_facts(),
                checked.product().namespace_facts(),
            )
            .expect_err("const enum member mutation is rejected");
            assert_eq!(
                error.kind,
                LowerErrorKind::ConstEnumOperation { operation },
                "{source}"
            );
        }
    }
    fn lower_local_const_enum_mutation(source: &str) -> LowerError {
        let source = Arc::new(
            SourceText::new(source.to_owned()).expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect_err("const enum member mutation must fail during lowering")
    }
    fn lower_imported_const_enum_mutation(importer: &str, import_statement: usize) -> LowerError {
        let enum_file = parse(scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new("export const enum K { X = 2 }".to_owned())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let importer_file = parse(scan(
            SourceId::new(1),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(importer.to_owned()).expect("test source fits the per-file budget"),
            ),
        ));
        let files = [enum_file, importer_file];
        let import = files[1].product().statements()[import_statement].data();
        let crate::syntax::Statement::Import(import) = import else {
            panic!("declared import statement is an import");
        };
        let Some(crate::syntax::ImportBinding::Named(specifiers)) = import
            .clause
            .as_ref()
            .and_then(|clause| clause.binding.as_ref())
        else {
            panic!("const enum import is named");
        };
        let specifier = specifiers[0].id();
        let edges = [ResolvedModuleEdge {
            from: SourceId::new(1),
            specifier: files[1].product().statements()[import_statement].id(),
            to: SourceId::new(0),
        }];
        let checked = check_program(
            ProgramCheckInput {
                files: &files,
                edges: &edges,
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
        );
        let facts = checked
            .product()
            .file(SourceId::new(1))
            .expect("program model contains importer");
        assert!(
            facts.enum_facts().is_elided_import_specifier(specifier),
            "invalid imported const-enum writes must not retain a runtime import"
        );
        lower_checked(
            files[1].product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            facts.enum_facts(),
            facts.namespace_facts(),
        )
        .expect_err("imported const enum member mutation must fail during lowering")
    }
    #[test]
    fn checked_lowering_rejects_local_const_enum_mutation_matrix() {
        for (operation, mutation, expected) in [
            ("assignment", "K.X = 3;", ConstEnumOperation::Write),
            (
                "compound assignment",
                "K.X += 3;",
                ConstEnumOperation::Write,
            ),
            ("prefix update", "++K.X;", ConstEnumOperation::Write),
            ("postfix update", "K.X++;", ConstEnumOperation::Write),
            (
                "nested assignment target",
                "({ value: K.X } = { value: 3 });",
                ConstEnumOperation::Write,
            ),
            ("delete", "delete K.X;", ConstEnumOperation::Delete),
        ] {
            for (site, source) in [
                ("top level", format!("const enum K {{ X = 2 }} {mutation}")),
                (
                    "nested function",
                    format!("const enum K {{ X = 2 }} function mutate() {{ {mutation} }}"),
                ),
                (
                    "pre-declaration",
                    format!("{mutation} const enum K {{ X = 2 }}"),
                ),
            ] {
                let error = lower_local_const_enum_mutation(&source);
                assert_eq!(
                    error.kind,
                    LowerErrorKind::ConstEnumOperation {
                        operation: expected
                    },
                    "{operation} at {site}: {source}"
                );
            }
        }
    }
    #[test]
    fn checked_lowering_rejects_imported_const_enum_mutation_matrix() {
        for (operation, mutation, expected) in [
            ("assignment", "K.X = 3;", ConstEnumOperation::Write),
            (
                "compound assignment",
                "K.X += 3;",
                ConstEnumOperation::Write,
            ),
            ("prefix update", "++K.X;", ConstEnumOperation::Write),
            ("postfix update", "K.X++;", ConstEnumOperation::Write),
            (
                "nested assignment target",
                "({ value: K.X } = { value: 3 });",
                ConstEnumOperation::Write,
            ),
            ("delete", "delete K.X;", ConstEnumOperation::Delete),
        ] {
            let import = "import { K } from './enum';";
            for (site, importer, import_statement) in [
                ("top level", format!("{import} {mutation}"), 0),
                (
                    "nested function",
                    format!("{import} function mutate() {{ {mutation} }}"),
                    0,
                ),
                ("pre-declaration", format!("{mutation} {import}"), 1),
            ] {
                let error = lower_imported_const_enum_mutation(&importer, import_statement);
                assert_eq!(
                    error.kind,
                    LowerErrorKind::ConstEnumOperation {
                        operation: expected
                    },
                    "{operation} at {site}: {importer}"
                );
            }
        }
    }
    #[test]
    fn checked_lowering_materializes_empty_exported_namespace_object() {
        let source = Arc::new(
            SourceText::new("export namespace N {}".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("empty exported namespace lowers");
        let code = module.functions()[module.entry().get() as usize].code();
        let create_object = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateObject { .. }))
            .expect("empty exported namespace materializes a runtime object");
        let export = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Export { .. }))
            .expect("empty exported namespace publishes a value export");
        assert!(
            create_object < export,
            "runtime container must exist before the value export is published"
        );
        let has_call = code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Call { .. }));
        assert!(!has_call, "empty namespace does not evaluate an IIFE body");
        assert_round_trips(&module);
    }
    #[test]
    fn checked_lowering_retains_elided_const_enum_import_side_effect_without_binding() {
        let enum_source = "export let evaluated = 0; evaluated += 1; export const enum K { X = 1 }";
        let importer_source =
            "import { K, evaluated } from './enum_dep.ts'; const observed = K.X + evaluated;";
        let enum_file = parse(scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(enum_source.to_owned())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let importer_file = parse(scan(
            SourceId::new(1),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(importer_source.to_owned())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let files = [enum_file, importer_file];
        let import = files[1].product().statements()[0].data();
        let crate::syntax::Statement::Import(import) = import else {
            panic!("first importer statement is an import");
        };
        let Some(crate::syntax::ImportBinding::Named(specifiers)) = import
            .clause
            .as_ref()
            .and_then(|clause| clause.binding.as_ref())
        else {
            panic!("importer uses named bindings");
        };
        let elided = specifiers[0].id();
        let retained = specifiers[1].id();
        let edges = [ResolvedModuleEdge {
            from: SourceId::new(1),
            specifier: files[1].product().statements()[0].id(),
            to: SourceId::new(0),
        }];
        let checked = check_program(
            ProgramCheckInput {
                files: &files,
                edges: &edges,
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
        );
        let facts = checked
            .product()
            .file(SourceId::new(1))
            .expect("program model contains importer");
        assert!(
            facts.enum_facts().is_elided_import_specifier(elided),
            "const-enum named binding is elided"
        );
        let retained_elided = facts.enum_facts().is_elided_import_specifier(retained);
        assert!(!retained_elided, "ordinary named binding is retained");
        let module = lower_checked(
            files[1].product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            facts.enum_facts(),
            facts.namespace_facts(),
        )
        .expect("elided const-enum import lowers");
        let code = module.functions()[module.entry().get() as usize].code();
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::Import { .. })),
            "direct checked-module lowering keeps Import for module evaluation"
        );
        let constants = module.constants();
        let reads_named = |export_name: &str| {
            code.iter().enumerate().any(|(index, instruction)| {
                let Instruction::GetProperty { key, .. } = instruction else {
                    return false;
                };
                code[..index].iter().rev().any(|prior| match prior {
                    Instruction::LoadConst { dst, constant } if dst == key => matches!(
                        &constants[constant.get() as usize],
                        Constant::String(value) if value.eq_ascii(export_name)
                    ),
                    _ => false,
                })
            })
        };
        let reads_k = reads_named("K");
        assert!(
            !reads_k,
            "elided const-enum specifier must not read a runtime export binding"
        );
        assert!(
            reads_named("evaluated"),
            "ordinary import bindings are still materialized"
        );
        let stores_global = |binding: &str| {
            code.iter().any(|instruction| match instruction {
                Instruction::StoreGlobal { name, .. } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value) if value.eq_ascii(binding)
                ),
                _ => false,
            })
        };
        let stores_k = stores_global("K");
        assert!(
            !stores_k,
            "elided const-enum specifier leaves no runtime local binding"
        );
        assert!(
            stores_global("evaluated"),
            "ordinary import bindings still install a runtime local"
        );
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::Number(value) if value.to_f64() == 1.0
        )));
        assert_round_trips(&module);
    }
    fn max_capture_count(module: &Module<Verified>) -> u32 {
        module
            .functions()
            .iter()
            .map(|function| function.capture_count())
            .max()
            .unwrap_or(0)
    }
    fn created_cell_used_as_capture(code: &[Instruction]) -> Option<Register> {
        code.iter().find_map(|instruction| {
            let Instruction::ArrayPush { array, value } = instruction else {
                return None;
            };
            if array == value {
                return None;
            }
            code.iter()
                .any(|candidate| {
                    matches!(
                        candidate,
                        Instruction::CreateArray { dst } | Instruction::CreateCell { dst }
                            if dst == value
                    )
                })
                .then_some(*value)
        })
    }
    fn cell_capture_pushes(code: &[Instruction], cell: Register) -> usize {
        code.iter()
            .filter(|instruction| {
                matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell)
            })
            .count()
    }
    fn cell_allocations(code: &[Instruction], cell: Register) -> usize {
        code.iter()
            .filter(|instruction| {
                matches!(
                    instruction,
                    Instruction::CreateArray { dst } | Instruction::CreateCell { dst }
                        if *dst == cell
                )
            })
            .count()
    }
    fn dormant_promotion_cell_blocks(code: &[Instruction]) -> usize {
        code.iter()
            .enumerate()
            .filter(|(entry, instruction)| {
                let Instruction::CreateArray { dst } = instruction else {
                    return false;
                };
                matches!(
                    code.get((*entry).saturating_sub(1)),
                    Some(Instruction::Jump { target }) if target.get() as usize == *entry + 2
                ) && matches!(
                    code.get(*entry + 1),
                    Some(Instruction::ArrayPush { array, value }) if array == dst && value == dst
                ) && !code.iter().any(|instruction| {
                    matches!(
                        instruction,
                        Instruction::Jump { target }
                            | Instruction::JumpIfTrue { target, .. }
                            | Instruction::JumpIfFalse { target, .. }
                            if target.get() as usize == *entry
                    )
                })
            })
            .count()
    }
    #[test]
    fn capture_keys_dedupe_live_containers_and_with_regions() {
        let name = String::from("value");
        let name_key = CaptureKey::Name(name.clone(), Vec::new());
        assert_eq!(name_key, CaptureKey::Name(name, Vec::new()));
        assert_eq!(
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Namespace,
                Register::new(3)
            ),
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Namespace,
                Register::new(3)
            )
        );
        assert_ne!(
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Enum,
                Register::new(3)
            ),
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Namespace,
                Register::new(3)
            )
        );
        assert_ne!(
            CaptureKey::WithObject((1, 4), Register::new(5)),
            CaptureKey::WithObject((2, 6), Register::new(5))
        );
        let nested_function_captures = [
            CaptureKey::Name(String::from("value"), Vec::new()),
            CaptureKey::Container(
                crate::checker::SymbolId::new(1),
                ContainerKind::Namespace,
                Register::new(2),
            ),
            CaptureKey::WithObject((10, 20), Register::new(3)),
            CaptureKey::WithObject((11, 19), Register::new(4)),
        ];
        assert!(matches!(
            nested_function_captures.last(),
            Some(CaptureKey::WithObject((11, 19), object)) if *object == Register::new(4)
        ));
        let mut live_regions = nested_function_captures
            .iter()
            .filter_map(|capture| match capture {
                CaptureKey::WithObject(site, object) => Some((*site, *object)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            live_regions,
            [((10, 20), Register::new(3)), ((11, 19), Register::new(4))]
        );
        live_regions.pop();
        assert_eq!(live_regions, [((10, 20), Register::new(3))]);
        live_regions.clear();
        assert!(live_regions.is_empty());
    }
    #[test]
    fn outer_write_is_observed_by_a_captured_read() {
        let module = lower_js(
            "function outer() { let value = 0; const read = () => value; value = 1; return read; }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| {
                created_cell_used_as_capture(code).is_some()
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .expect("outer function owns the promoted binding");
        let cell = created_cell_used_as_capture(code).expect("cell is captured");
        assert!(code.iter().any(
            |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell)
        ));
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
                )
        }));
    }
    #[test]
    fn inner_write_is_observed_by_the_outer_read() {
        let module = lower_js(
            "function outer() { let value = 0; const write = () => { value = 1; }; write(); return value; }",
        );
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == Register::new(0))
                )
        }));
        assert!(module.functions().iter().any(|function| {
            let code = function.code();
            created_cell_used_as_capture(code).is_some_and(|cell| {
                code.iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == cell)
                )
            })
        }));
    }
    #[test]
    fn assigned_local_cell_dominates_a_later_conditional_closure() {
        let module = lower_js(
            "function outer(flag) { let value = 0; value = 1; let read; if (flag) read = () => value; return value; }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("outer function owns the captured cell");
        let cell = created_cell_used_as_capture(code).expect("cell is captured");
        let allocation = code
            .iter()
            .position(
                |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
            )
            .expect("cell allocation is present");
        let conditional = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::JumpIfFalse { .. }))
            .expect("if statement branches");
        assert!(allocation < conditional);
        assert!(code[..conditional].iter().any(
            |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell)
        ));
    }
    #[test]
    fn assigned_parameter_uses_one_cell_before_later_method_capture() {
        let module = lower_js(
            "function mitt(all) { all = all || new Map(); return { read() { return all; } }; }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("mitt function owns the parameter cell");
        let cell = created_cell_used_as_capture(code).expect("parameter cell is captured");
        let allocation = code
            .iter()
            .position(
                |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
            )
            .expect("parameter cell is allocated");
        let assignment = code
            .iter()
            .position(
                |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell),
            )
            .expect("parameter assignment stores through its cell");
        let closure = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            .expect("method closure is created");
        assert!(allocation < assignment && assignment < closure);
        assert_eq!(cell_allocations(code, cell), 1);
    }
    #[test]
    fn captured_parameter_cells_precede_default_initializer_closures() {
        for source in [
            "function f(a = () => a) { return a; }",
            "function f(make = () => later, later = 1) { return make; }",
            "function f(make = () => rest, ...rest) { return make; }",
            "function f({ value = () => value } = {}) { return value; }",
        ] {
            let module = lower_js(source);
            let owner = module
                .functions()
                .iter()
                .find(|function| created_cell_used_as_capture(function.code()).is_some())
                .expect("parameter owner materializes a captured default closure");
            let code = owner.code();
            let cell = created_cell_used_as_capture(code).expect("parameter cell is captured");
            let allocation = code
                .iter()
                .position(
                    |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
                )
                .expect("parameter cell is allocated");
            let closure = code
                .iter()
                .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                .expect("default initializer creates a closure");
            assert!(allocation < closure, "{source}");
            assert_eq!(cell_allocations(code, cell), 1, "{source}");
        }
    }
    #[test]
    fn declaration_owned_closures_capture_their_predeclared_cells() {
        for source in [
            "function outer() { const f = () => f; return f; }",
            "function outer() { function f() { return f; } return f; }",
            "function outer() { class C { self() { return C; } } return C; }",
            "function outer() { const { f = () => f } = {}; return f; }",
            "function outer() { const f = () => f; { const f = 1; } return f; }",
        ] {
            let module = lower_js(source);
            let owner = module
                .functions()
                .iter()
                .find(|function| created_cell_used_as_capture(function.code()).is_some())
                .expect("declaration owner materializes the captured cell");
            let code = owner.code();
            let cell = created_cell_used_as_capture(code).expect("cell is captured");
            let allocation = code
                .iter()
                .position(
                    |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
                )
                .expect("captured cell is allocated");
            let closure = code
                .iter()
                .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                .expect("declaration value creates a closure");
            assert!(allocation < closure, "{source}");
            assert_eq!(cell_allocations(code, cell), 1, "{source}");
            assert!(
                code[closure..].iter().any(
                    |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell)
                ),
                "the declaration stores its final value into the same cell: {source}"
            );
        }
    }
    #[test]
    fn safe_uncaptured_lexical_stays_in_a_register() {
        let module = lower_js("function outer() { const value = 1; return value; }");
        assert!(module.functions().iter().all(|function| {
            !function
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
        }));
    }
    #[test]
    fn captured_later_lexical_is_predeclared_once() {
        let module = lower_js(
            "function outer() { const read = () => later; const later = 1; return read; }",
        );
        let owner = module
            .functions()
            .iter()
            .find(|function| {
                function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
            })
            .expect("owner predeclares the later lexical cell");
        assert_eq!(
            owner
                .code()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
                .count(),
            1
        );
        let cell = created_cell_used_as_capture(owner.code()).expect("closure captures the cell");
        assert_eq!(cell_allocations(owner.code(), cell), 1);
    }
    #[test]
    fn early_closure_read_uses_one_predeclared_cell_then_initializes_it() {
        let module = lower_js(
            "function outer() { const read = () => later; read(); let later = 1; return read(); }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("outer owns the captured later binding");
        let cell = created_cell_used_as_capture(code).expect("later binding is a cell");
        let create = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateCell { dst } if *dst == cell))
            .expect("cell is seeded at scope entry");
        let closure = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            .expect("reader closure is instantiated");
        let initialize = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell))
            .expect("declaration initializes the cell");
        assert!(create < closure && closure < initialize);
        assert_eq!(cell_allocations(code, cell), 1);
    }
    #[test]
    fn function_declaration_is_instantiated_once_before_executable_statements() {
        let module = lower_js(
            "function outer() { return declaredLater(); function declaredLater() { return 2; } }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| {
                code.iter()
                    .any(|instruction| matches!(instruction, Instruction::Call { .. }))
            })
            .expect("outer function calls its declaration");
        let closure = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            .expect("function declaration is instantiated");
        let call = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .expect("call is emitted");
        assert!(closure < call);
        assert_eq!(
            code.iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                .count(),
            1
        );
    }
    #[test]
    fn class_heritage_reads_its_own_uninitialized_cell() {
        let module = lower_js("function outer() { class C extends C {} return C; }");
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| {
                code.iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
            })
            .expect("class owner predeclares its binding");
        let cell = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::CreateCell { dst } => Some(*dst),
                _ => None,
            })
            .expect("class cell exists");
        let create = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateCell { dst } if *dst == cell))
            .expect("class cell allocation");
        let heritage_read = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == cell))
            .expect("heritage reads through the class cell");
        let initialize = code
            .iter()
            .rposition(|instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell))
            .expect("class declaration initializes the same cell");
        assert!(create < heritage_read && heritage_read < initialize);
    }
    #[test]
    fn same_name_shadow_does_not_overbox_uncaptured_binding() {
        let module =
            lower_js("function outer() { let value = 1; { let value = 2; } return () => value; }");
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("outer binding is captured");
        assert_eq!(
            code.iter()
                .filter(|instruction| matches!(
                    instruction,
                    Instruction::CreateArray { .. } | Instruction::CreateCell { .. }
                ))
                .count(),
            2,
            "only the captured binding cell and closure capture array allocate"
        );
        assert_eq!(dormant_promotion_cell_blocks(code), 0);
    }
    #[test]
    fn sibling_getter_and_setter_capture_the_same_cell() {
        let module = lower_js(
            "function outer() { let value = 0; const get = () => value; const set = (next) => { value = next; }; return [get, set]; }",
        );
        assert!(module.functions().iter().any(|function| {
            let code = function.code();
            created_cell_used_as_capture(code)
                .is_some_and(|cell| cell_capture_pushes(code, cell) == 2)
        }));
    }
    #[test]
    fn transitive_capture_passes_an_existing_cell_without_wrapping_it() {
        let module = lower_js("function outer() { let value = 1; return () => () => value; }");
        let middle = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            })
            .expect("middle closure materializes the inner closure");
        assert_eq!(
            middle
                .code()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateArray { .. }))
                .count(),
            1,
            "only the capture array is allocated; capture register zero is already a cell"
        );
        assert!(middle.code().iter().any(
            |instruction| matches!(instruction, Instruction::ArrayPush { value, .. } if *value == Register::new(0))
        ));
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && !function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
                )
        }));
    }
    #[test]
    fn capture_of_capture_reads_and_reexports_the_same_cell() {
        let module = lower_js(
            "function outer() { let value = 1; return () => { value; return () => value; }; }",
        );
        let middle = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            })
            .expect("middle closure reads and reexports the capture");
        assert!(middle.code().iter().any(
            |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
        ));
        assert_eq!(
            middle
                .code()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateArray { .. }))
                .count(),
            1
        );
    }
    #[test]
    fn logical_assignment_reads_and_writes_cell_contents() {
        let module = lower_js(
            "function outer() { let optional = false; return (term) => { optional ||= term; }; }",
        );
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
                )
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == Register::new(0))
                )
        }));
    }
    #[test]
    fn classic_for_let_rebinds_but_for_var_reuses_its_cell() {
        let lexical = lower_js(
            "function outer() { const reads = []; for (let index = 0; index < 2; index++) reads.push(() => index); return reads; }",
        );
        let shared = lower_js(
            "function outer() { const reads = []; for (var index = 0; index < 2; index++) reads.push(() => index); return reads; }",
        );
        let lexical_allocations = lexical
            .functions()
            .iter()
            .find_map(|function| {
                let code = function.code();
                let cell = created_cell_used_as_capture(code)?;
                Some(cell_allocations(code, cell))
            })
            .expect("lexical loop captures its binding cell");
        let shared_allocations = shared
            .functions()
            .iter()
            .find_map(|function| {
                let code = function.code();
                let cell = created_cell_used_as_capture(code)?;
                Some(cell_allocations(code, cell))
            })
            .expect("var loop captures its binding cell");
        assert_eq!(lexical_allocations, 2, "let copies into a fresh cell");
        assert_eq!(shared_allocations, 1, "var retains one function cell");
        for module in [&lexical, &shared] {
            let code = module
                .functions()
                .iter()
                .map(|function| function.code())
                .find(|code| created_cell_used_as_capture(code).is_some())
                .expect("captured loop owns a cell");
            assert_eq!(
                dormant_promotion_cell_blocks(code),
                0,
                "captured loops contain no late-promotion scaffold"
            );
        }
    }
    #[test]
    fn uncaptured_ordinary_and_loop_locals_emit_no_cell_scaffolds() {
        let ordinary = lower_js("function outer(value) { let copy = value; return copy; }");
        let classic =
            lower_js("function outer(limit) { for (let index = 0; index < limit; index++) {} }");
        let iterator = lower_js("function outer(values) { for (let value of values) {} }");
        for (label, module) in [
            ("ordinary", &ordinary),
            ("classic", &classic),
            ("iterator", &iterator),
        ] {
            let entry = module.entry().get() as usize;
            let code = module
                .functions()
                .iter()
                .enumerate()
                .find(|(index, _)| *index != entry)
                .map(|(_, function)| function.code())
                .expect("snippet has one declared function");
            assert_eq!(dormant_promotion_cell_blocks(code), 0);
            assert!(
                !code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateArray { .. })),
                "{label} local storage allocates no cell"
            );
            assert!(
                !code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. })),
                "{label} local storage initializes no cell"
            );
        }
    }
    #[test]
    fn iterator_let_allocates_inside_the_loop_but_var_allocates_before_it() {
        fn allocation_and_step(module: &Module<Verified>) -> (usize, usize) {
            module
                .functions()
                .iter()
                .find_map(|function| {
                    let code = function.code();
                    let cell = created_cell_used_as_capture(code)?;
                    let allocation = code.iter().position(
                        |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
                    )?;
                    let step = code
                        .iter()
                        .position(|instruction| matches!(instruction, Instruction::IteratorNext { .. }))?;
                    Some((allocation, step))
                })
                .expect("iterator loop captures its declaration")
        }
        let lexical = lower_js(
            "function outer(values) { const reads = []; for (let value of values) reads.push(() => value); return reads; }",
        );
        let shared = lower_js(
            "function outer(values) { const reads = []; for (var value of values) reads.push(() => value); return reads; }",
        );
        let (lexical_allocation, lexical_step) = allocation_and_step(&lexical);
        let (shared_allocation, shared_step) = allocation_and_step(&shared);
        assert!(
            lexical_step < lexical_allocation,
            "let creates a new cell after each iterator step"
        );
        assert!(
            shared_allocation < shared_step,
            "var creates one cell before iterator stepping begins"
        );
    }
    #[test]
    fn computed_member_access_uses_a_register_key() {
        let module = lower_js("const o: any = {}; const k = \"a\"; const v = o[k];");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetProperty { .. }
        )));
    }
    #[test]
    fn spread_call_builds_an_arguments_array_with_extend() {
        let module = lower_js("declare const f: any; const xs = [1]; f(...xs);");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::ArrayExtend { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Call { .. }
        )));
    }
    #[test]
    fn nonempty_array_pushes_elements() {
        let module = lower_js("const a = [1, 2, 3];");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::ArrayPush { .. }
        )));
    }
    #[test]
    fn closure_capturing_a_local_emits_a_nonempty_capture() {
        let module = lower_js("function outer() { const x = 1; return () => x; }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreateClosure { .. }
        )));
        assert!(max_capture_count(&module) >= 1, "the arrow captures `x`");
    }
    #[test]
    fn ordinary_function_declarations_materialize_own_prototypes() {
        let module = lower_js("function Base() {}");
        let code = module.functions()[0].code();
        let constants = module.constants();
        let key_name = |register: Register| -> String {
            let id = code
                .iter()
                .find_map(|instruction| match instruction {
                    Instruction::LoadConst { dst, constant } if *dst == register => Some(constant),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no LoadConst defines key register {register:?}"));
            match &constants[id.get() as usize] {
                Constant::String(value) => value
                    .to_utf8_strict()
                    .expect("compiler-interned property key is well-formed UTF-16"),
                other => panic!("expected a string constant for the key, got {other:?}"),
            }
        };
        let (closure_index, closure) = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::CreateClosure { dst, .. } => Some((index, *dst)),
                _ => None,
            })
            .expect("function declaration materializes a closure");
        let (prototype_index, prototype) = code[closure_index + 1..]
            .iter()
            .enumerate()
            .find_map(|(offset, instruction)| match instruction {
                Instruction::CreateObject { dst } => Some((closure_index + 1 + offset, *dst)),
                _ => None,
            })
            .expect("ordinary function gets an own prototype object");
        let constructor_key = code[prototype_index + 1..]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::SetProperty { object, key, value }
                    if *object == prototype && *value == closure =>
                {
                    Some(*key)
                }
                _ => None,
            })
            .expect("prototype.constructor is assigned the closure");
        assert_eq!(
            key_name(constructor_key),
            "constructor",
            "the reverse link is stored under the key \"constructor\""
        );
        let prototype_key = code[closure_index + 1..]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::SetProperty { object, key, value }
                    if *object == closure && *value == prototype =>
                {
                    Some(*key)
                }
                _ => None,
            })
            .expect("closure.prototype is assigned the prototype");
        assert_eq!(
            key_name(prototype_key),
            "prototype",
            "the forward link is stored under the key \"prototype\""
        );
    }
    #[test]
    fn lowering_marks_only_ecmascript_constructors_constructable() {
        let ordinary = lower_js("function Base() {}");
        assert_eq!(
            ordinary
                .functions()
                .iter()
                .filter(|function| function.flags().is_constructable)
                .count(),
            1,
            "the declaration is constructable and the module entry is not"
        );

        let mixed = lower_js("const arrow = () => 1; const object = { method() {} }; class C {}");
        assert_eq!(
            mixed
                .functions()
                .iter()
                .filter(|function| function.flags().is_constructable)
                .count(),
            1,
            "only the class constructor is constructable"
        );
    }
    #[test]
    fn template_literal_lowers_to_string_concatenation() {
        let module = lower_js("const a = 1; const s = `x${a}y`;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Binary {
                op: bamts_bytecode::BinaryOp::Add,
                ..
            }
        )));
    }
    #[test]
    fn for_of_lowers_to_the_iterator_protocol() {
        let module = lower_js("for (const v of [1, 2]) { globalThis; }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetIterator { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::IteratorNext { .. }
        )));
    }
    #[test]
    fn for_of_emits_an_iterator_close_cleanup() {
        let module = lower_js("for (const v of [1, 2]) { break; }");
        let code = module.functions()[0].code();
        assert!(any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::IteratorClose {
                mode: IteratorCloseMode::PreserveAbrupt,
                ..
            }
        )));
        let preserve_called = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::IteratorClose {
                    called,
                    mode: IteratorCloseMode::PreserveAbrupt,
                    ..
                } => Some(called),
                _ => None,
            })
            .expect("preserve close exists");
        assert!(
            !code.iter().any(|instruction| matches!(
                instruction,
                Instruction::RequireCloseResult { called, .. }
                    if called == preserve_called
            )),
            "preserve close never validates the return result"
        );
        assert!(
            code.windows(2).any(|window| {
                matches!(
                    (&window[0], &window[1]),
                    (
                        Instruction::IteratorClose {
                            result,
                            called,
                            mode: IteratorCloseMode::Propagate,
                            ..
                        },
                        Instruction::RequireCloseResult {
                            result: checked,
                            called: checked_called,
                        }
                    ) if result == checked && called == checked_called
                )
            }),
            "sync propagate close validates its raw result immediately"
        );
        assert!(!code.windows(2).any(|window| {
            matches!(
                (&window[0], &window[1]),
                (
                    Instruction::IteratorClose {
                        mode: IteratorCloseMode::PreserveAbrupt,
                        ..
                    },
                    Instruction::RequireCloseResult { .. }
                )
            )
        }));
        assert_round_trips(&module);
    }
    #[test]
    fn for_in_does_not_close_its_key_iterator() {
        let module = lower_js("for (const k in obj) { break; }");
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::IteratorClose { .. }
        )));
        assert_round_trips(&module);
    }
    #[test]
    fn for_await_awaits_the_close_result() {
        let module = lower_js("async function f() { for await (const x of xs) { break; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| {
                function.code().iter().any(|instruction| {
                    matches!(
                        instruction,
                        Instruction::IteratorClose {
                            mode: IteratorCloseMode::PreserveAbrupt,
                            ..
                        }
                    )
                })
            })
            .expect("async loop function has iterator cleanup");
        let code = function.code();
        let (preserve_called, preserve_await_pc) = code
            .windows(3)
            .enumerate()
            .find_map(|(pc, window)| match (&window[0], &window[1], &window[2]) {
                (
                    Instruction::IteratorClose {
                        result,
                        called,
                        mode: IteratorCloseMode::PreserveAbrupt,
                        ..
                    },
                    Instruction::Await { src, .. },
                    after,
                ) if result == src && !matches!(after, Instruction::RequireCloseResult { .. }) => {
                    Some((called, Pc::new(pc as u32 + 1)))
                }
                _ => None,
            })
            .expect("preserve close awaits without validating");
        assert!(
            !code.iter().any(|instruction| matches!(
                instruction,
                Instruction::RequireCloseResult { called, .. }
                    if called == preserve_called
            )),
            "preserve called flag is never consumed by close-result validation"
        );
        let propagate_close = code.windows(3).any(|window| {
            matches!(
                (&window[0], &window[1], &window[2]),
                (
                    Instruction::IteratorClose {
                        result,
                        called,
                        mode: IteratorCloseMode::Propagate,
                        ..
                    },
                    Instruction::Await { dst, src, .. },
                    Instruction::RequireCloseResult {
                        result: checked,
                        called: checked_called,
                    }
                ) if result == src && dst == checked && called == checked_called
            )
        });
        assert!(
            propagate_close,
            "async propagate validates the settled close result"
        );
        assert!(
            function.handlers().iter().any(|handler| {
                handler.start == preserve_await_pc
                    && handler.end.get() == preserve_await_pc.get() + 1
            }),
            "preserve rejection handler covers exactly one Await"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn for_of_cleanup_round_trips() {
        let module = lower_js(
            "function f(xs: any, ys: any) { outer: for (const x of xs) { for (const y of ys) { if (y) continue outer; if (x) break outer; return y; } } }",
        );
        assert_round_trips(&module);
    }
    #[test]
    fn object_destructuring_reads_named_properties() {
        let module = lower_js("declare const obj: any; const { a, b } = obj;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetProperty { .. }
        )));
    }
    #[test]
    fn regex_literal_lowers_to_create_regexp() {
        let module = lower_js("const r = /ab+c/gi;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreateRegExp { .. }
        )));
    }
    #[test]
    fn array_assignment_patterns_take_defaults_and_rest() {
        let module = lower_js("var a, b, c, d = {}; [a = 1, [b = 2], ...d.rest] = c;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetIterator { .. }
        )));
    }

    #[test]
    fn class_methods_are_defined_as_hidden_and_object_methods_are_not() {
        let class = lower_js("class C { m() {} get v() { return 1; } set v(x) {} }");
        assert!(any_instruction(&class, |i| matches!(
            i,
            Instruction::DefineDataProperty { .. }
        )));
        for expected in [
            bamts_bytecode::AccessorKind::ClassGetter,
            bamts_bytecode::AccessorKind::ClassSetter,
        ] {
            assert!(any_instruction(&class, |i| matches!(
                i,
                Instruction::DefineAccessor { kind, .. } if *kind == expected
            )));
        }
        let object = lower_js("var o = { m() {}, get v() { return 1; } };");
        assert!(!any_instruction(&object, |i| matches!(
            i,
            Instruction::DefineDataProperty { .. }
        )));
        assert!(any_instruction(&object, |i| matches!(
            i,
            Instruction::DefineAccessor { kind, .. } if *kind == bamts_bytecode::AccessorKind::Getter
        )));
    }

    #[test]
    fn class_with_extends_builds_prototype_chain() {
        let module = lower_js("class B {} class C extends B { m() { return 1; } }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::SetPrototype { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreateClosure { .. }
        )));
    }
    fn instruction_indices(
        code: &[Instruction],
        predicate: impl Fn(&Instruction) -> bool,
    ) -> Vec<usize> {
        code.iter()
            .enumerate()
            .filter_map(|(index, instruction)| predicate(instruction).then_some(index))
            .collect()
    }
    fn super_construct_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::ConstructWithNewTarget { .. })
        })
    }
    fn first_super_construct_index(code: &[Instruction]) -> Option<usize> {
        super_construct_indices(code).first().copied()
    }
    fn first_create_cell_index(code: &[Instruction]) -> Option<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::CreateCell { .. })
        })
        .first()
        .copied()
    }
    fn calls_before_index(code: &[Instruction], bound: usize) -> Vec<usize> {
        plain_call_indices(code)
            .into_iter()
            .filter(|index| *index < bound)
            .collect()
    }
    fn first_call_after_index(code: &[Instruction], bound: usize) -> Option<usize> {
        plain_call_indices(code)
            .into_iter()
            .find(|index| *index > bound)
    }
    fn instance_field_init_after_super(
        code: &[Instruction],
        super_construct: usize,
        this_cell: Register,
    ) -> usize {
        instruction_indices(code, |instruction| {
            matches!(
                instruction,
                Instruction::SetProperty { object, .. } if *object != this_cell
            )
        })
        .into_iter()
        .find(|index| *index > super_construct)
        .unwrap_or_else(|| panic!("derived field is initialized after super"))
    }
    fn plain_call_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::Call { .. })
        })
    }
    fn expect_one_index(label: &str, indices: Vec<usize>) -> usize {
        match indices.as_slice() {
            [index] => *index,
            [] => panic!("{label}: expected one match, found none"),
            _ => panic!("{label}: expected one match, found {indices:?}"),
        }
    }
    fn derived_constructor_function<'a>(
        module: &'a Module<Verified>,
        selector: impl Fn(&[Instruction]) -> bool,
        label: &'static str,
    ) -> &'a Function {
        module
            .functions()
            .iter()
            .find(|function| selector(function.code()))
            .unwrap_or_else(|| panic!("{label}"))
    }
    fn derived_constructor_with_super_count<'a>(
        module: &'a Module<Verified>,
        super_calls: usize,
        label: &'static str,
    ) -> &'a Function {
        derived_constructor_function(
            module,
            |code| {
                first_create_cell_index(code).is_some()
                    && super_construct_indices(code).len() == super_calls
                    && !code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            },
            label,
        )
    }
    fn this_cell_register(code: &[Instruction]) -> Register {
        code.iter()
            .find_map(|instruction| match instruction {
                Instruction::CreateCell { dst } => Some(*dst),
                _ => None,
            })
            .expect("derived constructor creates its this cell")
    }
    fn assert_super_construct_operands(function: &Function, index: usize) {
        let code = function.code();
        let Instruction::ConstructWithNewTarget {
            callee,
            new_target,
            arguments,
            ..
        } = &code[index]
        else {
            panic!("instruction at {index} is not ConstructWithNewTarget");
        };
        assert!(
            callee.get() < function.capture_count(),
            "super construct callee is the parent-constructor capture"
        );
        assert!(
            code[..index].iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::LoadNewTarget { dst } if *dst == *new_target
                )
            }),
            "super construct uses an explicit new.target operand"
        );
        assert!(
            code[..index].iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::CreateArray { dst } if *dst == *arguments
                )
            }) || code[..index].iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::ArrayExtend { array, .. } if *array == *arguments
                )
            }),
            "super construct receives a prepared arguments array operand"
        );
    }
    #[test]
    fn derived_constructor_places_fields_between_super_and_trailing_body() {
        let module = lower_js(
            "class Base {} class Derived extends Base { field = 1; constructor() { before(); super(); after(); } }",
        );
        let constructor = derived_constructor_function(
            &module,
            |code| super_construct_indices(code).len() == 1,
            "derived constructor constructs its parent with an explicit new.target",
        );
        let code = constructor.code();
        let super_construct = expect_one_index(
            "derived constructor constructs its parent with an explicit new.target",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_construct);
        let this_cell = this_cell_register(code);
        let before_call = expect_one_index(
            "before() remains a plain call",
            calls_before_index(code, super_construct),
        );
        let field = instance_field_init_after_super(code, super_construct, this_cell);
        let after_call = first_call_after_index(code, field)
            .expect("after() remains a plain call after field initialization");
        assert!(before_call < super_construct && super_construct < field && field < after_call);
    }
    #[test]
    fn implicit_derived_constructor_forwards_arguments_before_fields() {
        let module = lower_js("class Base {} class Derived extends Base { field = 1; }");
        let constructor = derived_constructor_function(
            &module,
            |code| {
                super_construct_indices(code).len() == 1
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::ArrayExtend { .. }))
            },
            "implicit derived constructor extends its arguments array",
        );
        let code = constructor.code();
        let super_construct = expect_one_index(
            "implicit derived constructor constructs its parent",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_construct);
        let this_cell = this_cell_register(code);
        let field = instance_field_init_after_super(code, super_construct, this_cell);
        assert!(super_construct < field);
    }
    #[test]
    fn derived_constructor_this_cell_matrix_lowers_without_shape_gating() {
        struct Case {
            source: &'static str,
            calls: usize,
            read_before_call: bool,
            read_after_call: bool,
        }
        for case in [
            Case {
                source: "class Base {} class Derived extends Base { constructor() { this.x; super(); } }",
                calls: 1,
                read_before_call: true,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor() { this.x = 1; super(); } }",
                calls: 1,
                read_before_call: true,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor(flag) { if (flag) super(); } }",
                calls: 1,
                read_before_call: false,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor() {} }",
                calls: 0,
                read_before_call: false,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor() { super(); this.x = 1; } }",
                calls: 1,
                read_before_call: false,
                read_after_call: true,
            },
        ] {
            let module = lower_js(case.source);
            let constructor = derived_constructor_with_super_count(
                &module,
                case.calls,
                "derived constructor matches its ConstructWithNewTarget count",
            );
            let code = constructor.code();
            let create_cell =
                first_create_cell_index(code).expect("derived constructor creates its this cell");
            let cell = this_cell_register(code);
            let super_calls = super_construct_indices(code);
            assert_eq!(super_calls.len(), case.calls, "{}", case.source);
            if case.calls == 1 {
                let super_construct = expect_one_index(
                    "derived constructor constructs its parent with ConstructWithNewTarget",
                    super_calls,
                );
                assert_super_construct_operands(constructor, super_construct);
            } else {
                assert!(
                    first_super_construct_index(code).is_none(),
                    "{}",
                    case.source
                );
            }
            let cell_reads_after_allocation: Vec<_> = instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { object, .. } if *object == cell)
            })
            .into_iter()
            .filter(|read| create_cell < *read)
            .collect();
            let this_reads_before_first_super = first_super_construct_index(code)
                .is_some_and(|call| cell_reads_after_allocation.iter().any(|read| *read < call));
            assert_eq!(
                this_reads_before_first_super, case.read_before_call,
                "{}",
                case.source
            );
            let last_super_anchor = first_super_construct_index(code)
                .or(super_construct_indices(code).last().copied())
                .unwrap_or(create_cell);
            assert_eq!(
                cell_reads_after_allocation
                    .iter()
                    .any(|read| *read > last_super_anchor),
                case.read_after_call,
                "{}",
                case.source
            );
        }
        let module = lower_js(
            "class Base {} class Derived extends Base { constructor(value, get = () => this) { super(); get().value = value; } }",
        );
        let constructor = derived_constructor_function(
            &module,
            |code| super_construct_indices(code).len() == 1,
            "default-parameter constructor constructs its parent with ConstructWithNewTarget",
        );
        let code = constructor.code();
        let cell = this_cell_register(code);
        assert_eq!(
            cell.get(),
            constructor.capture_count() + constructor.parameter_count(),
            "the this cell follows the initialized capture and parameter prefix"
        );
        let super_construct = expect_one_index(
            "default-parameter constructor constructs its parent",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_construct);
        let cell_creation = first_create_cell_index(code).expect("this cell creation is present");
        let cell_capture = expect_one_index(
            "default initializer arrow captures the this cell",
            instruction_indices(
                code,
                |instruction| matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell),
            ),
        );
        let closure_creation = expect_one_index(
            "default initializer creates its arrow",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::CreateClosure { .. })
            }),
        );
        assert!(cell_creation < cell_capture);
        assert!(cell_capture < closure_creation);
        assert!(closure_creation < super_construct);
    }
    #[test]
    fn derived_constructor_super_store_and_guard_are_adjacent() {
        let module =
            lower_js("class Base {} class Derived extends Base { constructor() { super(); } }");
        let constructor = derived_constructor_with_super_count(
            &module,
            1,
            "derived constructor constructs its parent with ConstructWithNewTarget",
        );
        let code = constructor.code();
        let constants = module.constants();
        let super_pc = expect_one_index(
            "derived constructor constructs its parent with ConstructWithNewTarget",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_pc);
        let Instruction::ConstructWithNewTarget {
            dst: construct_dst, ..
        } = &code[super_pc]
        else {
            panic!("instruction at {super_pc} is not ConstructWithNewTarget");
        };
        let construct_dst = *construct_dst;
        let cell_store_pc = expect_one_index(
            "super result is stored into the this cell",
            instruction_indices(code, |instruction| {
                matches!(
                    instruction,
                    Instruction::SetProperty { value, .. } if *value == construct_dst
                )
            })
            .into_iter()
            .filter(|index| *index > super_pc)
            .collect(),
        );
        let Instruction::SetProperty {
            object: this_cell, ..
        } = &code[cell_store_pc]
        else {
            panic!("instruction at {cell_store_pc} is not SetProperty");
        };
        let this_cell = *this_cell;
        let true_load_pc = expect_one_index(
            "derived super guard loads the boolean true constant",
            instruction_indices(code, |instruction| {
                matches!(
                    instruction,
                    Instruction::LoadConst { constant, .. }
                        if matches!(constants[constant.get() as usize], Constant::Boolean(true))
                )
            })
            .into_iter()
            .filter(|index| *index > cell_store_pc)
            .collect(),
        );
        let Instruction::LoadConst { dst: true_src, .. } = &code[true_load_pc] else {
            panic!("instruction at {true_load_pc} is not LoadConst");
        };
        let true_src = *true_src;
        let guard_move_pc = expect_one_index(
            "derived super guard moves the true constant into the guard register",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::Move { src, .. } if *src == true_src)
            })
            .into_iter()
            .filter(|index| *index > true_load_pc)
            .collect(),
        );
        assert!(
            super_pc < cell_store_pc
                && cell_store_pc < true_load_pc
                && true_load_pc < guard_move_pc,
            "super construct, this-cell store, true load, and guard move must be ordered"
        );
        for (offset, instruction) in code[super_pc + 1..guard_move_pc].iter().enumerate() {
            let pc = super_pc + 1 + offset;
            let violation = matches!(
                instruction,
                Instruction::Call { .. }
                    | Instruction::Construct { .. }
                    | Instruction::ConstructWithNewTarget { .. }
                    | Instruction::GetProperty { .. }
            ) || matches!(
                instruction,
                Instruction::SetProperty { object, .. } if *object != this_cell
            );
            assert!(
                !violation,
                "instruction at {pc} between super construct and guard move is not an allowed compiler-only op: {instruction:?}"
            );
        }
    }
    #[test]
    fn private_field_creates_a_private_name() {
        let module = lower_js("class C { #x = 1; read() { return this.#x; } }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreatePrivateName { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::LoadThis { .. }
        )));
    }
    #[test]
    fn generator_sets_the_flag_and_suspends() {
        let module = lower_js("function* g() { yield 1; yield 2; }");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function.flags().is_generator)
        );
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Suspend { .. }
        )));
        assert!(
            !any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "yield never emits the await opcode"
        );
    }
    #[test]
    fn generator_suspend_emits_inline_throw_and_return_dispatch() {
        let module = lower_js("function* g() { yield 1; }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("generator suspends");
        let Instruction::Suspend {
            dst, resume, mode, ..
        } = code[suspend_pc]
        else {
            unreachable!()
        };
        assert_ne!(
            dst, mode,
            "resume value and completion mode use distinct registers"
        );
        let resume_pc = resume.get() as usize;
        assert_eq!(
            resume_pc,
            suspend_pc + 1,
            "resume enters the inline dispatch"
        );

        let Instruction::LoadConst {
            dst: throw_marker,
            constant: throw_constant,
        } = code[resume_pc]
        else {
            panic!("throw mode marker is loaded first")
        };
        assert_eq!(
            module.constants()[throw_constant.get() as usize],
            Constant::Int32(RESUME_THROW)
        );
        let Instruction::Binary {
            dst: throw_matches,
            op: BinaryOp::StrictEqual,
            left: throw_left,
            right: throw_right,
        } = code[resume_pc + 1]
        else {
            panic!("throw mode is tested inline")
        };
        assert_eq!((throw_left, throw_right), (mode, throw_marker));
        let Instruction::JumpIfFalse {
            condition: throw_condition,
            target: after_throw,
        } = code[resume_pc + 2]
        else {
            panic!("throw guard skips the abrupt arm")
        };
        assert_eq!(throw_condition, throw_matches);
        assert_eq!(after_throw.get() as usize, resume_pc + 4);
        assert_eq!(code[resume_pc + 3], Instruction::Throw { value: dst });

        let Instruction::LoadConst {
            dst: return_marker,
            constant: return_constant,
        } = code[resume_pc + 4]
        else {
            panic!("return mode marker follows throw dispatch")
        };
        assert_eq!(
            module.constants()[return_constant.get() as usize],
            Constant::Int32(RESUME_RETURN)
        );
        let Instruction::Binary {
            dst: return_matches,
            op: BinaryOp::StrictEqual,
            left: return_left,
            right: return_right,
        } = code[resume_pc + 5]
        else {
            panic!("return mode is tested inline")
        };
        assert_eq!((return_left, return_right), (mode, return_marker));
        let Instruction::JumpIfFalse {
            condition: return_condition,
            target: after_return,
        } = code[resume_pc + 6]
        else {
            panic!("return guard skips the abrupt arm")
        };
        assert_eq!(return_condition, return_matches);
        assert_eq!(after_return.get() as usize, resume_pc + 8);
        assert_eq!(code[resume_pc + 7], Instruction::Return { value: dst });
        assert_round_trips(&module);
    }

    #[test]
    fn generator_throw_resume_dispatch_stays_inside_try_handler() {
        let module = lower_js("function* g() { try { yield 1; } catch (e) { yield e; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("try body suspends");
        let Instruction::Suspend { dst, resume, .. } = code[suspend_pc] else {
            unreachable!()
        };
        let throw_pc = code
            .iter()
            .enumerate()
            .skip(resume.get() as usize)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Throw { value } if *value == dst => Some(pc),
                _ => None,
            })
            .expect("resume throw arm");
        let handler = function
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= suspend_pc
                    && handler.end.get() as usize > suspend_pc
            })
            .expect("try handler covers the suspension");
        assert!(
            handler.start.get() as usize <= resume.get() as usize
                && handler.end.get() as usize > throw_pc,
            "resume entry and Throw remain inside the protected range"
        );
    }

    #[test]
    fn generator_return_bypasses_catch_and_routes_to_finally() {
        let module = lower_js(
            "function* g() { try { yield 1; } catch (e) { sink(e); } finally { sink(2); } }",
        );
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("try body suspends");
        let Instruction::Suspend { resume, .. } = code[suspend_pc] else {
            unreachable!()
        };
        let handler = function
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= suspend_pc
                    && handler.end.get() as usize > suspend_pc
            })
            .expect("try handler");
        let return_route = code[resume.get() as usize + 7..handler.end.get() as usize]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::Jump { target } => Some(*target),
                _ => None,
            })
            .expect("return routes out of the protected body");
        assert_ne!(
            return_route, handler.handler,
            "return completion must not enter the catch clause"
        );
        assert!(
            return_route.get() >= handler.end.get(),
            "return completion targets the finalizer after the protected range"
        );
    }

    #[test]
    fn nested_generator_return_routes_through_each_finally() {
        let module = lower_js(
            "function* g() { try { try { yield 1; } finally { sink(1); } } finally { sink(2); } }",
        );
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("nested try body suspends");
        let Instruction::Suspend { dst, resume, .. } = code[suspend_pc] else {
            unreachable!()
        };
        let mut enclosing: Vec<_> = function
            .handlers()
            .iter()
            .filter(|handler| {
                handler.start.get() as usize <= suspend_pc
                    && handler.end.get() as usize > suspend_pc
            })
            .collect();
        enclosing.sort_by_key(|handler| handler.end.get() - handler.start.get());
        let [inner, outer] = enclosing.as_slice() else {
            panic!("the suspension is protected by two nested handlers")
        };
        let return_body = resume.get() as usize + 7;
        assert!(
            code[return_body..inner.end.get() as usize].iter().any(
                |instruction| matches!(instruction, Instruction::Move { src, .. } if *src == dst)
            ),
            "return value is recorded in the innermost finally frame"
        );
        let inner_route = code[return_body..inner.end.get() as usize]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::Jump { target } => Some(*target),
                _ => None,
            })
            .expect("return routes to inner finalizer");
        assert!(
            inner_route.get() >= inner.end.get() && inner_route.get() < outer.end.get(),
            "inner finalizer runs while still inside the outer protected range"
        );
        assert!(
            code[inner_route.get() as usize..outer.end.get() as usize]
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Jump { target } if target.get() >= outer.end.get())),
            "inner finalizer dispatch preserves return and routes to the outer finalizer"
        );
    }

    #[test]
    fn async_await_uses_the_await_opcode() {
        let module = lower_js("async function f(p: any) { return await p; }");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function.flags().is_async)
        );
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Await { .. }
        )));
        assert!(
            !any_instruction(&module, |i| matches!(i, Instruction::Suspend { .. })),
            "await never emits the yield opcode"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn async_generator_distinguishes_await_from_yield() {
        let module = lower_js("async function* g(p: any) { const v = await p; yield v; }");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function.flags().is_async && function.flags().is_generator)
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "the await operand suspends with Await"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Suspend { .. })),
            "the produced item yields with Suspend"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn for_await_splits_step_await_result() {
        let module = lower_js("async function f(xs: any) { for await (const v of xs) { v; } }");
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::IteratorStep { .. })),
            "the async iterator is stepped for its raw result"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "the raw iterator result is awaited"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::IteratorResult { .. })),
            "the settled iterator result yields done/value"
        );
        assert!(
            !any_instruction(&module, |i| matches!(i, Instruction::IteratorNext { .. })),
            "async loops never use the fused sync step"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn async_generator_yield_star_delegates_through_the_async_protocol() {
        let module = lower_js("async function* g(xs: any) { yield* xs; }");
        assert!(
            any_instruction(&module, |i| matches!(
                i,
                Instruction::GetIterator {
                    kind: IteratorKind::Async,
                    ..
                }
            )),
            "the delegated iterator is acquired through Symbol.asyncIterator"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::IteratorStep { .. })),
            "each delegated step is acquired as a raw result"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "raw delegated results are awaited before unpacking"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Suspend { .. })),
            "delegated values yield through the generator suspension"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Call { .. })),
            "abrupt completions forward through delegated iterator methods"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn sync_generator_inside_async_function_keeps_sync_yield_star() {
        let module = lower_js(
            "async function f() { const g = function* (xs: any) { yield* xs; }; return g; }",
        );
        let generator = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("nested generator lowers");
        assert!(
            generator.code().iter().any(|instruction| matches!(
                instruction,
                Instruction::GetIterator {
                    kind: IteratorKind::Sync,
                    ..
                }
            )),
            "a sync generator's yield* stays on Symbol.iterator"
        );
        assert!(
            !generator.code().iter().any(|instruction| matches!(
                instruction,
                Instruction::GetIterator {
                    kind: IteratorKind::Async,
                    ..
                }
            )),
            "the enclosing async function must not leak into the nested generator"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn yield_star_allows_a_newline_before_the_delegated_operand() {
        let module = lower_js("async function* g(f: any) { yield*\n f(); }");
        assert!(
            any_instruction(&module, |i| matches!(
                i,
                Instruction::GetIterator {
                    kind: IteratorKind::Async,
                    ..
                }
            )),
            "the newline form still lowers as async delegation"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn free_names_load_from_the_environment() {
        let module = lower_js("const keys = Object.keys({});");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::LoadGlobal { .. }
        )));
    }
    #[test]
    fn try_finally_routes_completions_through_the_finalizer() {
        let module = lower_js(
            "function f(x: any) { while (x) { try { return 1; } finally { x = 0; } } return 2; }",
        );
        // A handler is registered and the finalizer runs before the return.
        assert!(
            module
                .functions()
                .iter()
                .any(|function| !function.handlers().is_empty())
        );
        assert_round_trips(&module);
    }
    #[test]
    fn optional_member_call_skips_arguments_and_preserves_receiver() {
        let key_is_method = |code: &[Instruction], constants: &[Constant], register: Register| {
            let constant = code
                .iter()
                .find_map(|instruction| match instruction {
                    Instruction::LoadConst { dst, constant } if *dst == register => Some(constant),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no LoadConst defines property key {register:?}"));
            match &constants[constant.get() as usize] {
                Constant::String(value) => {
                    value.to_utf8_strict().is_ok_and(|value| value == "method")
                }
                _ => false,
            }
        };
        let assert_optional_call = |src: &str, expect_method_jump: bool| {
            let module = lower_js(src);
            let code = module.functions()[0].code();
            let constants = module.constants();
            let (member_index, callee, object) = code
                .iter()
                .enumerate()
                .find_map(|(index, instruction)| match instruction {
                    Instruction::GetProperty { dst, object, key }
                        if key_is_method(code, constants, *key) =>
                    {
                        Some((index, *dst, *object))
                    }
                    _ => None,
                })
                .expect("optional member call loads its method");
            let (call_index, call_dst, this_value) = code
                .iter()
                .enumerate()
                .find_map(|(index, instruction)| match instruction {
                    Instruction::Call {
                        dst,
                        callee: call_callee,
                        this_value,
                        ..
                    } if *call_callee == callee => Some((index, *dst, *this_value)),
                    _ => None,
                })
                .expect("optional member call invokes the loaded method");
            assert_eq!(
                this_value, object,
                "the call keeps the member object as this"
            );
            let result_move_index = code[call_index + 1..]
                .iter()
                .enumerate()
                .find_map(|(offset, instruction)| match instruction {
                    Instruction::Move { src, .. } if *src == call_dst => {
                        Some(call_index + 1 + offset)
                    }
                    _ => None,
                })
                .expect("the call result is moved into a shared result register");
            let merge = result_move_index + 1;
            let (object_jump_index, object_jump_target) = code[..member_index]
                .iter()
                .enumerate()
                .rev()
                .find_map(|(index, instruction)| match instruction {
                    Instruction::JumpIfTrue { condition, target }
                        if code[..index].iter().any(|prior| {
                            matches!(
                                prior,
                                Instruction::Binary { dst, op: BinaryOp::Equal, left, .. }
                                    if *dst == *condition && *left == object
                            )
                        }) =>
                    {
                        Some((index, *target))
                    }
                    _ => None,
                })
                .expect("optional object test branches before the member read");
            assert!(
                code[object_jump_index + 1..call_index]
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::Call { .. })),
                "the argument side effect is emitted before the member call"
            );
            assert_eq!(
                object_jump_target.get() as usize,
                merge,
                "the object-nullish branch jumps to the instruction after the result assignment"
            );
            if expect_method_jump {
                let method_jump_target = code[member_index + 1..call_index]
                    .iter()
                    .enumerate()
                    .rev()
                    .find_map(|(offset, instruction)| {
                        let index = member_index + 1 + offset;
                        match instruction {
                            Instruction::JumpIfTrue { condition, target }
                                if code[member_index + 1..index].iter().any(|prior| {
                                    matches!(
                                        prior,
                                        Instruction::Binary { dst, op: BinaryOp::Equal, left, .. }
                                            if *dst == *condition && *left == callee
                                    )
                                }) =>
                            {
                                Some(target)
                            }
                            _ => None,
                        }
                    })
                    .expect("optional method test branches before the call");
                assert_eq!(
                    method_jump_target.get() as usize,
                    merge,
                    "the method-nullish branch jumps to the same merge point"
                );
            }
        };
        assert_optional_call(
            "declare const obj: any; declare function side_effect(): number; obj?.method(side_effect());",
            false,
        );
        assert_optional_call(
            "declare const obj: any; declare function side_effect(): number; obj?.method?.(side_effect());",
            true,
        );
    }
    #[test]
    fn arrow_rest_loads_the_activations_own_arguments() {
        // `(...options) => options` must collect the arrow invocation's own
        let module = lower_js("const collect = (...options) => options; collect(1, 2);");
        let entry = module.entry().get() as usize;
        let arrow = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, _)| *index != entry)
            .map(|(_, function)| function)
            .expect("the arrow is the sole non-entry function");
        let code = arrow.code();
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::LoadArguments { .. })),
            "the arrow body loads its own activation arguments for rest"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::GetIterator { .. })),
            "rest collection iterates the loaded arguments"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. })),
            "rest collection pushes into the rest array"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn regular_function_rest_with_fixed_parameters_loads_arguments() {
        let module = lower_js("function f(a, ...rest) { return rest; }");
        let entry = module.entry().get() as usize;
        let function = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, _)| *index != entry)
            .map(|(_, function)| function)
            .expect("the regular function is the sole non-entry function");
        let code = function.code();
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::LoadArguments { .. })),
            "the function loads its own arguments for rest"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::GetIterator { .. })),
            "rest collection iterates the loaded arguments"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::IteratorNext { .. })),
            "the fixed parameter is discarded by stepping the iterator"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn arrow_lexical_arguments_is_captured_not_loaded() {
        let module = lower_js("function outer() { const read = () => arguments; return read(); }");
        let arrow = module
            .functions()
            .iter()
            .find(|function| function.capture_count() >= 1)
            .expect("the arrow captures `arguments` from outer");
        assert!(
            !arrow
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadArguments { .. })),
            "the arrow reads `arguments` from its capture, not its own activation"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn dynamic_import_lowers_a_computed_specifier_once_before_options() {
        let module = lower_js("import('./left' + pick(), effects());");
        let code = module.functions()[0].code();
        let binary_positions: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                matches!(
                    instruction,
                    Instruction::Binary {
                        op: BinaryOp::Add,
                        ..
                    }
                )
                .then_some(index)
            })
            .collect();
        assert_eq!(
            binary_positions.len(),
            1,
            "the computed specifier expression is lowered once"
        );
        let call_positions: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. }).then_some(index)
            })
            .collect();
        assert_eq!(call_positions.len(), 2);
        let import_dynamic = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
            .expect("import(expr) emits ImportDynamic");
        assert!(binary_positions[0] > call_positions[0]);
        assert!(binary_positions[0] < call_positions[1]);
        assert!(call_positions[1] < import_dynamic);
        assert_round_trips(&module);
    }
    #[test]
    fn dynamic_import_lowers_a_literal_specifier_through_import_dynamic() {
        let module = lower_js("import('./dep.js');");
        assert!(any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::ImportDynamic { .. }
        )));
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::Import { .. }
        )));
        assert_round_trips(&module);
    }
    fn assert_round_trips(module: &Module<Verified>) {
        let bytes = module.encode();
        decode_verified(&bytes, &DecodeLimits::default())
            .expect("a verified module re-decodes and re-verifies");
    }
    #[test]
    fn synthetic_functions_allocate_captures_before_parameters() {
        use super::{Binding, DeclarationScope, FunctionContext, ModuleBuilder};
        use crate::enum_plan::EnumFacts;
        use crate::namespace_plan::NamespaceFacts;
        let source =
            Arc::new(SourceText::new("".to_owned()).expect("test source fits the per-file budget"));
        let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
        let parsed = parse(scanned);
        let file = parsed.product();
        let enum_facts = EnumFacts::unchecked();
        let namespace_facts = NamespaceFacts::unchecked();
        let mut builder = ModuleBuilder {
            source: file.source_id(),
            constants: Vec::new(),
            functions: Vec::new(),
        };
        let mut context = FunctionContext::new_top_level(
            file,
            None,
            super::LoweringGoal::Module,
            &enum_facts,
            &namespace_facts,
            namespace_facts.symbols(),
        );
        let range = file.range();
        // Enclosing state the synthetic closure captures by value: one named
        // cell and the class-definition element table.
        let seed = context.alloc_register(range).expect("register");
        context.declare(
            "seed".to_owned(),
            Binding::Cell(seed),
            DeclarationScope::Function,
        );
        let table = context.alloc_register(range).expect("register");
        context
            .emit(range, Instruction::CreateArray { dst: table })
            .expect("emit");
        let captures = [
            CaptureKey::Name("seed".to_owned(), Vec::new()),
            CaptureKey::ClassElements(table),
        ];
        let closure = context
            .build_synthetic_function(
                &mut builder,
                range,
                None,
                &captures,
                2,
                |inner, _, parameters| {
                    assert_eq!(parameters, &[Register::new(2), Register::new(3)]);
                    assert_eq!(inner.class_elements, Some(Register::new(1)));
                    let sum = inner.alloc_register(range)?;
                    inner.emit(
                        range,
                        Instruction::Binary {
                            dst: sum,
                            op: BinaryOp::Add,
                            left: parameters[0],
                            right: parameters[1],
                        },
                    )?;
                    Ok(sum)
                },
            )
            .expect("synthetic function lowers");
        let functions: Vec<_> = builder
            .functions
            .iter()
            .map(|slot| slot.as_ref().expect("filled"))
            .collect();
        assert_eq!(functions.len(), 1);
        let generated = functions[0];
        assert_eq!(generated.capture_count(), 2);
        assert_eq!(generated.parameter_count(), 2);
        assert_eq!(
            generated.code().last(),
            Some(&Instruction::Return {
                value: Register::new(4)
            }),
            "every synthetic function has exactly one trailing return"
        );
        let enclosing = context.code;
        let tail = &enclosing[enclosing.len() - 4..];
        assert!(
            matches!(tail[0], Instruction::CreateArray { .. })
                && matches!(
                    tail[1],
                    Instruction::ArrayPush { value, .. } if value == seed
                )
                && matches!(
                    tail[2],
                    Instruction::ArrayPush { value, .. } if value == table
                )
                && matches!(
                    tail[3],
                    Instruction::CreateClosure { dst, .. } if dst == closure
                ),
            "captures materialize by value in capture order: {tail:?}"
        );
    }

    // ------------------------------------------------------------------
    // Sloppy `with` lowering contracts
    // ------------------------------------------------------------------
    fn entry_code(module: &Module<Verified>) -> &[Instruction] {
        module.functions()[module.entry().get() as usize].code()
    }
    fn with_has_binding_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::WithHasBinding { .. })
        })
    }
    fn to_object_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::ToObject { .. })
        })
    }
    #[test]
    fn with_statement_lowers_object_once_through_to_object() {
        let module = lower_js("with (o) { x; }");
        let code = entry_code(&module);
        let to_objects = to_object_indices(code);
        assert_eq!(
            to_objects.len(),
            1,
            "exactly one ToObject for the with object"
        );
        let membership = with_has_binding_indices(code);
        assert!(!membership.is_empty(), "free name consults with membership");
        assert!(
            to_objects[0] < membership[0],
            "ToObject precedes membership tests"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn with_identifier_read_tests_membership_before_global_fallback() {
        let module = lower_js("with (o) { x; }");
        let code = entry_code(&module);
        let membership = expect_one_index("WithHasBinding", with_has_binding_indices(code));
        let get = expect_one_index(
            "GetProperty",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            }),
        );
        let loads = instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::LoadGlobal { .. })
        });
        let fallback = loads
            .iter()
            .copied()
            .find(|&index| index > get)
            .expect("unmatched path falls back to LoadGlobal after GetProperty");
        assert!(
            membership < get && get < fallback,
            "membership before GetProperty before fallback LoadGlobal: {membership} < {get} < {fallback}"
        );
    }
    #[test]
    fn with_body_lexical_declaration_shadows_the_with_object() {
        // Top-level `let` lowers through StoreGlobal without a local scope binding,
        // so exercise the lexical shadow inside a function body.
        let module = lower_js("function f(o) { with (o) { let x = 1; x; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| {
                function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::ToObject { .. }))
            })
            .expect("function containing with");
        assert!(
            with_has_binding_indices(function.code()).is_empty(),
            "body let beats with: no WithHasBinding for x"
        );
        assert_eq!(to_object_indices(function.code()).len(), 1);
    }
    #[test]
    fn with_shadows_an_outer_var() {
        let module = lower_js("function f(o) { var x = 1; with (o) { x; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| {
                function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::WithHasBinding { .. }))
            })
            .expect("function body emits WithHasBinding for outer var");
        assert_eq!(
            with_has_binding_indices(function.code()).len(),
            1,
            "outer var is shadowed by with"
        );
    }
    #[test]
    fn nested_with_regions_test_innermost_object_first() {
        let module = lower_js("with (a) { with (b) { x; } }");
        let code = entry_code(&module);
        let to_objects: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::ToObject { dst, .. } => Some((index, *dst)),
                _ => None,
            })
            .collect();
        assert_eq!(to_objects.len(), 2, "outer and inner ToObject");
        let inner_to_object_at = to_objects[1].0;
        let outer_object = to_objects[0].1;
        let inner_object = to_objects[1].1;
        // Object expr of the inner with may consult the outer region; the body
        // read of `x` starts after the inner ToObject and walks innermost-first.
        let membership: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::WithHasBinding { object, .. } if index > inner_to_object_at => {
                    Some(*object)
                }
                _ => None,
            })
            .collect();
        assert_eq!(membership.len(), 2, "body read probes both regions");
        assert_eq!(
            membership[0], inner_object,
            "innermost WithHasBinding comes first"
        );
        assert_eq!(membership[1], outer_object, "outer WithHasBinding follows");
    }
    #[test]
    fn with_simple_assignment_resolves_put_value_after_rhs() {
        // Literal RHS: no pre-RHS target freeze; membership is only for PutValue.
        let module = lower_js("with (o) { x = 2; }");
        let code = entry_code(&module);
        let to_object = expect_one_index("ToObject", to_object_indices(code));
        let membership = with_has_binding_indices(code);
        assert_eq!(membership.len(), 1, "PutValue alone probes membership");
        assert!(
            to_object < membership[0],
            "object coercion precedes PutValue"
        );
        let write = instruction_indices(code, |instruction| {
            matches!(
                instruction,
                Instruction::SetProperty { .. } | Instruction::StoreGlobal { .. }
            )
        })
        .into_iter()
        .find(|&index| index > membership[0])
        .expect("write follows PutValue membership");
        assert!(membership[0] < write);
    }
    #[test]
    fn with_compound_assignment_reresolves_put_value_after_rhs() {
        // GetValue before RHS, PutValue after — two membership walks around the
        // arithmetic (literal RHS avoids extra free-name probes).
        let module = lower_js("with (o) { x += 1; }");
        let code = entry_code(&module);
        let membership = with_has_binding_indices(code);
        assert_eq!(
            membership.len(),
            2,
            "compound assignment re-resolves PutValue after GetValue"
        );
        let binary = expect_one_index(
            "Binary",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::Binary { .. })
            }),
        );
        assert!(
            membership[0] < binary && binary < membership[1],
            "read membership < compute < write membership"
        );
    }
    #[test]
    fn with_update_reresolves_put_value_after_getvalue() {
        let module = lower_js("with (o) { x++; }");
        let code = entry_code(&module);
        let membership = with_has_binding_indices(code);
        assert_eq!(
            membership.len(),
            2,
            "update GetValue and PutValue each probe membership"
        );
        assert_eq!(
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            })
            .len(),
            1
        );
        assert_eq!(
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::SetProperty { .. })
            })
            .len(),
            1
        );
        assert!(membership[0] < membership[1]);
    }
    #[test]
    fn with_assignment_put_value_matches_node_after_rhs_delete() {
        // Instruction-order stand-in for Node's
        // `var outer=0; const o={x:1}; with(o){x=(delete o.x,2)}`
        // → globalThis.x=2. RHS delete completes before PutValue membership.
        let module = lower_js("with (o) { x = (delete o.x, 2); }");
        let code = entry_code(&module);
        let delete_at = expect_one_index(
            "DeleteProperty",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::DeleteProperty { .. })
            }),
        );
        let put_membership = with_has_binding_indices(code)
            .into_iter()
            .find(|&index| index > delete_at)
            .expect("PutValue WithHasBinding follows the RHS delete");
        let write_after = instruction_indices(code, |instruction| {
            matches!(
                instruction,
                Instruction::SetProperty { .. } | Instruction::StoreGlobal { .. }
            )
        })
        .into_iter()
        .any(|index| index > put_membership);
        assert!(
            write_after,
            "PutValue emits a write after the re-resolved membership test"
        );
    }
    #[test]
    fn with_typeof_falls_back_to_type_of_global() {
        let module = lower_js("with (o) { typeof x; }");
        let code = entry_code(&module);
        assert_eq!(with_has_binding_indices(code).len(), 1);
        assert!(any_instruction(&module, |instruction| {
            matches!(instruction, Instruction::TypeOfGlobal { .. })
        }));
        assert!(any_instruction(&module, |instruction| {
            matches!(
                instruction,
                Instruction::Unary {
                    op: UnaryOp::TypeOf,
                    ..
                }
            )
        }));
        assert!(
            !instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            })
            .is_empty()
        );
    }
    #[test]
    fn with_delete_targets_the_with_object() {
        let module = lower_js("with (o) { delete x; }");
        let code = entry_code(&module);
        assert_eq!(with_has_binding_indices(code).len(), 1);
        assert_eq!(
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::DeleteProperty { .. })
            })
            .len(),
            1
        );
    }
    #[test]
    fn with_method_call_receives_the_with_object_as_this() {
        let module = lower_js("with (o) { m(); }");
        let code = entry_code(&module);
        let get = expect_one_index(
            "GetProperty",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            }),
        );
        let call = expect_one_index("Call", plain_call_indices(code));
        let Instruction::GetProperty { object: base, .. } = code[get] else {
            panic!("expected GetProperty");
        };
        let Instruction::Call { this_value, .. } = code[call] else {
            panic!("expected Call");
        };
        assert_eq!(
            this_value, base,
            "matched identifier call uses with object as this"
        );
    }
    #[test]
    fn closure_in_with_body_captures_the_region_and_dispatches_after_exit() {
        let module = lower_js("with (o) { g = function () { return x; }; }");
        assert!(any_instruction(&module, |instruction| {
            matches!(instruction, Instruction::CreateClosure { .. })
        }));
        // Entry also freezes `g` for the assignment; the nested function is the
        // one that both probes membership and reads through GetProperty.
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                let code = function.code();
                code.iter()
                    .any(|instruction| matches!(instruction, Instruction::WithHasBinding { .. }))
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::GetProperty { .. }))
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::Return { .. }))
            })
            .expect("nested function consults captured with region");
        assert_eq!(with_has_binding_indices(inner.code()).len(), 1);
    }
    #[test]
    fn closure_captured_outer_binding_still_consults_with_region() {
        let module =
            lower_js("function f(o) { var x = 1; with (o) { return function () { return x; }; } }");
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 0
                    && function.code().iter().any(|instruction| {
                        matches!(instruction, Instruction::WithHasBinding { .. })
                    })
            })
            .expect("closure over outer var inside with still emits WithHasBinding");
        assert!(
            inner
                .code()
                .iter()
                .any(|instruction| { matches!(instruction, Instruction::GetProperty { .. }) })
        );
    }
    #[test]
    fn closure_with_body_lexical_capture_shadows_object_property() {
        // Lexical `x` declared inside the with body must win over a same-named
        // property on the with object once captured into a nested closure.
        let module =
            lower_js("function f(o) { with (o) { let x = 1; return function () { return x; }; } }");
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 0
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::Return { .. }))
            })
            .expect("closure capturing with-body lexical");
        assert!(
            with_has_binding_indices(inner.code()).is_empty(),
            "captured with-body lexical must not consult the with object property"
        );
    }
    #[test]
    fn nested_closures_propagate_captured_name_with_sites() {
        // Middle frame restores `x` at scope 0 beside the captured with region.
        // Innermost must still inherit site provenance through that boundary —
        // `floor < scope_depth` alone is not enough for captured names.
        let module = lower_js(
            "function f(o) { var x = 1; with (o) { return function () { return function () { return x; }; }; } }",
        );
        let innermost = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 0
                    && function.code().iter().any(|instruction| {
                        matches!(instruction, Instruction::WithHasBinding { .. })
                    })
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::GetProperty { .. }))
            })
            .expect("two-level nested closure must still consult captured with region");
        assert!(
            !with_has_binding_indices(innermost.code()).is_empty(),
            "captured-name with sites must propagate across nested closures"
        );
    }
    #[test]
    fn closure_parameter_shadows_a_captured_with_region() {
        let module = lower_js("with (o) { g = function (x) { return x; }; }");
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::Return { .. }))
            })
            .expect("nested function with parameter");
        assert!(
            inner
                .code()
                .iter()
                .all(|instruction| !matches!(instruction, Instruction::WithHasBinding { .. })),
            "child parameter shadows captured with region"
        );
    }
    #[test]
    fn with_object_expression_cannot_see_its_own_region() {
        let module = lower_js("with (o) { with (x) {} }");
        let code = entry_code(&module);
        let membership = expect_one_index("WithHasBinding", with_has_binding_indices(code));
        let to_objects = to_object_indices(code);
        assert_eq!(to_objects.len(), 2);
        assert!(
            membership < to_objects[1],
            "membership for x precedes the inner ToObject"
        );
    }
    #[test]
    fn with_statement_round_trips() {
        let module = lower_js("with (o) { x = 1; x++; typeof x; delete x; m(); }");
        assert_round_trips(&module);
    }
    #[test]
    fn identifier_read_outside_with_emits_no_membership_test() {
        let module = lower_js("x;");
        assert!(!any_instruction(&module, |instruction| {
            matches!(instruction, Instruction::WithHasBinding { .. })
        }));
    }
    #[test]
    fn with_body_error_still_pops_region() {
        let error = lower_js_result("with (o) { return; }").expect_err("top-level return");
        assert!(matches!(error.kind, LowerErrorKind::ReturnOutsideFunction));
    }

    #[test]
    fn ambient_string_module_lowers_to_empty_module() {
        let module = lower_js("declare module \"pkg\" { export const x: number; }");
        let entry = &module.functions()[module.entry().get() as usize];
        let has_runtime = entry.code().iter().any(|instruction| {
            matches!(
                instruction,
                Instruction::CreateObject { .. }
                    | Instruction::StoreGlobal { .. }
                    | Instruction::Call { .. }
            )
        });
        assert!(
            !has_runtime,
            "ambient string modules must erase to no runtime container work: {:?}",
            entry.code()
        );
    }

    #[test]
    fn identifier_namespace_still_lowers_iife_container() {
        let source = Arc::new(
            SourceText::new("namespace N { export const x = 1 }".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
                ..LowerOptions::default()
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("identifier namespace lowers with namespace facts");
        assert!(
            any_instruction(&module, |instruction| matches!(
                instruction,
                Instruction::CreateObject { .. }
            )),
            "identifier namespaces must keep runtime lowering"
        );
    }

    fn read_names(source: String) -> BTreeSet<String> {
        let parsed = parse(scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
        ));
        value_read_names(parsed.product(), None, false)
    }

    fn left_deep_chain(head: &str, links: &[&str]) -> String {
        let mut source = head.to_owned();
        for index in 0..20_000 {
            source.push_str(links[index % links.len()]);
        }
        source.push_str(";\n");
        source
    }

    fn names(expected: &[&str]) -> BTreeSet<String> {
        expected.iter().map(|name| (*name).to_owned()).collect()
    }

    #[test]
    fn value_reads_of_a_left_deep_member_chain_do_not_overflow() {
        assert_eq!(read_names(left_deep_chain("x", &[".p"])), names(&["x"]));
    }

    #[test]
    fn value_reads_of_a_left_deep_call_chain_do_not_overflow() {
        assert_eq!(
            read_names(left_deep_chain("f", &["(a)"])),
            names(&["a", "f"])
        );
    }

    #[test]
    fn value_reads_of_a_left_deep_mixed_chain_do_not_overflow() {
        assert_eq!(
            read_names(left_deep_chain("x", &[".p", "(a)", "[k]", ".q(b, ...c)"])),
            names(&["a", "b", "c", "k", "x"])
        );
    }

    #[test]
    fn value_reads_of_a_shallow_mixed_spine_are_exact() {
        let source = "class C extends B {\n  #p = 1;\n  constructor() {\n    super(a)[k].#p + d.e(f, ...g) || h;\n  }\n}\n";
        assert_eq!(
            read_names(source.to_owned()),
            names(&["#p", "B", "a", "d", "f", "g", "h", "k"])
        );
    }
