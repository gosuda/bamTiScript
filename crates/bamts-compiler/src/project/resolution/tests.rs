    use super::*;
    use crate::project::canonical::slash_text;
    use crate::project::test_paths::abs;
    use crate::project::{JsonObject, JsonValue, PathMapping, ProjectConfig};
    use std::collections::BTreeMap;

    #[derive(Default)]
    struct MemoryHost {
        files: BTreeMap<PathBuf, Arc<str>>,
        directories: BTreeSet<PathBuf>,
    }

    impl MemoryHost {
        fn file(&mut self, path: impl AsRef<Path>, source: &str) {
            let path = path.as_ref().to_path_buf();
            if let Some(parent) = path.parent() {
                self.mark_dirs(parent);
            }
            self.files.insert(path, Arc::from(source));
        }

        fn mark_dirs(&mut self, path: &Path) {
            let mut current = Some(path);
            while let Some(dir) = current {
                self.directories.insert(dir.to_path_buf());
                current = dir.parent();
            }
        }
    }

    impl ResolutionHost for MemoryHost {
        fn file_exists(&self, path: &Path) -> bool {
            self.files.contains_key(path)
        }

        fn directory_exists(&self, path: &Path) -> bool {
            self.directories.contains(path)
        }

        fn read_file(&self, path: &Path) -> Option<Arc<str>> {
            self.files.get(path).cloned()
        }
    }

    fn root() -> ProjectRoot {
        ProjectRoot::new(abs("/workspace")).expect("absolute root")
    }

    /// How a trace line spells the root of the fixture file system: c: on Windows,
    /// where upstream traces print a lowercase drive, and nothing elsewhere.
    fn trace_drive() -> String {
        slash_text(&abs("/"))
            .trim_end_matches('/')
            .to_ascii_lowercase()
    }

    fn options_with_resolution(module_resolution: &str) -> CompilerOptions {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            &format!(
                r#"{{"compilerOptions":{{"moduleResolution":"{module_resolution}","resolveJsonModule":true}}}}"#
            ),
        )
        .expect("config");
        config.options().clone()
    }

    fn options_with_paths(paths_json: &str) -> CompilerOptions {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            &format!(
                r#"{{"compilerOptions":{{"moduleResolution":"bundler","baseUrl":".","paths":{paths_json}}}}}"#
            ),
        )
        .expect("config");
        config.options().clone()
    }

    #[test]
    fn parses_resolution_kinds_and_resolution_mode_case_insensitively() {
        assert_eq!(
            ModuleResolutionKind::parse("Node16").unwrap(),
            ModuleResolutionKind::Node16
        );
        assert_eq!(
            ModuleResolutionKind::parse("nodenext").unwrap(),
            ModuleResolutionKind::NodeNext
        );
        assert_eq!(
            ModuleResolutionKind::parse("BUNDLER").unwrap(),
            ModuleResolutionKind::Bundler
        );
        assert_eq!(
            ModuleResolutionKind::parse("Classic").unwrap(),
            ModuleResolutionKind::Classic
        );
        assert!(ModuleResolutionKind::parse("node10").is_err());
        assert_eq!(
            ResolutionMode::parse("import").unwrap(),
            ResolutionMode::Import
        );
        assert_eq!(
            ResolutionMode::parse("require").unwrap(),
            ResolutionMode::Require
        );
        assert!(ResolutionMode::parse("eval").is_err());
        assert!(ModuleResolutionKind::Bundler.allows_extensionless_relative());
        assert!(ModuleResolutionKind::Classic.allows_extensionless_relative());
        assert!(!ModuleResolutionKind::Node16.allows_extensionless_relative());
    }

    #[test]
    fn classic_walks_up_ancestor_directories_for_bare_specifiers() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/ref/m1.ts"), "export const m1 = 1;\n");
        host.file(
            abs("/workspace/a/outputdir_ref/m2.tsx"),
            "export const m2 = 2;\n",
        );
        host.file(abs("/workspace/node_modules/left.ts"), "export {};\n");
        let options = options_with_resolution("classic");
        let mut cache = ResolutionCache::new();
        let importer = abs("/workspace/a/b/test.ts");

        let bare = resolve_module_name(
            &root(),
            &options,
            &importer,
            "ref/m1",
            (ModuleResolutionKind::Classic, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("bare specifier resolves from an ancestor directory");
        assert_eq!(bare.path(), abs("/workspace/ref/m1.ts").as_path());

        let relative = resolve_module_name(
            &root(),
            &options,
            &importer,
            "../outputdir_ref/m2",
            (ModuleResolutionKind::Classic, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("relative specifier resolves beside the importer");
        assert_eq!(
            relative.path(),
            abs("/workspace/a/outputdir_ref/m2.tsx").as_path()
        );

        let declaration = resolve_module_name(
            &root(),
            &options,
            &importer,
            "ref/m1",
            (ModuleResolutionKind::Classic, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("second lookup stays cached and identical");
        assert_eq!(declaration, bare);

        assert!(!bare.trace().steps().iter().any(|step| matches!(
            step,
            ResolutionTraceStep::NodeModulesWalk { .. } | ResolutionTraceStep::TypesFallback { .. }
        )));
        assert!(bare.trace().steps().iter().any(|step| matches!(
            step,
            ResolutionTraceStep::Candidate { path, .. }
                if path == abs("/workspace/a/b/ref/m1.ts").as_path(),
        )));
    }

    #[test]
    fn classic_prefers_type_script_extensions_and_gates_js_on_allow_js() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/dep.js"), "export {};\n");
        let mut cache = ResolutionCache::new();
        let importer = abs("/workspace/a/test.ts");

        let without_allow_js = options_with_resolution("classic");
        let miss = resolve_module_name(
            &root(),
            &without_allow_js,
            &importer,
            "dep",
            (ModuleResolutionKind::Classic, ResolutionMode::Require),
            &host,
            &mut cache,
        );
        assert!(matches!(miss, Err(ResolutionError::NotFound { .. })));

        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"classic","allowJs":true}}"#,
        )
        .expect("config");
        let with_allow_js = config.options().clone();
        let mut cache = ResolutionCache::new();
        let found = resolve_module_name(
            &root(),
            &with_allow_js,
            &importer,
            "dep",
            (ModuleResolutionKind::Classic, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("js candidate joins the family under allowJs");
        assert_eq!(found.path(), abs("/workspace/dep.js").as_path());
    }

    #[test]
    fn relative_extension_substitution_and_index_fallback() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/util.ts"), "export const n = 1;\n");
        host.file(abs("/workspace/src/nested/index.ts"), "export {};\n");
        let options = options_with_resolution("node16");
        let mut cache = ResolutionCache::new();

        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./util.js",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("util.js → util.ts");
        assert_eq!(resolved.path(), abs("/workspace/src/util.ts").as_path());
        assert!(
            resolved
                .trace()
                .steps()
                .iter()
                .any(|step| matches!(step, ResolutionTraceStep::Candidate { exists: true, .. }))
        );

        let nested = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./nested",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("directory index");
        assert_eq!(
            nested.path(),
            abs("/workspace/src/nested/index.ts").as_path()
        );
    }
    #[test]
    fn nodenext_import_requires_relative_extension_but_require_and_bundler_do_not() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/util.ts"), "export const n = 1;\n");
        let options = options_with_resolution("nodenext");
        let mut cache = ResolutionCache::new();
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./util",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
        for strategy in [
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
        ] {
            let resolved = resolve_module_name(
                &root(),
                &options,
                abs("/workspace/src/main.ts"),
                "./util",
                strategy,
                &host,
                &mut cache,
            )
            .expect("extensionless resolution is permitted");
            assert_eq!(resolved.path(), abs("/workspace/src/util.ts").as_path());
        }
    }

    #[test]
    fn nodenext_require_resolves_bare_package_index_without_manifest() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, CJS importer resolving
        // in CJS mode): a manifest-less package resolves to its directory index.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("CJS importer resolves a manifest-less package to its directory index");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/index.ts").as_path()
        );
    }

    #[test]
    fn node16_require_resolves_bare_package_index_without_manifest() {
        // Oracle (tsc 7.0.2, moduleResolution node16, CJS importer): same rule.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("node16");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::Node16, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("CJS importer resolves a manifest-less package to its directory index");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/index.ts").as_path()
        );
    }

    #[test]
    fn nodenext_import_rejects_bare_package_index_without_manifest() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, ESM importer resolving
        // in ESM mode): a package with no package.json gets no file probing,
        // so `dep` is not resolved.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.mts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut ResolutionCache::new(),
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
    }

    #[test]
    fn node16_import_rejects_bare_package_index_without_manifest() {
        // Oracle (tsc 7.0.2, moduleResolution node16, ESM importer): same rule.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("node16");
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.mts"),
            "dep",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut ResolutionCache::new(),
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
    }

    #[test]
    fn nodenext_import_resolves_bare_package_index_with_manifest() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, ESM importer): a package
        // whose manifest has neither `main` nor `exports` keeps the legacy
        // `index` default, resolved with extension substitution.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/package.json"),
            r#"{"name":"dep","version":"1.0.0"}"#,
        );
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.mts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("ESM importer resolves the legacy index default when a manifest exists");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/index.ts").as_path()
        );
    }

    #[test]
    fn nodenext_import_rejects_extensionless_subpath_even_with_manifest() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, ESM importer):
        // `dep/sub` without an extension never resolves, manifest or not.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/package.json"),
            r#"{"name":"dep","version":"1.0.0"}"#,
        );
        host.file(
            abs("/workspace/node_modules/dep/sub.ts"),
            "export const s = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.mts"),
            "dep/sub",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut ResolutionCache::new(),
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
    }

    #[test]
    fn nodenext_require_prefers_ts_over_tsx_in_directory_index() {
        // Guards the candidate order inside one index stem: with both
        // `dep/index.ts` and `dep/index.tsx` present, the `.ts` candidate
        // wins. Mutating the plan to probe `.tsx` first resolves the wrong
        // file and fails this test.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        host.file(
            abs("/workspace/node_modules/dep/index.tsx"),
            "export const a = 2;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("directory index resolves");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/index.ts").as_path()
        );
    }

    #[test]
    fn mode_for_importer_prefers_extension_then_package_type() {
        let root = root();
        let bare = MemoryHost::default();
        for importer in [
            "/workspace/src/main.mts",
            "/workspace/src/main.mjs",
            "/workspace/src/main.d.mts",
        ] {
            assert_eq!(
                mode_for_importer(&bare, &root, abs(importer).as_path()),
                ResolutionMode::Import,
                "{importer} resolves in ESM mode",
            );
        }
        for importer in [
            "/workspace/src/main.cts",
            "/workspace/src/main.cjs",
            "/workspace/src/main.d.cts",
        ] {
            assert_eq!(
                mode_for_importer(&bare, &root, abs(importer).as_path()),
                ResolutionMode::Require,
                "{importer} resolves in CJS mode",
            );
        }
        // A plain `.ts` file with no package scope defaults to CJS, whatever
        // the tsconfig `module` says (oracle: `module: nodenext` still CJS).
        assert_eq!(
            mode_for_importer(&bare, &root, abs("/workspace/src/main.ts").as_path()),
            ResolutionMode::Require,
        );
        let mut module_scope = MemoryHost::default();
        module_scope.file(
            abs("/workspace/package.json"),
            r#"{"name":"app","type":"module"}"#,
        );
        assert_eq!(
            mode_for_importer(
                &module_scope,
                &root,
                abs("/workspace/src/main.ts").as_path()
            ),
            ResolutionMode::Import,
        );
        // The extension beats the package type: `.mts` stays ESM inside a
        // CommonJS package, and `.cts` stays CJS inside an ESM package.
        assert_eq!(
            mode_for_importer(
                &module_scope,
                &root,
                abs("/workspace/src/main.cts").as_path()
            ),
            ResolutionMode::Require,
        );
        let mut commonjs_scope = MemoryHost::default();
        commonjs_scope.file(
            abs("/workspace/package.json"),
            r#"{"name":"app","type":"commonjs"}"#,
        );
        assert_eq!(
            mode_for_importer(
                &commonjs_scope,
                &root,
                abs("/workspace/src/main.mts").as_path()
            ),
            ResolutionMode::Import,
        );
        assert_eq!(
            mode_for_importer(
                &commonjs_scope,
                &root,
                abs("/workspace/src/main.ts").as_path()
            ),
            ResolutionMode::Require,
        );
        // The nearest manifest wins over an outer one.
        let mut nested_scope = MemoryHost::default();
        nested_scope.file(
            abs("/workspace/package.json"),
            r#"{"name":"app","type":"module"}"#,
        );
        nested_scope.file(
            abs("/workspace/src/package.json"),
            r#"{"name":"inner","type":"commonjs"}"#,
        );
        assert_eq!(
            mode_for_importer(
                &nested_scope,
                &root,
                abs("/workspace/src/main.ts").as_path()
            ),
            ResolutionMode::Require,
        );
    }

    #[test]
    fn nodenext_require_probes_package_stem_before_directory_index() {
        // Oracle (tsc 7.0.2, CJS mode, empty-`dep/`-directory trace): a bare
        // package probes `dep.ts` before `dep/index.ts`. The old plan probed
        // only `./index`, so the stem file below was missed.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("CJS importer probes the package stem");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep.ts").as_path()
        );
    }

    #[test]
    fn nodenext_require_prefers_stem_file_over_index_file() {
        // Oracle probe order: `dep.ts` precedes `dep/index.ts`.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep.ts"),
            "export const a = 1;\n",
        );
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 2;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("stem file beats directory index");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep.ts").as_path()
        );
    }

    #[test]
    fn nodenext_require_prefers_typescript_pass_over_javascript_fallback() {
        // Oracle: `dep/index.ts` (preferred pass) beats `dep.js` (fallback
        // pass). A single-pass `ts,tsx,…,js,jsx` order would resolve `dep.js`.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep.js"),
            "module.exports = {};\n",
        );
        host.file(
            abs("/workspace/node_modules/dep/index.ts"),
            "export const a = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("preferred pass beats fallback pass");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/index.ts").as_path()
        );
    }

    #[test]
    fn nodenext_require_resolves_legacy_index_js_with_manifest() {
        // Oracle (tsc 7.0.2, CJS importer, manifest without `main`): the
        // legacy `index` default resolves `index.js` when no `index.ts`
        // exists.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/package.json"),
            r#"{"name":"dep","version":"1.0.0"}"#,
        );
        host.file(
            abs("/workspace/node_modules/dep/index.js"),
            "module.exports = {};\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("legacy index default resolves index.js");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/index.js").as_path()
        );
    }

    #[test]
    fn nodenext_require_resolves_extensionless_subpath_without_manifest() {
        // Oracle (tsc 7.0.2, CJS mode): `dep/sub` probes `sub.ts` even with
        // no manifest anywhere in the package.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/dep/sub.ts"),
            "export const s = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "dep/sub",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("CJS importer probes subpath stems");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/dep/sub.ts").as_path()
        );
    }

    #[test]
    fn nodenext_require_probes_declaration_before_javascript() {
        // Oracle (empty-directory trace): `foo.d.ts` precedes `foo.js`.
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/foo.d.ts"), "export {};\n");
        host.file(abs("/workspace/src/foo.js"), "module.exports = {};\n");
        let options = options_with_resolution("nodenext");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "./foo",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("declaration beats javascript");
        assert_eq!(resolved.path(), abs("/workspace/src/foo.d.ts").as_path());
    }

    #[test]
    fn nodenext_require_ignores_extensionless_file_and_json() {
        // Oracle: neither a file literally named `foo` nor `foo.json` (even
        // with `resolveJsonModule`) resolves an extensionless relative import.
        let options = options_with_resolution("nodenext");
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/foo"), "anything\n");
        host.file(abs("/workspace/src/foo.json"), "{}\n");
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "./foo",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
    }

    #[test]
    fn nodenext_import_rejects_extensionless_exports_target() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, ESM importer):
        // `exports` target `./index` without an extension is not resolved.
        // The synthesized target therefore keeps the user-written guard.
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/pkg/package.json"),
            r#"{"name":"pkg","version":"1.0.0","exports":{".":"./index"}}"#,
        );
        host.file(
            abs("/workspace/node_modules/pkg/index.ts"),
            "export const p = 1;\n",
        );
        let options = options_with_resolution("nodenext");
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.mts"),
            "pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut ResolutionCache::new(),
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
    }

    #[test]
    fn nodenext_require_resolves_extensionless_paths_target() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, CJS importer): a
        // `paths` target without an extension probes with substitution.
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"nodenext","baseUrl":".","paths":{"@app/*":["./lib/*"]}}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/lib/data.ts"), "export const d = 1;\n");
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.cts"),
            "@app/data",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut ResolutionCache::new(),
        )
        .expect("paths target probes with substitution");
        assert_eq!(resolved.path(), abs("/workspace/lib/data.ts").as_path());
    }

    #[test]
    fn nodenext_import_rejects_extensionless_paths_target() {
        // Oracle (tsc 7.0.2, moduleResolution nodenext, ESM importer): a
        // `paths` target without an extension is not resolved.
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"nodenext","baseUrl":".","paths":{"@app/*":["./lib/*"]}}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/lib/data.ts"), "export const d = 1;\n");
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.mts"),
            "@app/data",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut ResolutionCache::new(),
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
    }

    #[test]
    fn paths_longest_prefix_wins_with_star_substitution() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/lib/foo/bar.ts"), "export {};\n");
        let options = options_with_paths(r#"{ "@app/*": ["lib/*"], "@app/foo/*": ["lib/foo/*"] }"#);
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "@app/foo/bar",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("paths");
        assert_eq!(resolved.path(), abs("/workspace/lib/foo/bar.ts").as_path());
        assert!(resolved.trace().steps().iter().any(|step| matches!(
            step,
            ResolutionTraceStep::PathsMatch { pattern, .. } if pattern.as_ref() == "@app/foo/*"
        )));
    }

    #[test]
    fn package_exports_honor_resolution_mode_conditions() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/pkg/package.json"),
            r#"{
                "name":"pkg",
                "exports":{
                    ".":{
                        "import":"./esm.js",
                        "require":"./cjs.js"
                    }
                }
            }"#,
        );
        host.file(abs("/workspace/node_modules/pkg/esm.js"), "export {};\n");
        host.file(
            abs("/workspace/node_modules/pkg/cjs.js"),
            "module.exports = {};\n",
        );
        // Provide TS stand-ins so extension substitution can succeed for both modes.
        host.file(abs("/workspace/node_modules/pkg/esm.ts"), "export {};\n");
        host.file(abs("/workspace/node_modules/pkg/cjs.ts"), "export {};\n");

        let options = options_with_resolution("nodenext");
        let mut cache = ResolutionCache::new();

        let import_hit = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("import condition");
        assert_eq!(
            import_hit.path(),
            abs("/workspace/node_modules/pkg/esm.ts").as_path()
        );

        let require_hit = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("require condition");
        assert_eq!(
            require_hit.path(),
            abs("/workspace/node_modules/pkg/cjs.ts").as_path()
        );
    }
    #[test]
    fn package_exports_block_private_and_null_subpaths() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/pkg/package.json"),
            r#"{"exports":{".":"./index.js","./blocked":null}}"#,
        );
        host.file(abs("/workspace/node_modules/pkg/index.ts"), "export {};\n");
        host.file(
            abs("/workspace/node_modules/pkg/private.ts"),
            "export {};\n",
        );
        host.file(
            abs("/workspace/node_modules/pkg/blocked.ts"),
            "export {};\n",
        );
        let options = options_with_resolution("nodenext");
        for specifier in ["pkg/private", "pkg/blocked"] {
            let error = resolve_module_name(
                &root(),
                &options,
                abs("/workspace/src/main.ts"),
                specifier,
                (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
                &host,
                &mut ResolutionCache::new(),
            )
            .expect_err("exports encapsulation blocks filesystem fallback");
            assert!(matches!(
                error,
                ResolutionError::Package(PackageError::SubpathNotExported { .. })
                    | ResolutionError::Package(PackageError::TargetBlocked)
            ));
        }
    }

    #[test]
    fn package_imports_resolve_and_detect_cycles() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/package.json"),
            r##"{
                "name":"app",
                "imports":{
                    "#internal/*": "./src/*.ts",
                    "#loop": "#loop"
                }
            }"##,
        );
        host.file(abs("/workspace/src/value.ts"), "export const v = 1;\n");
        host.file(abs("/workspace/src/main.ts"), "import '#internal/value';\n");

        let options = options_with_resolution("bundler");
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "#internal/value",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("hash import");
        assert_eq!(resolved.path(), abs("/workspace/src/value.ts").as_path());

        let cycle = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "#loop",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect_err("self-import cycle");
        assert!(matches!(cycle, ResolutionError::PackageCycle { .. }));
    }

    #[test]
    fn node_modules_walk_stops_at_project_root_and_confinement_rejects_escape() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/left-pad/package.json"),
            r#"{"name":"left-pad","main":"./index.js"}"#,
        );
        host.file(
            abs("/workspace/node_modules/left-pad/index.ts"),
            "export {};\n",
        );
        host.file(
            abs("/workspace/node_modules/left-pad/index.js"),
            "module.exports = {};\n",
        );

        let options = options_with_resolution("node16");
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/packages/app/src/main.ts"),
            "left-pad",
            (ModuleResolutionKind::Node16, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("upward walk");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/left-pad/index.ts").as_path()
        );
        assert!(
            resolved
                .trace()
                .steps()
                .iter()
                .any(|step| matches!(step, ResolutionTraceStep::NodeModulesWalk { .. }))
        );

        let escape = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "../../outside",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(escape.is_err(), "escaping relative must fail");
    }

    #[test]
    fn types_fallback_mangles_scoped_package_names() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/@types/scope__pkg/index.d.ts"),
            "export {};\n",
        );
        let options = options_with_resolution("nodenext");
        let mut cache = ResolutionCache::new();
        let resolved = resolve_type_reference(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "@scope/pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("@types scope mangling");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/@types/scope__pkg/index.d.ts").as_path()
        );
        assert!(resolved.trace().steps().iter().any(|step| matches!(
            step,
            ResolutionTraceStep::TypesFallback { package, .. }
                if package.as_ref() == "@types/scope__pkg"
        )));
    }

    #[test]
    fn cache_returns_identical_results_for_repeated_lookups() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/a.ts"), "export {};\n");
        let options = options_with_resolution("bundler");
        let mut cache = ResolutionCache::new();
        let first = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./a",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("first");
        let second = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./a",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("second");
        assert_eq!(first, second);
        assert_eq!(cache.len(), 1);

        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./missing",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(missing.is_err());
        let missing_again = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./missing",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert_eq!(
            missing.as_ref().err().map(ToString::to_string),
            missing_again.err().map(|e| e.to_string())
        );
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn trace_is_deterministic_across_two_fresh_caches() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/demo/package.json"),
            r#"{"name":"demo","exports":{".":{"import":"./lib.js"}}}"#,
        );
        host.file(abs("/workspace/node_modules/demo/lib.ts"), "export {};\n");
        host.file(abs("/workspace/node_modules/demo/lib.js"), "export {};\n");
        let options = options_with_resolution("node16");

        let mut cache_a = ResolutionCache::new();
        let a = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "demo",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache_a,
        )
        .expect("a");
        let mut cache_b = ResolutionCache::new();
        let b = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "demo",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache_b,
        )
        .expect("b");
        assert_eq!(a.trace(), b.trace());
    }

    #[test]
    fn from_options_reads_compiler_module_resolution() {
        let options = options_with_resolution("bundler");
        assert_eq!(
            ModuleResolutionKind::from_options(&options).unwrap(),
            ModuleResolutionKind::Bundler
        );
        // Prove PathMapping surface remains the shared model (no duplicate paths type).
        let _mappings: &[PathMapping] = options.paths();
        let _object_ty: Option<&JsonObject> = None;
        let _value_ty: Option<&JsonValue> = None;
    }
    fn options_with_module(module: &str) -> CompilerOptions {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            &format!(r#"{{"compilerOptions":{{"module":"{module}"}}}}"#),
        )
        .expect("config");
        config.options().clone()
    }
    fn options_with_type_roots(roots: &str) -> CompilerOptions {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            &format!(r#"{{"compilerOptions":{{"typeRoots":{roots}}}}}"#),
        )
        .expect("config");
        config.options().clone()
    }

    #[test]
    fn type_roots_probe_resolves_named_package_first() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/types/lib/index.d.ts"),
            "declare const x: number;\n",
        );
        host.file(
            abs("/workspace/node_modules/@types/lib/index.d.ts"),
            "declare const y: number;\n",
        );
        let options = options_with_type_roots(r#"["types"]"#);
        let mut cache = ResolutionCache::new();
        let resolved = resolve_type_reference(
            &root(),
            &options,
            abs("/workspace/app.ts"),
            "lib",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("typeRoots probe resolves");
        assert_eq!(
            resolved.path(),
            abs("/workspace/types/lib/index.d.ts").as_path()
        );
    }

    #[test]
    fn type_roots_miss_falls_back_to_at_types_walk() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/@types/beep__boop/index.d.ts"),
            "export const y: number;\n",
        );
        let options = options_with_type_roots(r#"["types"]"#);
        let mut cache = ResolutionCache::new();
        let resolved = resolve_type_reference(
            &root(),
            &options,
            abs("/workspace/a.ts"),
            "@beep/boop",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("at-types fallback still resolves");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/@types/beep__boop/index.d.ts").as_path()
        );
    }

    #[test]
    fn type_roots_miss_without_at_types_stays_unresolved() {
        let host = MemoryHost::default();
        let options = options_with_type_roots(r#"["types"]"#);
        let mut cache = ResolutionCache::new();
        let outcome = resolve_type_reference(
            &root(),
            &options,
            abs("/workspace/a.ts"),
            "mangled",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(matches!(
            outcome,
            Err(ResolutionError::NotFound { .. })
        ));
    }

    #[test]
    fn from_options_defaults_classic_for_legacy_module_formats() {
        for module in ["amd", "AMD", " system ", "umd", "UMD"] {
            let options = options_with_module(module);
            assert_eq!(
                ModuleResolutionKind::from_options(&options).unwrap(),
                ModuleResolutionKind::Classic,
                "module `{module}` defaults to classic"
            );
        }
        for module in ["commonjs", "CommonJS", "node16", "preserve"] {
            let options = options_with_module(module);
            assert_eq!(
                ModuleResolutionKind::from_options(&options).unwrap(),
                ModuleResolutionKind::NodeNext,
                "module `{module}` keeps the NodeNext default"
            );
        }
        let unset = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{}}"#,
        )
        .expect("config")
        .options()
        .clone();
        // Oracle (tsc 7.0.2, `--traceResolution` on a scratch project with
        // neither `module` nor `moduleResolution`): `Module resolution kind
        // is not specified, using 'Bundler'`.
        assert_eq!(
            ModuleResolutionKind::from_options(&unset).unwrap(),
            ModuleResolutionKind::Bundler
        );
        let explicit = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"module":"amd","moduleResolution":"nodenext"}}"#,
        )
        .expect("config")
        .options()
        .clone();
        assert_eq!(
            ModuleResolutionKind::from_options(&explicit).unwrap(),
            ModuleResolutionKind::NodeNext
        );
    }

    #[test]
    fn amd_default_resolves_bare_sibling_import() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/m1.ts"), "export const m1 = 1;\n");
        host.file(
            abs("/workspace/m2.ts"),
            "import m1 = require('m1');\nexport const v = m1;\n",
        );
        let options = options_with_module("amd");
        let kind = ModuleResolutionKind::from_options(&options).unwrap();
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/m2.ts"),
            "m1",
            (kind, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("bare sibling import resolves under the amd classic default");
        assert_eq!(resolved.path(), abs("/workspace/m1.ts").as_path());
    }

    #[test]
    fn amd_default_keeps_missing_bare_import_unresolved() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/m2.ts"),
            "import m1 = require('zzz_missing_sibling');\nexport const v = m1;\n",
        );
        let options = options_with_module("system");
        let kind = ModuleResolutionKind::from_options(&options).unwrap();
        let mut cache = ResolutionCache::new();
        let outcome = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/m2.ts"),
            "zzz_missing_sibling",
            (kind, ResolutionMode::Require),
            &host,
            &mut cache,
        );
        assert!(matches!(
            outcome,
            Err(ResolutionError::NotFound { .. })
        ));
    }
    #[test]
    fn trace_kind_line_marks_unspecified_resolution_kind() {
        let unspecified = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{}}"#,
        )
        .expect("config")
        .options()
        .clone();
        let specified = options_with_resolution("bundler");
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/other.ts"), "export {};\n");
        for (options, expected) in [
            (
                unspecified,
                "Module resolution kind is not specified, using 'Bundler'.",
            ),
            (
                specified,
                "Explicitly specified module resolution kind: 'Bundler'.",
            ),
        ] {
            let mut cache = ResolutionCache::new();
            let mut log = ResolutionTraceLog::default();
            resolve_module_name_with_trace(
                &root(),
                &options,
                abs("/workspace/main.ts"),
                "./other",
                (
                    ModuleResolutionKind::Bundler,
                    ResolutionMode::Import,
                    ResolutionFlavor::Runtime,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .expect("relative resolution");
            assert!(
                log.lines().iter().any(|line| line == expected),
                "missing `{expected}` in {:?}",
                log.lines()
            );
        }
    }
    #[test]
    fn trace_bundler_bare_miss_matches_upstream_walk() {
        let options = options_with_resolution("bundler");
        let host = MemoryHost::default();
        let mut cache = ResolutionCache::new();
        let mut log = ResolutionTraceLog::default();
        let outcome = resolve_module_name_with_trace(
            &root(),
            &options,
            abs("/workspace/a/b/c/lib.ts"),
            "foo",
            (
                ModuleResolutionKind::Bundler,
                ResolutionMode::Import,
                ResolutionFlavor::Runtime,
            ),
            TraceResolutionServices {
                host: &host,
                cache: &mut cache,
                log: &mut log,
            },
        );
        assert!(outcome.is_err());
        let expected: &[&str] = &[
            "======== Resolving module 'foo' from '/workspace/a/b/c/lib.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in CJS mode with conditions 'import', 'types'.",
            "File '/workspace/a/b/c/package.json' does not exist.",
            "File '/workspace/a/b/package.json' does not exist.",
            "File '/workspace/a/package.json' does not exist.",
            "File '/workspace/package.json' does not exist.",
            "Loading module 'foo' from 'node_modules' folder, target file types: TypeScript, JavaScript, Declaration, JSON.",
            "Searching all ancestor node_modules directories for preferred extensions: TypeScript, Declaration.",
            "Directory '/workspace/a/b/c/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/b/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/node_modules' does not exist, skipping all lookups in it.",
            "Searching all ancestor node_modules directories for fallback extensions: JavaScript, JSON.",
            "Directory '/workspace/a/b/c/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/b/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/node_modules' does not exist, skipping all lookups in it.",
            "======== Module name 'foo' was not resolved. ========",
        ];
        let drive = trace_drive();
        let expected: Vec<String> = expected
            .iter()
            .map(|line| line.replace("'/workspace", &format!("'{drive}/workspace")))
            .collect();
        let produced: Vec<&str> = log.lines().iter().map(String::as_str).collect();
        assert_eq!(produced, expected);
        assert!(log.unsupported().is_empty());
    }
    #[test]
    fn trace_bundler_subpath_package_scope_matches_upstream_found_lines() {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"module":"commonjs"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/foo/bar/package.json"),
            "{ \"types\": \"types.d.ts\" }\n",
        );
        host.file(abs("/workspace/node_modules/foo/package.json"), "{}\n");
        host.file(
            abs("/workspace/node_modules/foo/bar/types.d.ts"),
            "export const x: number;\n",
        );
        let mut cache = ResolutionCache::new();
        let mut log = ResolutionTraceLog::default();
        let resolved = resolve_module_name_with_trace(
            &root(),
            &options,
            abs("/workspace/a.ts"),
            "foo/bar",
            (
                ModuleResolutionKind::Bundler,
                ResolutionMode::Require,
                ResolutionFlavor::Runtime,
            ),
            TraceResolutionServices {
                host: &host,
                cache: &mut cache,
                log: &mut log,
            },
        )
        .expect("subpath types hit");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/foo/bar/types.d.ts").as_path()
        );
        let expected: &[&str] = &[
            "======== Resolving module 'foo/bar' from '/workspace/a.ts'. ========",
            "Module resolution kind is not specified, using 'Bundler'.",
            "Resolving in CJS mode with conditions 'require', 'types'.",
            "File '/workspace/package.json' does not exist.",
            "Loading module 'foo/bar' from 'node_modules' folder, target file types: TypeScript, JavaScript, Declaration, JSON.",
            "Searching all ancestor node_modules directories for preferred extensions: TypeScript, Declaration.",
            "Found 'package.json' at '/workspace/node_modules/foo/bar/package.json'.",
            "Found 'package.json' at '/workspace/node_modules/foo/package.json'.",
            "File '/workspace/node_modules/foo/bar.ts' does not exist.",
            "File '/workspace/node_modules/foo/bar.tsx' does not exist.",
            "File '/workspace/node_modules/foo/bar.d.ts' does not exist.",
            "'package.json' does not have a 'typesVersions' field.",
            "'package.json' does not have a 'typings' field.",
            "'package.json' has 'types' field 'types.d.ts' that references '/workspace/node_modules/foo/bar/types.d.ts'.",
            "File '/workspace/node_modules/foo/bar/types.d.ts' exists - use it as a name resolution result.",
            "Resolving real path for '/workspace/node_modules/foo/bar/types.d.ts', result '/workspace/node_modules/foo/bar/types.d.ts'.",
            "======== Module name 'foo/bar' was successfully resolved to '/workspace/node_modules/foo/bar/types.d.ts'. ========",
            "File '/workspace/node_modules/foo/bar/package.json' exists according to earlier cached lookups.",
        ];
        let drive = trace_drive();
        let expected: Vec<String> = expected
            .iter()
            .map(|line| line.replace("'/workspace", &format!("'{drive}/workspace")))
            .collect();
        let produced: Vec<&str> = log.lines().iter().map(String::as_str).collect();
        assert_eq!(produced, expected);
        assert!(log.unsupported().is_empty());
    }
    #[test]
    fn trace_bundler_loose_file_hit_matches_upstream_probes() {
        let options = options_with_resolution("bundler");
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/a/b/node_modules/foo.d.ts"),
            "export declare const x: number;\n",
        );
        let mut cache = ResolutionCache::new();
        let mut log = ResolutionTraceLog::default();
        let resolved = resolve_module_name_with_trace(
            &root(),
            &options,
            abs("/workspace/a/b/c/d/e/app.ts"),
            "foo",
            (
                ModuleResolutionKind::Bundler,
                ResolutionMode::Import,
                ResolutionFlavor::Runtime,
            ),
            TraceResolutionServices {
                host: &host,
                cache: &mut cache,
                log: &mut log,
            },
        )
        .expect("loose declaration hit");
        assert_eq!(
            resolved.path(),
            abs("/workspace/a/b/node_modules/foo.d.ts").as_path()
        );
        let expected: &[&str] = &[
            "======== Resolving module 'foo' from '/workspace/a/b/c/d/e/app.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in CJS mode with conditions 'import', 'types'.",
            "File '/workspace/a/b/c/d/e/package.json' does not exist.",
            "File '/workspace/a/b/c/d/package.json' does not exist.",
            "File '/workspace/a/b/c/package.json' does not exist.",
            "File '/workspace/a/b/package.json' does not exist.",
            "File '/workspace/a/package.json' does not exist.",
            "File '/workspace/package.json' does not exist.",
            "Loading module 'foo' from 'node_modules' folder, target file types: TypeScript, JavaScript, Declaration, JSON.",
            "Searching all ancestor node_modules directories for preferred extensions: TypeScript, Declaration.",
            "Directory '/workspace/a/b/c/d/e/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/b/c/d/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/b/c/node_modules' does not exist, skipping all lookups in it.",
            "File '/workspace/a/b/node_modules/foo.ts' does not exist.",
            "File '/workspace/a/b/node_modules/foo.tsx' does not exist.",
            "File '/workspace/a/b/node_modules/foo.d.ts' exists - use it as a name resolution result.",
            "Resolving real path for '/workspace/a/b/node_modules/foo.d.ts', result '/workspace/a/b/node_modules/foo.d.ts'.",
            "======== Module name 'foo' was successfully resolved to '/workspace/a/b/node_modules/foo.d.ts'. ========",
        ];
        let drive = trace_drive();
        let expected: Vec<String> = expected
            .iter()
            .map(|line| line.replace("'/workspace", &format!("'{drive}/workspace")))
            .collect();
        let produced: Vec<&str> = log.lines().iter().map(String::as_str).collect();
        assert_eq!(produced, expected);
        assert!(log.unsupported().is_empty());
    }
    #[test]
    fn trace_log_matches_upstream_bundler_relative_blob() {
        // Lines pinned byte-for-byte to the upstream baselines
        // `bundlerRelative1(module=esnext).trace.json` and
        // `bundlerRelative1(module=preserve).trace.json` (byte-identical; the
        // `./dir/index`, `./dir/index.js`, and `./dir/index.ts` blocks) plus
        // the cache-hit re-resolution template. Upstream renders Bundler
        // resolutions in CJS mode even for `import` conditions: every
        // `bundler*.trace.json` baseline prints `Resolving in CJS mode`, and
        // ESM mode appears only under Node16/NodeNext.
        let expected: &[&str] = &[
            "======== Resolving module './dir/index' from '/main.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in CJS mode with conditions 'import', 'types'.",
            "Loading module as file / folder, candidate module location '/dir/index', target file types: TypeScript, JavaScript, Declaration, JSON.",
            "File '/dir/index.ts' exists - use it as a name resolution result.",
            "======== Module name './dir/index' was successfully resolved to '/dir/index.ts'. ========",
            "======== Resolving module './dir/index.js' from '/main.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in CJS mode with conditions 'import', 'types'.",
            "Loading module as file / folder, candidate module location '/dir/index.js', target file types: TypeScript, JavaScript, Declaration, JSON.",
            "File name '/dir/index.js' has a '.js' extension - stripping it.",
            "File '/dir/index.ts' exists - use it as a name resolution result.",
            "======== Module name './dir/index.js' was successfully resolved to '/dir/index.ts'. ========",
            "======== Resolving module './dir/index.ts' from '/main.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in CJS mode with conditions 'import', 'types'.",
            "Loading module as file / folder, candidate module location '/dir/index.ts', target file types: TypeScript, JavaScript, Declaration, JSON.",
            "File name '/dir/index.ts' has a '.ts' extension - stripping it.",
            "File '/dir/index.ts' exists - use it as a name resolution result.",
            "======== Module name './dir/index.ts' was successfully resolved to '/dir/index.ts'. ========",
            "======== Resolving module './dir/index' from '/main.ts'. ========",
            "Resolution for module './dir/index' was found in cache from location '/'.",
            "======== Module name './dir/index' was successfully resolved to '/dir/index.ts'. ========",
        ];

        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let config = ProjectConfig::parse(
            &fs_root,
            abs("/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/main.ts"), "import {} from './dir/index.js';\n");
        host.file(abs("/dir/index.ts"), "export {};\n");
        let mut cache = ResolutionCache::new();
        let mut log = ResolutionTraceLog::default();

        for specifier in ["./dir/index", "./dir/index.js", "./dir/index.ts"] {
            resolve_module_name_with_trace(
                &fs_root,
                &options,
                abs("/main.ts"),
                specifier,
                (
                    ModuleResolutionKind::Bundler,
                    ResolutionMode::Import,
                    ResolutionFlavor::Runtime,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .unwrap_or_else(|error| panic!("resolve {specifier}: {error}"));
        }
        resolve_module_name_with_trace(
            &fs_root,
            &options,
            abs("/main.ts"),
            "./dir/index",
            (
                ModuleResolutionKind::Bundler,
                ResolutionMode::Import,
                ResolutionFlavor::Runtime,
            ),
            TraceResolutionServices {
                host: &host,
                cache: &mut cache,
                log: &mut log,
            },
        )
        .expect("cache hit");

        let drive = trace_drive();
        let expected: Vec<String> = expected
            .iter()
            .map(|line| line.replace("'/", &format!("'{drive}/")))
            .collect();
        let produced: Vec<&str> = log.lines().iter().map(String::as_str).collect();
        assert_eq!(produced, expected);
        assert!(log.unsupported().is_empty());
    }
    #[test]
    fn trace_bundler_mode_word_is_cjs_for_both_modes() {
        // Upstream renders Bundler resolutions in CJS mode for both `import`
        // and `require` conditions (no `bundler*.trace.json` baseline prints
        // ESM mode); only the condition word follows the resolution mode.
        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let config = ProjectConfig::parse(
            &fs_root,
            abs("/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/dir/index.ts"), "export {};\n");

        for (mode, word) in [
            (ResolutionMode::Import, "CJS"),
            (ResolutionMode::Require, "CJS"),
        ] {
            let mut cache = ResolutionCache::new();
            let mut log = ResolutionTraceLog::default();
            resolve_module_name_with_trace(
                &fs_root,
                &options,
                abs("/main.ts"),
                "./dir/index.ts",
                (
                    ModuleResolutionKind::Bundler,
                    mode,
                    ResolutionFlavor::Runtime,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .expect("relative resolution");
            let expected = format!(
                "Resolving in {word} mode with conditions '{}', 'types'.",
                mode.as_str()
            );
            assert!(
                log.lines().iter().any(|line| line == &expected),
                "missing `{expected}` in {:?}",
                log.lines()
            );
        }
    }

    #[test]
    fn trace_types_flavor_narrates_declaration_candidates_first() {
        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let config = ProjectConfig::parse(
            &fs_root,
            abs("/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/dir/index.d.ts"), "export {};\n");
        host.file(abs("/dir/index.ts"), "export {};\n");

        for (flavor, chosen, narrated) in [
            (ResolutionFlavor::Runtime, "index.ts", "dir/index.ts"),
            (ResolutionFlavor::Types, "index.d.ts", "dir/index.d.ts"),
        ] {
            let mut cache = ResolutionCache::new();
            let mut log = ResolutionTraceLog::default();
            let resolved = resolve_module_name_with_trace(
                &fs_root,
                &options,
                abs("/main.ts"),
                "./dir/index",
                (
                    ModuleResolutionKind::Bundler,
                    ResolutionMode::Import,
                    flavor,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .expect("resolution");
            assert_eq!(resolved.path(), abs(&format!("/dir/{chosen}")).as_path());
            // Narration stops at the first probed candidate, so the single
            // narrated file must be the one the resolver actually chose.
            let narrated_files: Vec<String> = log
                .lines()
                .iter()
                .filter(|line| line.starts_with("File '"))
                .cloned()
                .collect();
            let expected = format!(
                "File '{}/{narrated}' exists - use it as a name resolution result.",
                trace_drive()
            );
            assert_eq!(narrated_files, vec![expected]);
        }
    }

    #[test]
    fn cache_keys_distinguish_runtime_and_types_flavors() {
        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let mut host = MemoryHost::default();
        host.file(abs("/dir/index.d.ts"), "export {};\n");
        host.file(abs("/dir/index.ts"), "export {};\n");
        let options = options_with_resolution("bundler");
        let mut cache = ResolutionCache::new();
        let runtime = resolve_module_name(
            &fs_root,
            &options,
            abs("/main.ts"),
            "./dir/index",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("runtime flavor");
        let types = resolve_type_reference(
            &fs_root,
            &options,
            abs("/main.ts"),
            "./dir/index",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("types flavor");
        assert_eq!(runtime.path(), abs("/dir/index.ts").as_path());
        assert_eq!(types.path(), abs("/dir/index.d.ts").as_path());
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn json_specifier_resolves_the_exact_file_when_resolve_json_module_is_on() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/data.json"), "{\n  \"a\": 1\n}\n");
        // A script module beside the JSON file must not win: a `.json`
        // specifier is planned as an exact file with no extension
        // substitution.
        host.file(abs("/workspace/src/data.ts"), "export const a = 1;\n");
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler","resolveJsonModule":true}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./data.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("exact JSON module");
        assert_eq!(resolved.path(), abs("/workspace/src/data.json").as_path());
        assert!(
            resolved.trace().steps().iter().all(|step| !matches!(
                step,
                ResolutionTraceStep::Candidate { path, .. }
                    if path.extension().is_some_and(|ext| ext != "json"),
            )),
            "no non-JSON candidate may be probed"
        );
    }

    #[test]
    fn json_specifier_probes_the_exact_file_even_when_resolve_json_module_is_off() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/data.json"), "{\n  \"a\": 1\n}\n");
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut cache = ResolutionCache::new();
        // Upstream resolves a relative exact `.json` import even without
        // `resolveJsonModule` (requireOfJsonFileWithoutResolveJsonModule,
        // importAssertionsDeprecated): the flag only decides whether `.json`
        // joins the *searched* extension list.
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./data.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("exact JSON module resolves without the flag");
        assert_eq!(resolved.path(), abs("/workspace/src/data.json").as_path());

        // A `.json` specifier that names no file fails as a plain cannot-find
        // miss (upstream TS2732) — never as an unsupported-extension
        // rejection.
        let error = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./missing.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect_err("missing JSON module cannot resolve");
        assert!(matches!(error, ResolutionError::NotFound { .. }));
    }

    #[test]
    fn json_specifier_with_paths_mapping_resolves_through_the_mapping() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/config/pkg.json"),
            "{\n  \"name\": \"pkg\"\n}\n",
        );
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler","baseUrl":".","paths":{"@config/*":["config/*"]},"resolveJsonModule":true}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "@config/pkg.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("paths-mapped JSON module");
        assert_eq!(resolved.path(), abs("/workspace/config/pkg.json").as_path());

        // The searched routes stay flag-gated: with `resolveJsonModule`
        // disabled a paths-mapped `.json` cannot be found with the current
        // settings (upstream TS2732 on
        // requireOfJsonFileWithoutResolveJsonModuleAndPathMapping), even
        // though the mapped target file exists.
        let without_flag = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler","baseUrl":".","paths":{"@config/*":["config/*"]}}}"#,
        )
        .expect("config");
        // A fresh cache: the flag-on probe above stored its hit under the
        // same (directory, specifier) key.
        let mut fresh = ResolutionCache::new();
        let error = resolve_module_name(
            &root(),
            without_flag.options(),
            abs("/workspace/src/main.ts"),
            "@config/pkg.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut fresh,
        )
        .expect_err("flag-off paths JSON cannot resolve");
        assert!(matches!(error, ResolutionError::NotFound { .. }));
    }
