//! Filesystem-free classic-script compilation.

use std::sync::Arc;

use bamts_bytecode::{
    Constant, ConstantId, EcmaString, ModuleId, Program, ProgramModule, ProgramVerifyError,
    Verified,
};

use crate::{
    diagnostic::DiagnosticSeverity,
    enum_plan::EnumFacts,
    lower::{self, LowerError, LowerErrorKind, LowerOptions},
    namespace_plan::NamespaceFacts,
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText, Utf16Pos},
};

const DEFAULT_MODULE_NAME: &str = "evalmachine.<anonymous>";

/// The closed set of classic-script compilation failures, in compiler terms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScriptCompileError {
    /// The source contained an unpaired UTF-16 surrogate at this code-unit offset.
    IllFormedSource { unit_offset: usize },
    /// Parsing or lowering found invalid JavaScript syntax.
    Syntax {
        message: String,
        line: u32,
        column: u32,
    },
    /// The source used syntax outside the supported classic-script profile.
    Unsupported {
        message: String,
        line: u32,
        column: u32,
    },
    /// A fixed compiler or bytecode capacity was exhausted.
    Capacity { message: String },
}

/// Compiles exact UTF-16 source into a one-module verified classic-script program.
///
/// This entrypoint performs no filesystem access, project resolution, type checking,
/// or lossy UTF-16 conversion.
pub fn compile_classic_script(
    source: &[u16],
    resource_name: &str,
) -> Result<Program<Verified>, ScriptCompileError> {
    let text = EcmaString::from_units(source)
        .to_utf8_strict()
        .map_err(|error| ScriptCompileError::IllFormedSource {
            unit_offset: error.unit_offset,
        })?;
    let source = Arc::new(
        SourceText::new(text).map_err(|error| ScriptCompileError::Capacity {
            message: error.to_string(),
        })?,
    );
    let parsed = parser::parse(scanner::scan(
        SourceId::new(0),
        ScriptKind::JavaScript,
        Arc::clone(&source),
    ));
    if let Some(diagnostic) = parsed
        .diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
    {
        let (line, column) = line_column(&source, diagnostic.range().start());
        return Err(ScriptCompileError::Syntax {
            message: diagnostic.message().to_owned(),
            line,
            column,
        });
    }

    let module_name = normalized_module_name(resource_name).unwrap_or(DEFAULT_MODULE_NAME);
    let options = LowerOptions {
        javascript_compatibility: true,
        ..LowerOptions::default()
    };
    let enum_facts = EnumFacts::unchecked();
    let namespace_facts = NamespaceFacts::unchecked();
    let assembled = lower::assemble_classic_script_named(
        parsed.product(),
        options,
        module_name,
        &enum_facts,
        &namespace_facts,
    )
    .map_err(|error| map_lower_error(&source, error))?;
    let encoded_name = EcmaString::encode(module_name);
    let name = assembled
        .constants()
        .iter()
        .position(|constant| matches!(constant, Constant::String(value) if value == &encoded_name))
        .and_then(|index| u32::try_from(index).ok())
        .map(ConstantId::new)
        .ok_or_else(|| ScriptCompileError::Capacity {
            message: "classic-script module name is absent from the constant pool".to_owned(),
        })?;
    let module = assembled
        .verify()
        .map_err(|error| ScriptCompileError::Capacity {
            message: error.to_string(),
        })?;

    Program::link(
        vec![ProgramModule {
            name,
            code: module,
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        }],
        ModuleId::new(0),
    )
    .map_err(map_program_error)
}

fn map_lower_error(source: &SourceText, error: LowerError) -> ScriptCompileError {
    let (line, column) = line_column(source, error.range.start());
    match error.kind {
        LowerErrorKind::Unsupported(construct) => ScriptCompileError::Unsupported {
            message: construct.to_string(),
            line,
            column,
        },
        LowerErrorKind::Capacity(limit) => ScriptCompileError::Capacity {
            message: limit.to_string(),
        },
        kind => ScriptCompileError::Syntax {
            message: kind.to_string(),
            line,
            column,
        },
    }
}

fn map_program_error(error: ProgramVerifyError) -> ScriptCompileError {
    ScriptCompileError::Capacity {
        message: error.to_string(),
    }
}

fn line_column(source: &SourceText, position: Utf16Pos) -> (u32, u32) {
    source
        .line_column(position)
        .map(|(line, column)| {
            (
                u32::try_from(line).unwrap_or(u32::MAX),
                u32::try_from(column).unwrap_or(u32::MAX),
            )
        })
        .unwrap_or((0, 0))
}

fn normalized_module_name(resource_name: &str) -> Option<&str> {
    if resource_name.is_empty()
        || resource_name.starts_with('/')
        || resource_name.contains('\\')
        || resource_name.contains('\0')
    {
        return None;
    }
    let mut segments = resource_name.split('/');
    let first = segments.next()?;
    if first.contains(':') || first.is_empty() || first == "." || first == ".." {
        return None;
    }
    if segments.any(|segment| segment.is_empty() || segment == "." || segment == "..") {
        return None;
    }
    Some(resource_name)
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::{Constant, Instruction, Verified};

    use super::{ScriptCompileError, compile_classic_script};

    #[test]
    fn classic_script_has_a_single_linkage_free_module() {
        let program = compile_classic_script(
            "1 + 1".encode_utf16().collect::<Vec<_>>().as_slice(),
            "script.js",
        )
        .expect("classic script compiles");

        assert_classic_script_is_linkage_free(&program);
    }

    #[test]
    fn classic_script_dynamic_import_lowers_without_static_linkage() {
        let program = compile_classic_script(
            "import(specifier)"
                .encode_utf16()
                .collect::<Vec<_>>()
                .as_slice(),
            "script.js",
        )
        .expect("classic script dynamic import compiles");

        assert_classic_script_is_linkage_free(&program);
        assert!(
            program.modules()[0]
                .code()
                .functions()
                .iter()
                .flat_map(|function| function.code())
                .any(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
        );
    }

    fn assert_classic_script_is_linkage_free(program: &bamts_bytecode::Program<Verified>) {
        assert_eq!(program.entry().get(), 0);
        assert_eq!(program.modules().len(), 1);
        let module = &program.modules()[0];
        assert!(module.edges().is_empty());
        assert!(module.bindings().is_empty());
        assert!(module.exports().is_empty());
        assert!(matches!(
            module.code().functions()[module.code().entry().get() as usize]
                .code()
                .last(),
            Some(Instruction::Return { .. })
        ));
        assert!(
            module
                .code()
                .functions()
                .iter()
                .flat_map(|function| function.code())
                .all(|instruction| !matches!(
                    instruction,
                    Instruction::Import { .. } | Instruction::Export { .. }
                ))
        );
        assert!(matches!(
            &module.code().constants()[module.name().get() as usize],
            Constant::String(name)
                if name.to_utf8_strict().is_ok_and(|name| name == "script.js")
        ));
    }

    #[test]
    fn classic_script_rejects_module_syntax_before_program_linking() {
        for (source, expected) in [
            (
                "import x from 'y'",
                "`import` declaration in a classic script",
            ),
            (
                "export const a = 1",
                "`export` declaration in a classic script",
            ),
            (
                "export default 1",
                "`export` declaration in a classic script",
            ),
            ("return 1", "return statement outside of a function"),
            ("import.meta", "`import.meta` in a classic script"),
        ] {
            let result =
                compile_classic_script(&source.encode_utf16().collect::<Vec<_>>(), "script.js");
            assert!(
                matches!(
                    result,
                    Err(ScriptCompileError::Syntax { ref message, .. }) if message == expected
                ),
                "{source:?} should be a syntax error in a classic script: {result:?}"
            );
        }
    }

    #[test]
    fn ill_formed_utf16_source_is_typed() {
        assert_eq!(
            compile_classic_script(&[0xD800], "script.js"),
            Err(ScriptCompileError::IllFormedSource { unit_offset: 0 })
        );
    }

    #[test]
    fn syntax_diagnostics_are_typed() {
        assert!(matches!(
            compile_classic_script(&"(".encode_utf16().collect::<Vec<_>>(), "script.js"),
            Err(ScriptCompileError::Syntax { .. })
        ));
    }

    #[test]
    fn non_normalized_resource_name_is_advisory() {
        assert!(compile_classic_script(&[], "/tmp/script.js").is_ok());
    }

    #[test]
    fn completion_cases_compile_to_verified_returning_scripts() {
        for source in [
            "",
            "var x = 5",
            "1 + 1",
            "if (true) { 42 }",
            "1; if (true) {}",
            "{ 7 }",
            "for (let i = 0; i < 3; i++) { i }",
            "1; while (false) { 2 }",
            "try { 1 } finally { 2 }",
            "switch (1) { case 1: 5 }",
            "function f() {}",
        ] {
            let program =
                compile_classic_script(&source.encode_utf16().collect::<Vec<_>>(), "script.js")
                    .unwrap_or_else(|error| panic!("{source:?} did not compile: {error:?}"));
            let entry = &program.modules()[0].code().functions()[0];
            assert!(matches!(
                entry.code().last(),
                Some(Instruction::Return { .. })
            ));
        }
    }
}
