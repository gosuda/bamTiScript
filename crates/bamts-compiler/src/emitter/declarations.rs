//! `.d.ts` emit through the existing declaration printer.
//!
//! The JavaScript printer already has a [`super::Surface::Declaration`] path.
//! This module is the declaration-emit policy layer in front of that path: it
//! rewrites the tree so parameter properties become class fields, private
//! members print without types, and isolated-declaration errors are reported for
//! exported values that would otherwise require the checker to invent a type.
//!
//! # Guarantees
//! * **One printer.** Lowered trees are handed to [`super::print`]; this module
//!   never prints syntax itself.
//! * **Source order.** Members and statements keep the order they had in the
//!   source, with lifted parameter properties inserted immediately before the
//!   constructor that declared them.
//! * **Deterministic.** Identical input and [`DeclarationOptions`] produce
//!   byte-identical `.d.ts` text and diagnostic vectors.
//! * **Negative paths.** An exported function, method, or variable that lacks a
//!   portable type under isolated declarations yields a typed [`Diagnostic`]
//!   rather than an implicit `any`.

use crate::checker::SemanticModel;
use crate::diagnostic::Diagnostic;
use crate::syntax::{
    Accessibility, BindingPattern, ClassDeclaration, ClassMember, ClassMemberNode, ClassProperty,
    ConstructorDeclaration, DeclarationModifiers, ExportDeclaration, ExportDefaultValue,
    ExportNamedDeclaration, FunctionLike, Node, NodeId, Parameter, ParameterModifiers,
    PropertyName, SourceFile, Statement, Stmt, VariableDeclaration,
};

use super::{EmitFileNames, EmitOutput, Newline, PrintOptions, ScriptTarget, Surface, print};

/// Stable diagnostic identifiers produced by declaration emit.
pub mod codes {
    use crate::diagnostic::DiagnosticCode;

    /// An exported function or method has no return type annotation.
    pub const MISSING_RETURN_TYPE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1201");
    /// An exported variable has no type annotation and no portable initializer.
    pub const MISSING_VARIABLE_TYPE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1202");
    /// A parameter property is bound to a pattern, which cannot be lifted.
    pub const PARAMETER_PROPERTY_PATTERN: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1203");
}

/// Immutable declaration-emit options.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DeclarationOptions {
    /// Structural newline sequence forwarded to the printer.
    pub newline: Newline,
    /// Spaces per indent level forwarded to the printer.
    pub indent_width: u8,
    /// Target the declaration text must run on.
    pub target: ScriptTarget,
    /// When true, exported values without portable types are errors.
    pub isolated_declarations: bool,
    /// When true, emit a source map for the declaration file.
    pub declaration_map: bool,
}

impl Default for DeclarationOptions {
    fn default() -> Self {
        Self {
            newline: Newline::Lf,
            indent_width: 4,
            target: ScriptTarget::EsNext,
            isolated_declarations: false,
            declaration_map: false,
        }
    }
}

impl DeclarationOptions {
    /// Isolated-declaration checking.
    #[must_use]
    pub const fn isolated() -> Self {
        Self {
            newline: Newline::Lf,
            indent_width: 4,
            target: ScriptTarget::EsNext,
            isolated_declarations: true,
            declaration_map: false,
        }
    }
}

/// Prints `file` as a `.d.ts` after applying declaration policy rewrites.
#[must_use]
pub fn emit_declarations(
    file: &SourceFile,
    model: &SemanticModel,
    options: DeclarationOptions,
    names: &EmitFileNames,
) -> EmitOutput {
    let mut diagnostics = Vec::new();
    if options.isolated_declarations {
        collect_isolated_errors(file, &mut diagnostics);
    }
    let rewritten = rewrite_file(file, &mut diagnostics);
    let mut output = print(
        &rewritten,
        model,
        PrintOptions {
            newline: options.newline,
            indent_width: options.indent_width,
            target: options.target,
            source_map: options.declaration_map,
            inline_source_map: false,
            inline_sources: false,
            remove_comments: false,
            module_marker: false,
            verbatim_module_syntax: false,
        },
        names,
        Surface::Declaration,
        None,
    );
    output.diagnostics.append(&mut diagnostics);
    output.diagnostics.sort();
    output.diagnostics.dedup();
    output
}

fn rewrite_file(file: &SourceFile, diagnostics: &mut Vec<Diagnostic>) -> SourceFile {
    let statements = rewrite_statements(file.statements(), diagnostics);
    SourceFile::new(
        file.id(),
        file.source_id(),
        file.script_kind(),
        file.range(),
        std::sync::Arc::new(file.source_text().clone()),
        file.tokens().to_vec(),
        statements,
        *file.eof(),
        file.diagnostics().to_vec(),
    )
}

fn rewrite_statements(statements: &[Stmt], diagnostics: &mut Vec<Diagnostic>) -> Vec<Stmt> {
    statements
        .iter()
        .map(|statement| rewrite_statement(statement, diagnostics))
        .collect()
}

fn rewrite_statement(statement: &Stmt, diagnostics: &mut Vec<Diagnostic>) -> Stmt {
    match statement.data() {
        Statement::Class(class) => Node::new(
            statement.id(),
            statement.range(),
            Statement::Class(rewrite_class(class, diagnostics)),
        ),
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) => {
            let inner = rewrite_statement(inner, diagnostics);
            Node::new(
                statement.id(),
                statement.range(),
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(Box::new(inner)),
                )),
            )
        }
        Statement::Export(ExportDeclaration::Default(default)) => {
            let value = match &default.value {
                ExportDefaultValue::Class(class) => {
                    ExportDefaultValue::Class(rewrite_class(class, diagnostics))
                }
                other => other.clone(),
            };
            Node::new(
                statement.id(),
                statement.range(),
                Statement::Export(ExportDeclaration::Default(
                    crate::syntax::ExportDefaultDeclaration { value },
                )),
            )
        }
        Statement::Declare(inner) => Node::new(
            statement.id(),
            statement.range(),
            Statement::Declare(Box::new(rewrite_statement(inner, diagnostics))),
        ),
        _ => statement.clone(),
    }
}

fn rewrite_class(class: &ClassDeclaration, diagnostics: &mut Vec<Diagnostic>) -> ClassDeclaration {
    let mut members = Vec::new();
    for member in &class.members {
        match member.data() {
            ClassMember::Constructor(constructor) => {
                let (properties, constructor) =
                    lift_parameter_properties(member.id(), constructor, diagnostics);
                members.extend(properties);
                members.push(Node::new(
                    member.id(),
                    member.range(),
                    ClassMember::Constructor(constructor),
                ));
            }
            _ => members.push(member.clone()),
        }
    }
    ClassDeclaration {
        members,
        ..class.clone()
    }
}

fn lift_parameter_properties(
    constructor_id: NodeId,
    constructor: &ConstructorDeclaration,
    diagnostics: &mut Vec<Diagnostic>,
) -> (Vec<ClassMemberNode>, ConstructorDeclaration) {
    let mut properties = Vec::new();
    let mut parameters = Vec::new();
    for (index, parameter) in constructor.parameters.iter().enumerate() {
        let data = parameter.data();
        if !super::is_parameter_property(data) {
            parameters.push(parameter.clone());
            continue;
        }
        match data.binding.data() {
            BindingPattern::Identifier(ident) => {
                properties.push(Node::new(
                    NodeId::new(constructor_id.get().saturating_add(1000 + index as u32)),
                    parameter.range(),
                    ClassMember::Property(ClassProperty {
                        decorators: data.decorators.clone(),
                        modifiers: DeclarationModifiers {
                            accessibility: data.modifiers.accessibility,
                            is_abstract: false,
                            is_declare: false,
                            is_override: data.modifiers.is_override,
                            is_readonly: data.modifiers.is_readonly,
                            is_static: false,
                        },
                        name: PropertyName::Identifier(ident.clone()),
                        optional: data.optional,
                        definite: false,
                        type_annotation: data.type_annotation.clone(),
                        initializer: None,
                    }),
                ));
                parameters.push(Node::new(
                    parameter.id(),
                    parameter.range(),
                    Parameter {
                        modifiers: ParameterModifiers::default(),
                        ..data.clone()
                    },
                ));
            }
            _ => {
                diagnostics.push(Diagnostic::error(
                    codes::PARAMETER_PROPERTY_PATTERN,
                    // Filled below; the caller has the file identity. Use a
                    // placeholder that print() will not duplicate: the rewrite
                    // still keeps the original parameter so the printer can
                    // recover, and this diagnostic is attached with a dummy
                    // source until `attach_source` rewrites it.
                    crate::source::SourceId::new(0),
                    parameter.range(),
                    "parameter property must bind an identifier",
                ));
                parameters.push(parameter.clone());
            }
        }
    }
    (
        properties,
        ConstructorDeclaration {
            parameters,
            ..constructor.clone()
        },
    )
}

fn collect_isolated_errors(file: &SourceFile, diagnostics: &mut Vec<Diagnostic>) {
    for statement in file.statements() {
        collect_statement(file, statement, false, diagnostics);
    }
}

fn collect_statement(
    file: &SourceFile,
    statement: &Stmt,
    exported: bool,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match statement.data() {
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) => {
            collect_statement(file, inner, true, diagnostics);
        }
        Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
            ExportDefaultValue::Function(function) => {
                check_function(file, statement, function, diagnostics);
            }
            ExportDefaultValue::Class(class) => check_class(file, class, diagnostics),
            _ => {}
        },
        Statement::Function(function) if exported => {
            check_function(file, statement, &function.function, diagnostics);
        }
        Statement::Variable(declaration) if exported => {
            check_variable(file, declaration, diagnostics);
        }
        Statement::Class(class) if exported => check_class(file, class, diagnostics),
        Statement::Declare(inner) => collect_statement(file, inner, exported, diagnostics),
        _ => {}
    }
}

fn check_function(
    file: &SourceFile,
    statement: &Stmt,
    function: &FunctionLike,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if function.return_type.is_none() {
        diagnostics.push(Diagnostic::error(
            codes::MISSING_RETURN_TYPE,
            file.source_id(),
            statement.range(),
            "exported function must have an explicit return type",
        ));
    }
}

fn check_variable(
    file: &SourceFile,
    declaration: &VariableDeclaration,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for declarator in &declaration.declarations {
        let data = declarator.data();
        if data.type_annotation.is_some() {
            continue;
        }
        let portable = data
            .initializer
            .as_ref()
            .is_some_and(|expression| is_portable_initializer(expression.data()));
        if !portable {
            diagnostics.push(Diagnostic::error(
                codes::MISSING_VARIABLE_TYPE,
                file.source_id(),
                declarator.range(),
                "exported variable must have an explicit type annotation",
            ));
        }
    }
}

fn check_class(file: &SourceFile, class: &ClassDeclaration, diagnostics: &mut Vec<Diagnostic>) {
    for member in &class.members {
        if let ClassMember::Method(method) = member.data()
            && method.modifiers.accessibility != Some(Accessibility::Private)
            && method.function.return_type.is_none()
            && method.modifier == crate::syntax::PropertyModifier::None
        {
            diagnostics.push(Diagnostic::error(
                codes::MISSING_RETURN_TYPE,
                file.source_id(),
                member.range(),
                "exported function must have an explicit return type",
            ));
        }
    }
}

fn is_portable_initializer(expression: &crate::syntax::Expression) -> bool {
    matches!(
        expression,
        crate::syntax::Expression::Literal(_)
            | crate::syntax::Expression::As(_)
            | crate::syntax::Expression::Satisfies(_)
            | crate::syntax::Expression::TypeAssertion(_)
    )
}

#[cfg(test)]
mod tests {
    use super::{DeclarationOptions, codes, emit_declarations};
    use crate::checker;
    use crate::parser;
    use crate::scanner;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use std::sync::Arc;

    fn parse(source: &str) -> crate::diagnostic::Recovered<crate::syntax::SourceFile> {
        parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("static test source fits size limit")),
        ))
    }

    fn emit_dts(source: &str, options: DeclarationOptions) -> crate::emitter::EmitOutput {
        let parsed = parse(source);
        let model = checker::check(&parsed).into_product();
        emit_declarations(
            parsed.product(),
            &model,
            options,
            &crate::emitter::EmitFileNames::default(),
        )
    }

    #[test]
    fn function_bodies_are_elided_and_declare_is_prefixed() {
        let output = emit_dts(
            "export function f(x: number): number { return x; }\n",
            DeclarationOptions::default(),
        );
        assert!(!output.has_errors());
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export declare function f(x: number): number;\n"
        );
    }

    #[test]
    fn public_accessibility_is_omitted_in_declarations_like_class_constructor_accessibility() {
        let output = emit_dts(
            "export class C {\n\
             \x20   public p: number;\n\
             \x20   public static s: number;\n\
             \x20   public m(): void {}\n\
             \x20   protected q: number;\n\
             \x20   constructor(public x: number, protected y: number) {}\n\
             }\n",
            DeclarationOptions::default(),
        );
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export declare class C {\n    p: number;\n    static s: number;\n    m(): void;\n    protected q: number;\n    x: number;\n    protected y: number;\n    constructor(x: number, y: number);\n}\n"
        );
    }

    #[test]
    fn private_members_print_without_types_like_comments_class_members() {
        let output = emit_dts(
            "export class C {\n\
             \x20   #hidden: string;\n\
             \x20   private p: number;\n\
             \x20   private static x: number;\n\
             \x20   private readonly a1: string;\n\
             \x20   private m(): void {}\n\
             \x20   private get g(): number { return 1; }\n\
             \x20   private set g(v: number) {}\n\
             \x20   private accessor acc: number;\n\
             \x20   visible: string;\n\
             }\n",
            DeclarationOptions::default(),
        );
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export declare class C {\n    #private;\n    private p;\n    private static x;\n    private readonly a1;\n    private m;\n    private get g();\n    private set g(value);\n    private accessor acc;\n    visible: string;\n}\n"
        );
    }

    #[test]
    fn overloaded_private_methods_print_one_bare_member_like_decl_file_for_class_with_private_overloaded_function()
     {
        let output = emit_dts(
            "export class O {\n\
             \x20   private foo(): void;\n\
             \x20   private foo(x: string): void;\n\
             \x20   private foo(x?: string): void {}\n\
             }\n",
            DeclarationOptions::default(),
        );
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export declare class O {\n    private foo;\n}\n"
        );
    }

    #[test]
    fn parameter_properties_are_lifted_before_the_constructor() {
        let output = emit_dts(
            "export class C { constructor(public x: number) {} }\n",
            DeclarationOptions::default(),
        );
        assert!(!output.has_errors(), "{:?}", output.diagnostics);
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export declare class C {\n    x: number;\n    constructor(x: number);\n}\n"
        );
    }

    #[test]
    fn isolated_declarations_require_exported_return_types() {
        let output = emit_dts(
            "export function f(x: number) { return x; }\n",
            DeclarationOptions::isolated(),
        );
        assert!(output.has_errors());
        assert_eq!(output.diagnostics[0].code(), codes::MISSING_RETURN_TYPE);
    }

    #[test]
    fn isolated_declarations_require_exported_variable_types() {
        let output = emit_dts(
            "export const f = () => 1;\n",
            DeclarationOptions::isolated(),
        );
        assert!(output.has_errors());
        assert_eq!(output.diagnostics[0].code(), codes::MISSING_VARIABLE_TYPE);
    }

    #[test]
    fn isolated_declarations_accept_literal_initializers() {
        let output = emit_dts("export const n = 1;\n", DeclarationOptions::isolated());
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::MISSING_VARIABLE_TYPE),
            "{:?}",
            output.diagnostics
        );
    }
    #[test]
    fn isolated_declarations_ignore_unexported_implementation_details() {
        let output = emit_dts(
            "const local = factory(); export const n: number = 1;\n",
            DeclarationOptions::isolated(),
        );
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::MISSING_VARIABLE_TYPE),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn parameter_property_patterns_are_errors() {
        let output = emit_dts(
            "export class C { constructor(public [x]: number[]) {} }\n",
            DeclarationOptions::default(),
        );
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::PARAMETER_PROPERTY_PATTERN),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn declaration_emit_is_deterministic() {
        let source =
            "export class C { constructor(readonly y: string) { this.y = y; } z(): void {} }\n";
        let left = emit_dts(source, DeclarationOptions::default());
        let right = emit_dts(source, DeclarationOptions::default());
        assert_eq!(left, right);
    }

    #[test]
    fn interfaces_and_type_aliases_are_preserved() {
        let output = emit_dts(
            "export interface I { x: number; }\nexport type T = I;\n",
            DeclarationOptions::default(),
        );
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export interface I {\n    x: number;\n}\nexport type T = I;\n"
        );
    }

    #[test]
    fn const_literal_type_is_inferred() {
        let output = emit_dts(
            "export const n = 42;\nexport const s = \"hello\";\nexport const b = true;\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare const n: 42;"),
            "expected literal type for const n, got: {code}"
        );
        assert!(
            code.contains("export declare const s: \"hello\";"),
            "expected literal type for const s, got: {code}"
        );
        assert!(
            code.contains("export declare const b: true;"),
            "expected literal type for const b, got: {code}"
        );
    }

    #[test]
    fn let_literal_type_is_widened() {
        let output = emit_dts(
            "export let n = 42;\nexport let s = \"hello\";\nexport let b = true;\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare let n: number;"),
            "expected widened type for let n, got: {code}"
        );
        assert!(
            code.contains("export declare let s: string;"),
            "expected widened type for let s, got: {code}"
        );
        assert!(
            code.contains("export declare let b: boolean;"),
            "expected widened type for let b, got: {code}"
        );
    }

    #[test]
    fn const_symbol_call_emits_unique_symbol() {
        let output = emit_dts(
            "export const sym = Symbol();\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare const sym: unique symbol;"),
            "expected unique symbol for const Symbol(), got: {code}"
        );
    }

    #[test]
    fn let_symbol_call_emits_symbol() {
        let output = emit_dts(
            "export let sym = Symbol();\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare let sym: symbol;"),
            "expected symbol for let Symbol(), got: {code}"
        );
    }

    #[test]
    fn const_object_literal_type_is_inferred() {
        let output = emit_dts(
            "export const obj = { x: 1, y: \"hello\" };\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare const obj:"),
            "expected type annotation for const obj, got: {code}"
        );
        // tsc widens property types in object literals even for const.
        assert!(
            code.contains("x: number"),
            "expected widened property type x: number, got: {code}"
        );
        assert!(
            code.contains("y: string"),
            "expected widened property type y: string, got: {code}"
        );
    }

    #[test]
    fn const_arrow_function_type_is_inferred() {
        let output = emit_dts(
            "export const fn = (x: number) => x + 1;\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare const fn:"),
            "expected type annotation for const fn, got: {code}"
        );
        assert!(
            code.contains("=>"),
            "expected function type with =>, got: {code}"
        );
    }

    #[test]
    fn jsdoc_comment_is_retained_on_variable() {
        let output = emit_dts(
            "/** This is a JSDoc comment */\nexport const x = 1;\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("/** This is a JSDoc comment */"),
            "expected JSDoc comment retained, got: {code}"
        );
    }

    #[test]
    fn jsdoc_comment_is_retained_on_class_member() {
        let output = emit_dts(
            "/** A class with documented members */\nexport class C {\n    /** @return {number} */\n    method(): number { return 1; }\n}\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("/** A class with documented members */"),
            "expected JSDoc on class, got: {code}"
        );
        assert!(
            code.contains("/** @return {number} */"),
            "expected JSDoc on class member, got: {code}"
        );
    }

    #[test]
    fn jsdoc_comment_is_retained_on_function() {
        let output = emit_dts(
            "/** Adds two numbers */\nexport function add(a: number, b: number): number { return a + b; }\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("/** Adds two numbers */"),
            "expected JSDoc on function, got: {code}"
        );
    }

    #[test]
    fn class_property_inferred_type_from_initializer() {
        let output = emit_dts(
            "export class C { x = 42; }\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("x: 42"),
            "expected inferred literal type for class property, got: {code}"
        );
    }

    /// Object type literals break across lines in `.d.ts` output.
    ///
    /// Authority: `tests/baselines/reference/DeclarationErrorsNoEmitOnError.js:14-21`
    /// ```text
    /// //// [DeclarationErrorsNoEmitOnError.d.ts]
    /// type T = {
    ///     x: number;
    /// };
    /// ```
    #[test]
    fn object_type_literal_breaks_across_lines() {
        let output = emit_dts(
            "type T = { x : number }\nexport interface I { f: T; }\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("type T = {\n    x: number;\n};"),
            "expected multi-line object type, got: {code}"
        );
    }

    /// Mapped types break across lines in `.d.ts` output.
    ///
    /// Authority: `tests/baselines/reference/mappedTypes3.js:8-10`
    /// ```text
    /// type Boxified<T> = {
    ///     [K in keyof T]: Box<T[K]>;
    /// }
    /// ```
    #[test]
    fn mapped_type_breaks_across_lines() {
        let output = emit_dts(
            "class Box<P> { value: P; }\ntype Boxified<T> = { [K in keyof T]: Box<T[K]>; }\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("type Boxified<T> = {\n    [K in keyof T]: Box<T[K]>;\n}"),
            "expected multi-line mapped type, got: {code}"
        );
    }

    /// Constructor type uses arrow form `=> T`, not colon form `: T`.
    ///
    /// Authority: `tests/baselines/reference/exportClassExtendingIntersection.js:72-73`
    /// ```text
    /// export type Constructor<T> = new (...args: any[]) => T;
    /// ```
    #[test]
    fn constructor_type_uses_arrow_form() {
        let output = emit_dts(
            "export type Constructor<T> = new (...args: any[]) => T;\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("new (...args: any[]) => T"),
            "expected arrow form for constructor type, got: {code}"
        );
        assert!(
            !code.contains("new (...args: any[]): T"),
            "expected no colon form for constructor type, got: {code}"
        );
    }

    /// Empty class body emits `{\n}` not `{}`.
    ///
    /// Authority: `tests/baselines/reference/declarationEmitFirstTypeArgumentGenericFunctionType.js:54-56`
    /// ```text
    /// declare class X<A> {
    /// }
    /// ```
    #[test]
    fn empty_class_body_emits_newline() {
        let output = emit_dts("class X<A> {\n}\n", DeclarationOptions::default());
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("declare class X<A> {\n}"),
            "expected empty class body with newline, got: {code}"
        );
        assert!(
            !code.contains("declare class X<A> {}"),
            "expected no inline empty class body, got: {code}"
        );
    }

    /// Synthesized object type from a class expression breaks across lines.
    ///
    /// Authority: `tests/baselines/reference/emitClassExpressionInDeclarationFile.js:69-74`
    /// ```text
    /// export declare var simpleExample: {
    ///     new (): {
    ///         tags(): void;
    ///     };
    ///     getTags(): void;
    /// };
    /// ```
    #[test]
    fn synthesized_object_type_breaks_across_lines() {
        let output = emit_dts(
            "export var simpleExample = class {\n    static getTags() { }\n    tags() { }\n}\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("export declare var simpleExample: {\n"),
            "expected multi-line synthesized object type, got: {code}"
        );
        assert!(
            code.contains("new (): {"),
            "expected nested object type for construct signature return, got: {code}"
        );
    }

    /// Consecutive JSDoc blocks before a declaration are all retained.
    ///
    /// Authority: `tests/baselines/reference/importDeferJsdoc.js:21-28`
    /// ```text
    /// //// [foo.d.ts]
    /// /**
    ///  * @import defer * as ns from "./types"
    ///  */
    /// /**
    ///  * @type { ns.X }
    ///  */
    /// declare let a: ns.X;
    /// ```
    #[test]
    fn consecutive_jsdoc_blocks_are_retained() {
        let output = emit_dts(
            "/**\n * @import defer * as ns from \"./types\"\n */\n\n/**\n * @type { ns.X }\n */\nlet a = 2;\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("@import defer"),
            "expected @import defer JSDoc retained, got: {code}"
        );
        assert!(
            code.contains("@type { ns.X }"),
            "expected @type JSDoc retained, got: {code}"
        );
    }

    /// Functions without explicit return type get inferred `: void` in `.d.ts`.
    ///
    /// Authority: `tests/baselines/reference/mappedTypes3.js:81`
    /// ```text
    /// declare function f1(b: Bacon): void;
    /// ```
    #[test]
    fn inferred_void_return_type_is_emitted() {
        let output = emit_dts(
            "interface Bacon { kind: string; }\nfunction f1(b: Bacon) { }\nexport { f1 };\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("declare function f1(b: Bacon): void;"),
            "expected inferred void return type, got: {code}"
        );
    }

    /// Generic function-type arguments in type arguments are wrapped in
    /// parens to disambiguate `<<T>() => T>` from a misplaced `<<`.
    ///
    /// Authority: `tests/baselines/reference/declarationEmitFirstTypeArgumentGenericFunctionType.js:56`
    /// ```text
    /// declare var prop11: X<(<Tany>() => Tany)>;
    /// ```
    #[test]
    fn generic_function_type_argument_wrapped_in_parens() {
        let output = emit_dts(
            "class X<T> {}\nvar prop11: X<<U>() => U>;\nexport { prop11 };\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("X<(<U>() => U)>"),
            "expected parens around generic function type argument, got: {code}"
        );
    }

    /// Non-generic function-type arguments stay unwrapped.
    ///
    /// Authority: `tests/baselines/reference/declFileForFunctionTypeAsTypeParameter.js`
    /// ```text
    /// declare class C extends X<() => number> {
    /// ```
    #[test]
    fn non_generic_function_type_argument_not_wrapped() {
        let output = emit_dts(
            "class X<T> {}\nclass C extends X<() => number> {}\nexport { C };\n",
            DeclarationOptions::default(),
        );
        let code = &output.declaration.as_ref().unwrap().code;
        assert!(
            code.contains("X<() => number>"),
            "expected no parens around non-generic function type argument, got: {code}"
        );
    }

    /// Rule: a JavaScript source does not get the `declare` prefix on its
    /// exported declarations, while a TypeScript one does.
    ///
    /// Authority: `tests/cases/conformance/jsdoc/callbackOnConstructor.ts`
    /// (allowJs) emits `export class Preferences {`; `tests/cases/compiler/
    /// accessorDeclarationEmitVisibilityErrors.ts` (TypeScript) emits
    /// `export declare class Q {`.
    #[test]
    fn js_source_exported_class_omits_declare_prefix() {
        let source = "export class C {}\n";
        let ts = emit_dts(source, DeclarationOptions::default());
        assert_eq!(
            ts.declaration.as_ref().unwrap().code,
            "export declare class C {\n}\n"
        );
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::JavaScript,
            Arc::new(SourceText::new(source).expect("static test source fits size limit")),
        ));
        let model = checker::check(&parsed).into_product();
        let js = emit_declarations(
            parsed.product(),
            &model,
            DeclarationOptions::default(),
            &crate::emitter::EmitFileNames::default(),
        );
        assert_eq!(
            js.declaration.as_ref().unwrap().code,
            "export class C {\n}\n"
        );
    }

    /// Rule: inside an identifier-named namespace body the `export` keyword is
    /// dropped from member declarations; inside a string-named `module "..."`
    /// body it is kept.
    ///
    /// Authority: `tests/baselines/reference/declFileTypeofInAnonymousType.js`
    /// ```text
    /// declare namespace m1 {
    ///     class c {
    /// ```
    /// and `declarationEmitPrefersPathKindBasedOnBundling2`
    /// ```text
    /// declare module "lib/operators/scalar" {
    ///     export interface Scalar {
    /// ```
    #[test]
    fn namespace_members_drop_export_but_module_bodies_keep_it() {
        let ns = emit_dts(
            "namespace m1 { export class c { } }\n",
            DeclarationOptions::default(),
        );
        let ns_code = &ns.declaration.as_ref().unwrap().code;
        assert!(
            ns_code.contains("declare namespace m1 {"),
            "namespace keeps declare: {ns_code}"
        );
        assert!(
            ns_code.contains("\n    class c {"),
            "member export dropped in namespace: {ns_code}"
        );
        assert!(
            !ns_code.contains("export class"),
            "no member export keyword in namespace: {ns_code}"
        );
        let module = emit_dts(
            "declare module \"m\" { export interface I { } }\n",
            DeclarationOptions::default(),
        );
        let module_code = &module.declaration.as_ref().unwrap().code;
        assert!(
            module_code.contains("export interface I {"),
            "member export kept in module body: {module_code}"
        );
    }

    /// Rule: `export import X = ...` never takes the `declare` prefix, even at
    /// top level, and keeps `export` inside a namespace body.
    ///
    /// Authority: `tests/baselines/reference/declFileForExportedImport.js`
    /// ```text
    /// export import a = require('./declFileForExportedImport_0');
    /// ```
    /// and `aliasInaccessibleModule.js`
    /// ```text
    /// declare namespace M {
    ///     export import X = N;
    /// ```
    #[test]
    fn exported_import_equals_has_no_declare_and_keeps_export_in_namespace() {
        let top = emit_dts(
            "import a = require(\"./m\");\nexport import a2 = require(\"./m\");\n",
            DeclarationOptions::default(),
        );
        let top_code = &top.declaration.as_ref().unwrap().code;
        assert!(
            top_code.contains("export import a2 = require"),
            "export keyword kept on exported import equals: {top_code}"
        );
        let line = top_code
            .lines()
            .find(|line| line.contains("export import a2"))
            .expect("exported import equals line is emitted");
        assert!(
            !line.contains("declare"),
            "no declare prefix on exported import equals: {line}"
        );
        let nested = emit_dts(
            "namespace M { namespace N { } export import X = N; }\n",
            DeclarationOptions::default(),
        );
        let nested_code = &nested.declaration.as_ref().unwrap().code;
        assert!(
            nested_code.contains("export import X = N;"),
            "export import keeps export inside namespace: {nested_code}"
        );
    }

    /// Rule: a non-exported top-level declaration still gets the `declare`
    /// prefix, in both TypeScript and JavaScript sources.
    ///
    /// Authority: `tests/baselines/reference/jsDeclarationsClassStatic2.js`
    /// ```text
    /// declare class Base {
    /// ```
    #[test]
    fn non_exported_top_level_declarations_keep_declare() {
        let output = emit_dts("class A {}\n", DeclarationOptions::default());
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "declare class A {\n}\n"
        );
    }

    /// Rule: an explicit `export declare X` in the source keeps its prefix.
    ///
    /// Authority: `tests/cases/compiler/exportedInterfaceInaccessibleInCallbackInModule.ts`
    /// ```text
    /// export declare class TPromise<V> {
    /// ```
    #[test]
    fn explicit_export_declare_is_preserved() {
        let output = emit_dts(
            "export declare class T { }\n",
            DeclarationOptions::default(),
        );
        assert_eq!(
            output.declaration.as_ref().unwrap().code,
            "export declare class T {\n}\n"
        );
    }
}
