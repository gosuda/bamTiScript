    use super::*;
    use crate::diagnostic::Recovered;
    use crate::source::{ScriptKind, Utf16Pos};
    use std::sync::Arc;

    /// Builds an AST with token ranges that point into a real source string, so
    /// the emitter resolves identifier and literal lexemes exactly as it would
    /// for a parser product.
    struct Builder {
        text: String,
        len: usize,
    }

    impl Builder {
        fn new() -> Self {
            Self {
                text: String::new(),
                len: 0,
            }
        }

        fn range(start: usize, end: usize) -> TextRange {
            TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered range")
        }

        fn token(&mut self, kind: TokenKind, lexeme: &str) -> Token {
            let start = self.len;
            self.text.push_str(lexeme);
            self.len += lexeme.encode_utf16().count();
            Token::new(kind, Self::range(start, self.len))
        }

        fn ident(&mut self, name: &str) -> IdentifierNode {
            let token = self.token(TokenKind::Identifier, name);
            Node::new(NodeId::new(0), token.range(), Identifier::new(token))
        }

        fn ident_expr(&mut self, name: &str) -> Expr {
            let ident = self.ident(name);
            let range = ident.range();
            Node::new(NodeId::new(0), range, Expression::Identifier(ident))
        }

        fn number(&mut self, literal: &str) -> Expr {
            let token = self.token(TokenKind::NumericLiteral, literal);
            let node = Node::new(NodeId::new(0), token.range(), NumericLiteral::new(token));
            let range = node.range();
            Node::new(
                NodeId::new(0),
                range,
                Expression::Literal(Literal::Number(node)),
            )
        }

        fn string(&mut self, literal: &str) -> StringLiteralNode {
            let token = self.token(TokenKind::StringLiteral, literal);
            Node::new(NodeId::new(0), token.range(), StringLiteral::new(token))
        }

        fn finish(self, statements: Vec<Stmt>) -> SourceFile {
            let source =
                Arc::new(SourceText::new(self.text).expect("test source fits the per-file budget"));
            let len = source.len_utf16();
            let full = TextRange::new(Utf16Pos::ZERO, len).expect("range");
            let eof = Token::new(
                TokenKind::EndOfFile,
                TextRange::new(len, len).expect("range"),
            );
            SourceFile::new(
                NodeId::new(0),
                SourceId::new(0),
                ScriptKind::TypeScript,
                full,
                source,
                Vec::new(),
                statements,
                eof,
                Vec::new(),
            )
        }
    }

    fn dummy() -> TextRange {
        TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("range")
    }

    fn expr(data: Expression) -> Expr {
        Node::new(NodeId::new(0), dummy(), data)
    }

    fn stmt(data: Statement) -> Stmt {
        Node::new(NodeId::new(0), dummy(), data)
    }

    fn expr_stmt(expression: Expr) -> Stmt {
        stmt(Statement::Expression(ExpressionStatement {
            expression: Box::new(expression),
        }))
    }

    fn binary(operator: BinaryOperator, left: Expr, right: Expr) -> Expr {
        expr(Expression::Binary(BinaryExpression {
            operator,
            left: Box::new(left),
            right: Box::new(right),
        }))
    }

    fn emit_output(file: &SourceFile, options: &EmitOptions) -> EmitOutput {
        let checked_file = SourceFile::new(
            file.id(),
            file.source_id(),
            file.script_kind(),
            file.range(),
            Arc::new(
                SourceText::new(file.source_text().as_str())
                    .expect("test source fits the per-file budget"),
            ),
            file.tokens().to_vec(),
            file.statements().to_vec(),
            *file.eof(),
            file.diagnostics().to_vec(),
        );
        let recovered = Recovered::clean(checked_file);
        let checked = crate::checker::check(&recovered);
        emit_checked(file, checked.product(), options, &EmitFileNames::default())
    }

    fn emit_js(file: &SourceFile) -> EmittedFile {
        emit_output(file, &EmitOptions::default())
            .javascript
            .expect("JavaScript output")
    }

    fn emit_declaration(file: &SourceFile) -> EmitOutput {
        let options = EmitOptions {
            declaration: true,
            emit_declaration_only: true,
            ..EmitOptions::default()
        };
        emit_output(file, &options)
    }

    fn javascript(output: &EmitOutput) -> &EmittedFile {
        output.javascript.as_ref().expect("JavaScript output")
    }

    fn declaration(output: &EmitOutput) -> &EmittedFile {
        output.declaration.as_ref().expect("declaration output")
    }

    #[test]
    fn multiplication_binds_tighter_than_addition() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // a + b * c -- no parentheses required.
        let tree = binary(
            BinaryOperator::Add,
            a,
            binary(BinaryOperator::Multiply, bb, c),
        );
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "a + b * c;\n");
    }

    #[test]
    fn lower_precedence_left_operand_is_parenthesized() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a + b) * c -- the additive left operand needs parentheses.
        let tree = binary(
            BinaryOperator::Multiply,
            binary(BinaryOperator::Add, a, bb),
            c,
        );
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(a + b) * c;\n");
    }
    #[test]
    fn tagged_template_spacing_follows_the_unwrapped_tag() {
        fn emit_tagged(input: &str) -> String {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty(), "{input}");
            emit_output(parsed.product(), &EmitOptions::default())
                .javascript
                .expect("JavaScript output")
                .code
                .clone()
        }
        assert_eq!(emit_tagged("tag`x`;\n"), "tag`x`;\n");
        assert_eq!(emit_tagged("getTag()`x`;\n"), "getTag() `x`;\n");
        assert_eq!(emit_tagged("new Tag()`x`;\n"), "new Tag() `x`;\n");
        assert_eq!(emit_tagged("(getTag())`x`;\n"), "(getTag()) `x`;\n");
        assert_eq!(emit_tagged("(tag as any)`x`;\n"), "tag`x`;\n");
    }

    #[test]
    fn exponent_is_right_associative_and_forces_left_grouping() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a ** b) ** c must keep the left grouping; a ** b ** c must not add any.
        let left_grouped = binary(
            BinaryOperator::Exponentiate,
            binary(BinaryOperator::Exponentiate, a, bb),
            c,
        );
        let file = b.finish(vec![expr_stmt(left_grouped)]);
        assert_eq!(emit_js(&file).code, "(a ** b) ** c;\n");
    }

    #[test]
    fn unary_left_of_exponent_is_parenthesized() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let neg = expr(Expression::Unary(UnaryExpression {
            operator: UnaryOperator::Minus,
            argument: Box::new(a),
        }));
        let tree = binary(BinaryOperator::Exponentiate, neg, bb);
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(-a) ** b;\n");
    }

    #[test]
    fn nullish_and_logical_or_require_parentheses_when_mixed() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a || b) ?? c -- mixing ?? with || is a syntax error without parens.
        let or = expr(Expression::Logical(LogicalExpression {
            operator: LogicalOperator::Or,
            left: Box::new(a),
            right: Box::new(bb),
        }));
        let tree = expr(Expression::Logical(LogicalExpression {
            operator: LogicalOperator::Nullish,
            left: Box::new(or),
            right: Box::new(c),
        }));
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(a || b) ?? c;\n");
    }

    #[test]
    fn object_literal_expression_statement_is_parenthesized() {
        let b = Builder::new();
        let object = expr(Expression::Object(ObjectLiteral {
            members: Vec::new(),
        }));
        let file = b.finish(vec![expr_stmt(object)]);
        assert_eq!(emit_js(&file).code, "({});\n");
    }

    #[test]
    fn arrow_object_body_is_parenthesized() {
        let b = Builder::new();
        let object = expr(Expression::Object(ObjectLiteral {
            members: Vec::new(),
        }));
        let arrow = expr(Expression::Arrow(ArrowFunction {
            is_async: false,
            type_parameters: None,
            parameters: Vec::new(),
            return_type: None,
            body: FunctionBody::Expression(Box::new(object)),
        }));
        let file = b.finish(vec![expr_stmt(arrow)]);
        assert_eq!(emit_js(&file).code, "() => ({});\n");
    }

    #[test]
    fn type_annotation_is_erased_in_javascript() {
        let mut b = Builder::new();
        let name = b.ident("x");
        let init = b.number("1");
        let annotation = Node::new(
            NodeId::new(0),
            dummy(),
            TypeAnnotation {
                type_node: Box::new(Node::new(
                    NodeId::new(0),
                    dummy(),
                    TypeNode::Keyword(KeywordType::Number),
                )),
            },
        );
        let binding = Node::new(
            NodeId::new(0),
            name.range(),
            BindingPattern::Identifier(name),
        );
        let declarator = Node::new(
            NodeId::new(0),
            dummy(),
            VariableDeclarator {
                binding,
                definite: false,
                type_annotation: Some(annotation),
                initializer: Some(Box::new(init)),
            },
        );
        let declaration = stmt(Statement::Variable(VariableDeclaration {
            range: dummy(),
            kind: VariableKind::Let,
            declarations: vec![declarator],
        }));
        let file = b.finish(vec![declaration]);
        assert_eq!(emit_js(&file).code, "let x = 1;\n");
    }

    #[test]
    fn as_expression_is_erased_but_keeps_needed_parentheses() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a + b as T) * c erases to (a + b) * c.
        let as_expr = expr(Expression::As(AsExpression {
            expression: Box::new(binary(BinaryOperator::Add, a, bb)),
            type_node: Some(Box::new(Node::new(
                NodeId::new(0),
                dummy(),
                TypeNode::Keyword(KeywordType::Any),
            ))),
        }));
        let tree = binary(BinaryOperator::Multiply, as_expr, c);
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(a + b) * c;\n");
    }

    #[test]
    fn newline_policy_uses_configured_terminator() {
        let mut b = Builder::new();
        let first = expr_stmt(b.ident_expr("a"));
        let second = expr_stmt(b.ident_expr("b"));
        let file = b.finish(vec![first, second]);
        let options = EmitOptions::default().with_newline(Newline::CrLf);
        let output = emit_output(&file, &options);
        assert_eq!(javascript(&output).code, "a;\r\nb;\r\n");
    }

    #[test]
    fn missing_expression_reports_stable_diagnostic() {
        let b = Builder::new();
        let missing = expr(Expression::Missing(MissingNode::new(
            NodeKind::IdentifierExpression,
        )));
        let file = b.finish(vec![expr_stmt(missing)]);
        let output = emit_output(&file, &EmitOptions::default());
        assert_eq!(javascript(&output).code, "void 0;\n");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].code(), codes::MISSING_EXPRESSION);
        assert!(output.has_errors());
    }

    #[test]
    fn enum_lowers_to_runtime_object_with_reverse_mapping() {
        let mut b = Builder::new();
        let enum_name = b.ident("E");
        let member_a = Node::new(
            NodeId::new(1),
            dummy(),
            EnumMember {
                name: PropertyName::Identifier(b.ident("A")),
                initializer: None,
            },
        );
        let member_b = Node::new(
            NodeId::new(2),
            dummy(),
            EnumMember {
                name: PropertyName::Identifier(b.ident("B")),
                initializer: None,
            },
        );
        let declaration = Node::new(
            NodeId::new(3),
            dummy(),
            Statement::Enum(EnumDeclaration {
                is_const: false,
                name: enum_name,
                members: vec![member_a, member_b],
            }),
        );
        let file = b.finish(vec![declaration]);
        let expected = "var E;\n(function (E) {\n    E[E[\"A\"] = 0] = \"A\";\n    E[E[\"B\"] = 1] = \"B\";\n})(E || (E = {}));\n";
        assert_eq!(emit_js(&file).code, expected);
    }

    #[test]
    fn enum_string_member_has_no_reverse_mapping() {
        let mut b = Builder::new();
        let enum_name = b.ident("E");
        let value = b.string("\"hi\"");
        let member = Node::new(
            NodeId::new(1),
            dummy(),
            EnumMember {
                name: PropertyName::Identifier(b.ident("A")),
                initializer: Some(Box::new(expr(Expression::Literal(Literal::String(value))))),
            },
        );
        let declaration = Node::new(
            NodeId::new(2),
            dummy(),
            Statement::Enum(EnumDeclaration {
                is_const: false,
                name: enum_name,
                members: vec![member],
            }),
        );
        let file = b.finish(vec![declaration]);
        let expected = "var E;\n(function (E) {\n    E[\"A\"] = \"hi\";\n})(E || (E = {}));\n";
        assert_eq!(emit_js(&file).code, expected);
    }

    #[test]
    fn namespace_reports_unlowered_diagnostic_in_javascript() {
        let mut b = Builder::new();
        let name = b.ident("N");
        let body = Node::new(
            NodeId::new(0),
            dummy(),
            Block {
                statements: Vec::new(),
            },
        );
        let declaration = stmt(Statement::Namespace(NamespaceDeclaration {
            name: NamespaceName::Identifier {
                name,
                keyword: NamespaceKeyword::Namespace,
            },
            body,
        }));
        let file = b.finish(vec![declaration]);
        let output = emit_output(&file, &EmitOptions::default());
        assert_eq!(javascript(&output).code, "");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].code(), codes::NAMESPACE_UNLOWERED);
    }

    #[test]
    fn parameter_property_is_lowered_to_constructor_assignment() {
        let mut b = Builder::new();
        let class_name = b.ident("C");
        let param_name = b.ident("x");
        let binding = Node::new(
            NodeId::new(0),
            param_name.range(),
            BindingPattern::Identifier(param_name),
        );
        let parameter = Node::new(
            NodeId::new(0),
            dummy(),
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers {
                    accessibility: Some(Accessibility::Private),
                    is_readonly: false,
                    is_override: false,
                },
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        );
        let constructor = Node::new(
            NodeId::new(0),
            dummy(),
            ClassMember::Constructor(ConstructorDeclaration {
                decorators: Vec::new(),
                modifiers: DeclarationModifiers::default(),
                parameters: vec![parameter],
                body: Node::new(
                    NodeId::new(0),
                    dummy(),
                    Block {
                        statements: Vec::new(),
                    },
                ),
            }),
        );
        let class = stmt(Statement::Class(ClassDeclaration {
            decorators: Vec::new(),
            modifiers: DeclarationModifiers::default(),
            name: Some(class_name),
            type_parameters: None,
            extends: None,
            implements: Vec::new(),
            members: vec![constructor],
        }));
        let file = b.finish(vec![class]);
        let expected = "class C {\n    constructor(x) {\n        this.x = x;\n    }\n}\n";
        assert_eq!(emit_js(&file).code, expected);
    }

    #[test]
    fn declaration_mode_prints_type_alias_and_erases_bodies() {
        let mut b = Builder::new();
        let alias_name = b.ident("Id");
        let alias = stmt(Statement::TypeAlias(TypeAliasDeclaration {
            name: alias_name,
            type_parameters: None,
            type_node: Box::new(Node::new(
                NodeId::new(0),
                dummy(),
                TypeNode::Keyword(KeywordType::Number),
            )),
        }));
        let file = b.finish(vec![alias]);
        let output = emit_declaration(&file);
        assert_eq!(declaration(&output).code, "type Id = number;\n");
    }

    #[test]
    fn declaration_mode_emits_function_signature_without_body() {
        let mut b = Builder::new();
        let function_name = b.ident("f");
        let function = stmt(Statement::Function(FunctionDeclaration {
            function: FunctionLike {
                decorators: Vec::new(),
                name: Some(function_name),
                is_async: false,
                is_generator: false,
                type_parameters: None,
                parameters: Vec::new(),
                return_type: Some(Node::new(
                    NodeId::new(0),
                    dummy(),
                    TypeAnnotation {
                        type_node: Box::new(Node::new(
                            NodeId::new(0),
                            dummy(),
                            TypeNode::Keyword(KeywordType::Void),
                        )),
                    },
                )),
                body: None,
            },
        }));
        let file = b.finish(vec![function]);
        let output = emit_declaration(&file);
        assert_eq!(declaration(&output).code, "declare function f(): void;\n");
    }

    #[test]
    fn union_type_parenthesizes_function_members() {
        let mut b = Builder::new();
        let alias_name = b.ident("U");
        let func_type = Node::new(
            NodeId::new(0),
            dummy(),
            TypeNode::Function(FunctionType {
                type_parameters: None,
                parameters: Vec::new(),
                return_type: Box::new(Node::new(
                    NodeId::new(0),
                    dummy(),
                    TypeNode::Keyword(KeywordType::Void),
                )),
                return_type_missing: false,
            }),
        );
        let number = Node::new(
            NodeId::new(0),
            dummy(),
            TypeNode::Keyword(KeywordType::Number),
        );
        let union = Node::new(
            NodeId::new(0),
            dummy(),
            TypeNode::Union(vec![func_type, number]),
        );
        let alias = stmt(Statement::TypeAlias(TypeAliasDeclaration {
            name: alias_name,
            type_parameters: None,
            type_node: Box::new(union),
        }));
        let file = b.finish(vec![alias]);
        let output = emit_declaration(&file);
        assert_eq!(
            declaration(&output).code,
            "type U = (() => void) | number;\n"
        );
    }

    #[test]
    fn optional_call_and_member_chain_round_trips() {
        let mut b = Builder::new();
        let object = b.ident_expr("a");
        let member = expr(Expression::Member(MemberExpression {
            object: Box::new(object),
            property: MemberProperty::Named(b.ident("b")),
            optional: true,
        }));
        let call = expr(Expression::Call(CallExpression {
            callee: Box::new(member),
            optional: true,
            type_arguments: None,
            arguments: Vec::new(),
        }));
        let file = b.finish(vec![expr_stmt(call)]);
        assert_eq!(emit_js(&file).code, "a?.b?.();\n");
    }

    #[test]
    fn conditional_test_lower_precedence_gets_parentheses() {
        let mut b = Builder::new();
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        let d = b.ident_expr("d");
        // (a = b) ? c : d -- assignment test must be parenthesized.
        let assign = expr(Expression::Assignment(AssignmentExpression {
            operator: AssignmentOperator::Assign,
            left: Node::new(
                NodeId::new(0),
                dummy(),
                AssignmentTarget::Identifier(b.ident("a2")),
            ),
            right: Box::new(bb),
        }));
        let conditional = expr(Expression::Conditional(ConditionalExpression {
            test: Box::new(assign),
            consequent: Box::new(c),
            alternate: Box::new(d),
        }));
        let file = b.finish(vec![expr_stmt(conditional)]);
        assert_eq!(emit_js(&file).code, "(a2 = b) ? c : d;\n");
    }

    #[test]
    fn export_type_reexport_with_source_erased_in_js() {
        let mut b = Builder::new();
        let specifier = Node::new(
            NodeId::new(0),
            dummy(),
            ExportSpecifier {
                mode: ExportSpecifierMode::TypeOnly,
                local: ModuleExportName::Identifier(b.ident("A")),
                exported: ModuleExportName::Identifier(b.ident("A")),
            },
        );
        let export_stmt = stmt(Statement::Export(ExportDeclaration::Named(
            ExportNamedDeclaration::Specifiers {
                type_only: false,
                specifiers: vec![specifier],
                source: Some(b.string("\"./mod\"")),
                attributes: None,
            },
        )));
        let file = b.finish(vec![export_stmt]);
        assert_eq!(emit_js(&file).code, "export {};\n");
    }

    #[test]
    fn mixed_type_and_value_reexport_retains_value_exports() {
        let mut b = Builder::new();
        let type_spec = Node::new(
            NodeId::new(0),
            dummy(),
            ExportSpecifier {
                mode: ExportSpecifierMode::TypeOnly,
                local: ModuleExportName::Identifier(b.ident("A")),
                exported: ModuleExportName::Identifier(b.ident("A")),
            },
        );
        let val_spec = Node::new(
            NodeId::new(0),
            dummy(),
            ExportSpecifier {
                mode: ExportSpecifierMode::Value,
                local: ModuleExportName::Identifier(b.ident("B")),
                exported: ModuleExportName::Identifier(b.ident("B")),
            },
        );
        let export_stmt = stmt(Statement::Export(ExportDeclaration::Named(
            ExportNamedDeclaration::Specifiers {
                type_only: false,
                specifiers: vec![type_spec, val_spec],
                source: Some(b.string("\"./mod\"")),
                attributes: None,
            },
        )));
        let file = b.finish(vec![export_stmt]);
        assert_eq!(emit_js(&file).code, "export { B } from \"./mod\";\n");
    }

    #[test]
    fn export_assignment_is_dropped_from_an_es_module() {
        let input = "const answer = 42;
export = answer;";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "const answer = 42;
export {};
"
        );

        let reparsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(javascript(&output).code.as_str())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        assert!(reparsed.diagnostics().is_empty());
    }

    #[test]
    fn export_default_interface_is_erased_in_javascript() {
        let input = "export default interface Foo {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "export {};\n");
    }

    #[test]
    fn array_assignment_rest_and_defaults_emit_as_written() {
        let input = "[a = 1, ...b] = c;\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, input);
    }

    #[test]
    fn a_bare_class_semicolon_survives_javascript_and_not_declarations() {
        // Authority: `classWithSemicolonClassElement1` and `2` keep each `;`.
        let input = "export class C {\n    ;\n    ;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "export class C {\n    ;\n    ;\n}\n"
        );
        let declaration = emit_declaration(parsed.product());
        assert!(!declaration.has_errors());
        assert!(!format!("{declaration:?}").contains(";\\n    ;"));
    }

    #[test]
    fn empty_class_body_expands_in_javascript() {
        // Authority: `exnextmodulekindExportClassNameWithObject(target=es2015)`
        // emits `export class Object {}` as `export class Object {\n}`. The TS
        // emitter always expands class bodies: a strict doc-header-aware
        // census over 3846 single-unit `.ts` baselines finds zero single-line
        // classes in any `.js` output section (every `{}` keeper is an echo,
        // declaration-only, or error artifact).
        let input = "export class Object {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "export class Object {\n}\n");
    }

    #[test]
    fn empty_block_body_emits_spaced_braces_in_javascript() {
        // Authority: `expandoFunctionSymbolProperty.js` emits a tight source
        // `function inner() {}` as `function inner() { }`. The TS emitter
        // normalizes every empty block (function, method, arrow, try, static)
        // to `{ }`: 2011 spaced paren-blocks vs zero true-tight `.js`
        // outputs under the same strict census (every tight keeper is an
        // echo, declaration-only, error, or comment artifact).
        let input = "function foo() {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "function foo() { }\n");
    }

    #[test]
    fn single_line_function_body_stays_single_line_in_javascript() {
        // Authority: 292 true single-line function outputs in the stable
        // baselines (e.g. newOperatorErrorCases.js). A non-empty body
        // authored without a line break keeps `{ stmt; stmt; }`.
        let input = "function f() { return 1; }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "function f() { return 1; }\n");
    }

    #[test]
    fn multi_line_function_body_stays_expanded_in_javascript() {
        let input = "function f() {\n  return 1;\n}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "function f() {\n    return 1;\n}\n"
        );
    }

    #[test]
    fn single_line_arrow_block_body_stays_single_line_in_javascript() {
        // Authority: 3 true single-line arrow-block outputs in the stable baselines.
        let input = "const f = () => { return 1; };";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "const f = () => { return 1; };\n");
    }

    #[test]
    fn single_line_constructor_body_stays_single_line_in_javascript() {
        // The constructor's own body preserves one-line layout while the
        // class body around it still expands.
        let input = "class C { constructor() { this.x = 1; } }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "class C {\n    constructor() { this.x = 1; }\n}\n"
        );
    }

    #[test]
    fn constructor_parameter_property_always_expands_in_javascript() {
        // Parameter-property injections are synthesized at print time, so
        // the body expands even when authored on one line.
        let input = "class C { constructor(public x: number) {} }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "class C {\n    constructor(x) {\n        this.x = x;\n    }\n}\n"
        );
    }

    #[test]
    fn single_line_object_literal_joins_members_in_javascript() {
        let input = "({ a: 1, b: 2 });";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "({ a: 1, b: 2 });\n");
    }

    #[test]
    fn tight_authored_object_literal_gains_uniform_spacing_in_javascript() {
        // Authority: downlevelLetConst15 emits authored `{a: 1}` as `{ a: 1 }`.
        let input = "({a:1});";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "({ a: 1 });\n");
    }

    #[test]
    fn multi_line_object_literal_stays_expanded_in_javascript() {
        let input = "({\n  a: 1\n});";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "({\n    a: 1\n});\n");
    }

    #[test]
    fn anonymous_function_expressions_space_before_parameters() {
        // Authority: 2dArrays (`function (val) { ... }`), FunctionExpression1_es6
        // (`function* () { }`), asyncAwaitIsolatedModules_es2017 (`async function ()`).
        // Named forms bind the space to the name: `function f(v)`, `function* g()`.
        let input = "var a = function(v) { return v; };\nvar b = function*(w) { yield w; };\nvar c = function named(x) { return x; };\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("function (v)"), "{code}");
        assert!(code.contains("function* (w)"), "{code}");
        assert!(code.contains("function named(x)"), "{code}");
    }

    #[test]
    fn empty_function_body_authored_across_lines_keeps_two_lines() {
        // Authority: 285-baseline census — a newline-authored empty body
        // prints `{\n}` (ParameterList6 ctor shape); same-line keeps `{ }`.
        let input = "function f() {\n}\nclass C {\n  constructor() {\n  }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("function f() {\n}\n"), "{code}");
        assert!(code.contains("constructor() {\n    }"), "{code}");
    }

    #[test]
    fn same_line_empty_bodies_keep_the_spaced_form() {
        let input = "function g() {}\nclass D { constructor() {} }\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("function g() { }"), "{code}");
        assert!(code.contains("constructor() { }"), "{code}");
    }

    #[test]
    fn statement_block_expands_even_when_authored_single_line() {
        // Authority: parser768531 baseline expands an authored single-line
        // standalone block; preservation belongs to function-family bodies.
        let input = "{ a: 3; } /x/;";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "{\n    a: 3;\n}\n/x/;\n");
    }

    #[test]
    fn static_init_block_preserves_single_line_in_javascript() {
        // Authority: classThisReference(target=esnext).js keeps
        // `static { this; }` on its authored line while the class body
        // around it expands.
        let input = "class C { static { this; } static x = this; }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(
            javascript(&output).code.contains("static { this; }"),
            "{output:?}"
        );
    }

    #[test]
    fn empty_interface_body_expands_in_declaration_emit() {
        // Authority: importTag16 a.d.ts expands tight-authored
        // `export interface I {}` to `export interface I {\n}` (0 tight
        // / 21 expand in true declaration outputs; the 24 tights are
        // d.ts input copies echoed into the output zone, not outputs).
        let input = "export default interface Foo {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_declaration(parsed.product());
        assert_eq!(
            declaration(&output).code,
            "export default interface Foo {\n}\n"
        );
    }

    #[test]
    fn comments_above_statements_survive_in_javascript() {
        let emit = |input: &str, remove_comments: bool| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("// above\nvar x = 1;\n// next\nvar y = 2;\n", false),
            "// above\nvar x = 1;\n// next\nvar y = 2;\n"
        );
        assert_eq!(
            emit("/* one */ var x = 1;\n", false),
            "/* one */ var x = 1;\n"
        );
        assert_eq!(
            emit("function f() {\n    // inner\n    return 1;\n}\n", false),
            "function f() {\n    // inner\n    return 1;\n}\n"
        );
        assert_eq!(
            emit("var x; // t\n// next\nvar y;\n", false),
            "var x; // t\n// next\nvar y;\n"
        );
        // A comment on an erased declaration goes with it.
        assert_eq!(
            emit("// gone\ninterface I {}\n// kept\nvar x;\n", false),
            "// kept\nvar x;\n"
        );
        // A header stays even when the first statement erases.
        assert_eq!(
            emit("// header\n\n// gone\ninterface I {}\nvar x;\n", false),
            "// header\nvar x;\n"
        );
        assert_eq!(emit("var x;\n// end\n", false), "var x;\n// end\n");
        // The rewriter removes a `declare` from the list, but its comment stays
        // with it rather than moving to the next statement that prints.
        assert_eq!(
            emit(
                "// one\ndeclare var a;\n\n// two\ndeclare var b;\nc();\n",
                false
            ),
            "c();\n"
        );
        assert_eq!(
            emit("if (a) {\n    /* a\n       b */\n    f();\n}\n", false),
            "if (a) {\n    /* a\n       b */\n    f();\n}\n"
        );
        assert_eq!(emit("// above\nvar x; // t\n// end\n", true), "var x;\n");
    }

    #[test]
    fn leading_param_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("function foo(/*c1*/ x, /*d1*/ y, /*e1*/ w) { }\n"),
            "function foo(/*c1*/ x, /*d1*/ y, /*e1*/ w) { }\n"
        );
        assert_eq!(
            emit("function foo(/**hm*/ a) { }\n"),
            "function foo(/**hm*/ a) { }\n"
        );
    }

    #[test]
    fn trailing_param_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("function commentedParameters(a /* parameter a */, b /* parameter b */) { }\n"),
            "function commentedParameters(a /* parameter a */, b /* parameter b */) { }\n"
        );
        assert_eq!(
            emit("function foo2(greeting, ...restGreetings /* more greeting */) { }\n"),
            "function foo2(greeting, ...restGreetings /* more greeting */) { }\n"
        );
    }

    #[test]
    fn call_argument_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("foo(/*c1*/ x, y /*c2*/);\n"),
            "foo(/*c1*/ x, y /*c2*/);\n"
        );
        assert_eq!(emit("foo(0 /* E.A */);\n"), "foo(0 /* E.A */);\n");
    }

    #[test]
    fn empty_paren_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(emit("a( /*1*/);\n"), "a( /*1*/);\n");
        assert_eq!(
            emit("function foo( /** nothing */) { }\n"),
            "function foo( /** nothing */) { }\n"
        );
    }

    #[test]
    fn multiline_param_comments_keep_line_breaks() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("function commentedParameters(\n/* Parameter a */\na\n/* End of parameter a */\n/* Parameter b */\n,\nb\n/* End of parameter b */\n) { }\n"),
            "function commentedParameters(\n/* Parameter a */\na\n/* End of parameter a */\n/* Parameter b */\n, b\n/* End of parameter b */\n) { }\n"
        );
    }

    #[test]
    fn removecomments_drops_param_comments_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: true,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("function foo(/*c*/ x, y /*d*/) { }\n"),
            "function foo(x, y) { }\n"
        );
        assert_eq!(emit("a( /*1*/);\n"), "a();\n");
    }

    #[test]
    fn declare_function_keeps_param_comment() {
        let input = "declare function f1(/**param a*/ a: number): number;\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_declaration(parsed.product());
        assert_eq!(
            declaration(&output).code,
            "declare function f1(/**param a*/ a: number): number;\n"
        );
    }
    #[test]
    fn if_condition_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("if /*c*/ ( /*d*/ true /*e*/) /*f*/ { }\n"),
            "if /*c*/ ( /*d*/true /*e*/) /*f*/ { }\n"
        );
    }

    #[test]
    fn while_condition_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("/*a*/ while /*b*/ ( /*c*/false /*d*/) /*e*/ { }\n"),
            "/*a*/ while /*b*/ ( /*c*/false /*d*/) /*e*/ { }\n"
        );
    }

    #[test]
    fn for_condition_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("for (/*c2*/ a; /*c4*/ a; /*c6*/ a) { }\n"),
            "for (/*c2*/a; /*c4*/ a; /*c6*/ a) { }\n"
        );
        assert_eq!(
            emit("for (/*c*/ var x in /*o*/ y) { }\n"),
            "for (/*c*/var x in /*o*/ y) { }\n"
        );
    }

    #[test]
    fn paren_expression_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("var j = ( /* Preserve */j = f());\n"),
            "var j = ( /* Preserve */j = f());\n"
        );
    }

    #[test]
    fn catch_binding_comments_survive_in_javascript() {
        let emit = |input: &str| {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
            ));
            assert!(parsed.diagnostics().is_empty());
            let options = EmitOptions {
                remove_comments: false,
                ..EmitOptions::default()
            };
            javascript(&emit_output(parsed.product(), &options))
                .code
                .clone()
        };
        assert_eq!(
            emit("try {\n} catch ( /*c*/[/*a*/ a]) {\n}\n"),
            "try {\n}\ncatch ( /*c*/[/*a*/ a]) {\n}\n"
        );
    }


    #[test]
    fn trailing_line_comment_follows_statement_in_javascript() {
        // Authority: arrayAugment prints `var y; // Expect no error here`
        // with removeComments off (the default).
        let input = "var x = 1; // first\nvar y; // Expect no error here\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("var x = 1; // first\n"), "{code}");
        assert!(code.contains("var y; // Expect no error here\n"), "{code}");
    }

    fn emit_authored_js(input: &str) -> String {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        javascript(&output).code.clone()
    }

    #[test]
    fn brace_less_control_bodies_break_onto_an_indented_line() {
        // Authority: APISample_jsdoc emitted `if (tags)` / `flat.push(...tags);`,
        // typePredicateTopLevelTypeParameter, reachabilityChecks1 (`while (true);`).
        let code = emit_authored_js(
            "function f(x) {\n    if (x) return 1;\n    while (x);\n    for (;;) break;\n}\n",
        );
        assert!(
            code.contains(
                "    if (x)\n        return 1;\n    while (x)\n        ;\n    for (;;)\n        break;\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn else_catch_and_finally_start_their_own_line() {
        // Authority: tryCatchFinally, propertyWrappedInTry (`} catch(e) {}` in
        // the source, `}` then `catch (e) { }` emitted), inferTypePredicates.
        let code = emit_authored_js(
            "function f(x) {\n    if (x) { a(); } else if (x) { b(); } else { c(); }\n    try { a(); } catch (e) {} finally { b(); }\n}\n",
        );
        assert!(
            code.contains(
                "    if (x) {\n        a();\n    }\n    else if (x) {\n        b();\n    }\n    else {\n        c();\n    }\n    try {\n        a();\n    }\n    catch (e) { }\n    finally {\n        b();\n    }\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn empty_statement_blocks_keep_the_lines_they_were_authored_on() {
        // Authority: forInStatement1, catchClauseWithInitializer1.
        let code = emit_authored_js("var x: any;\nfor (var a in x) {\n}\nwhile (x) {}\n");
        assert!(
            code.contains("for (var a in x) {\n}\nwhile (x) { }\n"),
            "{code}"
        );
    }

    #[test]
    fn an_authored_new_without_arguments_keeps_its_missing_parentheses() {
        // Authority: iterableArrayPattern10 (`value: new Foo,`) and
        // iteratorSpreadInCall (`foo(...new SymbolIterator);`) print no `()`.
        let code = emit_authored_js(
            "class Foo {}\nvar a = new Foo;\nvar b = new Foo();\nf(new Foo, new Foo());\n",
        );
        assert!(
            code.contains("var a = new Foo;\nvar b = new Foo();\nf(new Foo, new Foo());\n"),
            "{code}"
        );
    }

    #[test]
    fn no_emit_helpers_omits_helper_definitions() {
        // Authority: asyncAliasReturnType_es6 — with noEmitHelpers the
        // __awaiter reference remains but no helper body is emitted.
        let options = EmitOptions {
            target: ScriptTarget::Es2015,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "async function f(): Promise<void> {\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("return __awaiter(this, void 0, void 0, function* () {"),
            "{code}"
        );
        assert!(!code.contains("function __awaiter("), "{code}");
        assert!(!code.contains("function __generator("), "{code}");
    }

    #[test]
    fn es5_async_empty_body_lowers_to_generator_machine() {
        // Authority: es5-asyncFunction(target=es5) `empty` — a yield-free
        // body becomes the linear machine with the bare return sentinel.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nasync function empty() {\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function empty() {\n    return __awaiter(this, void 0, void 0, function () {\n        return __generator(this, function (_a) {\n            return [2 /*return*/];\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_async_await_lowers_to_switch_machine() {
        // Authority: es5-asyncFunction(target=es5) `singleAwait` — each
        // statement-level await splits a labeled case and the resumed value
        // is consumed through _a.sent().
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nasync function singleAwait() {\n    await x;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function singleAwait() {\n    return __awaiter(this, void 0, void 0, function () {\n        return __generator(this, function (_a) {\n            switch (_a.label) {\n                case 0: return [4 /*yield*/, x];\n                case 1:\n                    _a.sent();\n                    return [2 /*return*/];\n            }\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_async_statements_hoist_vars_into_machine() {
        // Authority: awaitCallExpression5_es5(target=es5) `func` — var
        // declarations hoist outside __generator and rebind as assignments.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var a: boolean;\ndeclare var o: { fn(arg0: boolean, arg1: boolean, arg2: boolean): void; };\ndeclare function before(): void;\ndeclare function after(): void;\nasync function func(): Promise<void> {\n    before();\n    var b = o.fn(a, a, a);\n    after();\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function func() {\n    return __awaiter(this, void 0, void 0, function () {\n        var b;\n        return __generator(this, function (_a) {\n            before();\n            b = o.fn(a, a, a);\n            after();\n            return [2 /*return*/];\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn a_clause_keeps_its_only_statement_on_the_authored_line() {
        // Authority: booleanLiteralTypes1 (`case true: return "true";`) and
        // sourceMapValidationSwitch (two statements, or one on its own line,
        // print one per line).
        let input = "var x = 10;\nswitch (x) {\ncase 5: x = 0;\ncase 6: x++; break;\ncase 7:\n    x = 1;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(
            code.contains(
                "    case 5: x = 0;\n    case 6:\n        x++;\n        break;\n    case 7:\n        x = 1;\n"
            ),
            "{code}"
        );
    }

    #[test]
    fn empty_switch_expands_to_two_lines() {
        // Authority: switchStatements.js — `switch ('') { }` (and 13 siblings)
        // prints as `switch ('') {\n}`.
        let code = emit_authored_js("var x: any;\nswitch (x) { }\n");
        assert!(code.contains("switch (x) {\n}\n"), "{code}");
        assert!(!code.contains("switch (x) {}"), "{code}");
    }

    #[test]
    fn nested_empty_switch_keeps_its_indent() {
        // Authority: switchStatements.js empty switches at top level; nesting
        // checks the close brace aligns with `switch` instead of column 0.
        let code = emit_authored_js("function f(x) {\n    switch (x) { }\n}\n");
        assert!(code.contains("    switch (x) {\n    }\n"), "{code}");
    }

    #[test]
    fn es5_async_arrow_becomes_function_expression() {
        // Authority: asyncArrowFunction1_es5(target=es5) — ES5 has no
        // arrows, so the lowered arrow is a function expression returning
        // the awaiter with a `void 0` receiver (arrows never bind `this`).
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "var foo = async (): Promise<void> => {\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "var foo = function () { return __awaiter(void 0, void 0, void 0, function () {\n    return __generator(this, function (_a) {\n        return [2 /*return*/];\n    });\n}); };";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_async_if_branch_await_builds_labeled_machine() {
        // Authority: es5-asyncFunctionIfStatements(target=es5)
        // ifStatement2 — a suspending consequent builds the labeled shape:
        // negated-test break to the else label, the consequent, a break to
        // the end label, the alternate under the else label with an
        // explicit end-label assignment, and the end label itself.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y, z;\nasync function ifStatement2() {\n    if (x) { await y; } else { z; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("if (!x) return [3 /*break*/, 2];"), "{code}");
        assert!(
            code.contains("case 2:\n                    z;\n                    _a.label = 3;\n                case 3: return [2 /*return*/];"),
            "{code}"
        );
    }

    #[test]
    fn es5_async_while_body_await_builds_loop_machine() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5)
        // whileStatement2 — a suspending loop body builds the labeled
        // shape: guard at the head, resume translating to a head jump,
        // exit label after.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y;\nasync function whileStatement2() {\n    while (x) { await y; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("if (!x) return [3 /*break*/, 2];"), "{code}");
        assert!(
            code.contains("case 1:\n                    _a.sent();\n                    return [3 /*break*/, 0];\n                case 2: return [2 /*return*/];"),
            "{code}"
        );
    }

    #[test]
    fn es5_async_do_while_builds_positive_guard_machine() {
        // Authority: es5-asyncFunctionDoStatements(target=es5)
        // doStatement1 — the do-while guard is positive (loop-back is the
        // taken branch) and continue jumps to the test label, not the head.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y;\nasync function doStatement1() {\n    do { await x; } while (y);\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("case 2:\n                    if (y) return [3 /*break*/, 0];\n                    _a.label = 3;\n                case 3: return [2 /*return*/];"),
            "{code}"
        );
    }

    #[test]
    fn es5_async_for_clause_await_builds_phase_labels() {
        // Authority: es5-asyncFunctionForStatements(target=es5)
        // forStatement2 — the test clause suspends: init marks the test
        // label, the guard resumes from the yield, the update loops back
        // to the test label, and continue targets the update label.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y, z, a;\nasync function forStatement2() {\n    for (x; await y; z) { a; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("case 0:\n                    x;\n                    _a.label = 1;\n                case 1: return [4 /*yield*/, y];"),
            "{code}"
        );
        assert!(
            code.contains(
                "case 3:\n                    z;\n                    return [3 /*break*/, 1];"
            ),
            "{code}"
        );
    }

    #[test]
    fn es5_labeled_while_with_labeled_continue_lowers() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5)
        // whileStatement7 — a clean labeled loop with a labeled continue
        // still lowers to the machine; the leaked-await walker once
        // refused every labeled loop body, and no other pin covers it.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nasync function f() {\n    A: while (x) { continue A; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("A: while (x) {\n                continue A;\n            }\n            return [2 /*return*/];"),
            "{code}"
        );
        assert!(!code.contains("function*"), "{code}");
    }

    #[test]
    fn es5_async_switch_case_await_builds_dispatch_chain() {
        // Authority: es5-asyncFunctionSwitchStatements(target=es5)
        // switchStatement2 — a suspending case test yields, and its
        // resume opens a dispatch over the held discriminant comparing
        // the sent value, falling through to the default body's label.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y, a, b;\nasync function switchStatement2() {\n    switch (x) { case await y: a; break; default: b; break; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("case _b.sent(): return [3 /*break*/, 2];"),
            "{code}"
        );
        assert!(code.contains("return [3 /*break*/, 3];"), "{code}");
    }

    #[test]
    fn es5_async_arrow_passes_the_captured_this_to_the_awaiter() {
        // Authority: asyncArrowFunctionCapturesThis_es5(target=es5) binds
        // `var _this = this;` and calls `__awaiter(_this, ...)`; only a body
        // that reads `arguments` hoists `arguments_1`
        // (asyncArrowFunctionCapturesArguments_es5).
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nvar foo = async () => {\n    await x;\n    this.y = 1;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("var _this = this;\n"), "{code}");
        assert!(
            code.contains("__awaiter(_this, void 0, void 0, function () {"),
            "{code}"
        );
        assert!(!code.contains("arguments_1"), "{code}");
    }

    #[test]
    fn arrow_single_param_parens_follow_the_authored_form() {
        // Authority: complicatedIndexesOfIntersectionsAreInferencable keeps
        // `props => {`; arrowFunctionContexts keeps `(props) =>` and `() =>`.
        // The AST drops the distinction, so the token stream answers.
        let input = "var a = props => { return props; };
var b = (props) => { return props; };
var c = () => 1;
";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("var a = props => {"), "{code}");
        assert!(code.contains("var b = (props) => {"), "{code}");
        assert!(code.contains("var c = () =>"), "{code}");
    }

    #[test]
    fn trailing_comment_attaches_to_the_last_statement_on_its_line() {
        // tsc attaches a trailing comment to the last statement on the
        // source line only: `var a = 1; var b = 2; // note` prints the
        // comment after `b`, never duplicated after `a`.
        let input = "var a = 1; var b = 2; // note\nvar c = 3;\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("var a = 1;\n"), "{code}");
        assert!(code.contains("var b = 2; // note\n"), "{code}");
    }

    #[test]
    fn decorators_round_trip_through_javascript_emit() {
        let input = "@classFirst @classSecond class C {\n\
                     @constructorFirst @constructorSecond\n\
                     constructor(@constructorParameterFirst @constructorParameterSecond parameter) {}\n\
                     @methodFirst @methodSecond\n\
                     method(@methodParameterFirst @methodParameterSecond parameter) {}\n\
                     @propertyFirst @propertySecond\n\
                     property = 1;\n\
                     @accessorFirst @accessorSecond\n\
                     accessor value = 2;\n\
                     }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            concat!(
                "@classFirst\n",
                "@classSecond\n",
                "class C {\n",
                "    @constructorFirst\n",
                "    @constructorSecond\n",
                "    constructor(@constructorParameterFirst @constructorParameterSecond parameter) { }\n",
                "    @methodFirst\n",
                "    @methodSecond\n",
                "    method(@methodParameterFirst @methodParameterSecond parameter) { }\n",
                "    @propertyFirst\n",
                "    @propertySecond\n",
                "    property = 1;\n",
                "    @accessorFirst\n",
                "    @accessorSecond\n",
                "    accessor value = 2;\n",
                "}\n",
            ),
        );

        let reparsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(javascript(&output).code.as_str())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        assert!(reparsed.diagnostics().is_empty());
        let file = reparsed.product();
        let source = file.source_text();
        let decorator_texts = |decorators: &[DecoratorNode]| {
            decorators
                .iter()
                .map(|decorator| {
                    let range = decorator.range();
                    let start = source
                        .utf16_to_byte(range.start())
                        .expect("decorator range starts on a source boundary");
                    let end = source
                        .utf16_to_byte(range.end())
                        .expect("decorator range ends on a source boundary");
                    &source.as_str()[start..end]
                })
                .collect::<Vec<_>>()
        };

        let Statement::Class(class) = file.statements()[0].data() else {
            panic!("expected a class declaration");
        };
        assert_eq!(
            decorator_texts(&class.decorators),
            ["@classFirst", "@classSecond"]
        );

        let ClassMember::Constructor(constructor) = class.members[0].data() else {
            panic!("expected a constructor");
        };
        assert_eq!(
            decorator_texts(&constructor.decorators),
            ["@constructorFirst", "@constructorSecond"]
        );
        assert_eq!(
            decorator_texts(&constructor.parameters[0].data().decorators),
            ["@constructorParameterFirst", "@constructorParameterSecond"]
        );

        let ClassMember::Method(method) = class.members[1].data() else {
            panic!("expected a method");
        };
        assert_eq!(
            decorator_texts(&method.function.decorators),
            ["@methodFirst", "@methodSecond"]
        );
        assert_eq!(
            decorator_texts(&method.function.parameters[0].data().decorators),
            ["@methodParameterFirst", "@methodParameterSecond"]
        );

        let ClassMember::Property(property) = class.members[2].data() else {
            panic!("expected a property");
        };
        assert_eq!(
            decorator_texts(&property.decorators),
            ["@propertyFirst", "@propertySecond"]
        );

        let ClassMember::AutoAccessor(accessor) = class.members[3].data() else {
            panic!("expected an auto-accessor");
        };
        assert_eq!(
            decorator_texts(&accessor.decorators),
            ["@accessorFirst", "@accessorSecond"]
        );
    }

    #[test]
    fn pr199_for_of_assignment_targets_lower_to_indexed_loops() {
        let source = "var target = {}; for (target[2 ** 1] of source(2 ** 3)) { use(target); }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("fits")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let statement = parsed.product().statements().last().expect("loop");
        let crate::syntax::Statement::ForOf(for_of) = statement.data() else {
            panic!("expected a for-of AST for {source}");
        };
        assert!(matches!(
            for_of.binding,
            crate::syntax::ForBinding::Target(_)
        ));
        let output = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = &javascript(&output).code;
        assert!(!code.contains(" of "), "native for-of survived ES5: {code}");
        assert_eq!(code.matches("Math.pow(2, 3)").count(), 1, "{code}");
        assert_eq!(code.matches("Math.pow(2, 1)").count(), 1, "{code}");
        assert!(!code.contains("**"), "{code}");
        let assign = code
            .find("target[Math.pow(2, 1)] = ")
            .expect("indexed assignment");
        let use_call = code.find("use(target)").expect("body");
        assert!(assign < use_call, "{code}");
    }

    fn pr199_emit_at(input: &str, target: ScriptTarget) -> EmitOutput {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("fits")),
        ));
        assert!(
            parsed.diagnostics().is_empty(),
            "{:?}",
            parsed.diagnostics()
        );
        emit_output(
            parsed.product(),
            &EmitOptions {
                target,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        )
    }

    #[test]
    fn pr199_native_declarations_emit_keys_in_declarator_order() {
        let source = "declare function before(): number; \
            declare function key(): string; \
            declare function between(): number; \
            declare function laterKey(): string; \
            declare function after(): number; \
            declare function finish(): void; \
            function* g() { \
                const left = before(), C = class { [yield key()]() {} }, \
                    middle = between(), D = class { [yield laterKey()]() {} }, \
                    right = after(); \
                finish(); return [left, C, middle, D, right]; \
            }";
        for target in [ScriptTarget::Es2015, ScriptTarget::Es2016] {
            let output = pr199_emit_at(source, target);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            let code = &javascript(&output).code;
            let positions = [
                "before()",
                "key()",
                "C =",
                "between()",
                "laterKey()",
                "D =",
                "after()",
                "finish()",
            ]
            .map(|needle| {
                assert_eq!(code.matches(needle).count(), 1, "{needle}: {code}");
                code.find(needle).expect("one occurrence")
            });
            assert!(positions.windows(2).all(|pair| pair[0] < pair[1]), "{code}");
        }
    }

    #[test]
    fn pr199_async_native_declarations_do_not_lose_key_awaits() {
        let source = "declare function before(): number; \
            declare function key(): string; declare function after(): number; \
            async function g() { \
                const left = before(), C = class { [await key()]() {} }, right = after(); \
                return [left, C, right]; \
            }";
        let output = pr199_emit_at(source, ScriptTarget::Es2015);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        let code = &javascript(&output).code;
        let positions = ["before()", "key()", "C =", "after()"].map(|needle| {
            assert_eq!(code.matches(needle).count(), 1, "{needle}: {code}");
            code.find(needle).expect("one occurrence")
        });
        assert!(positions.windows(2).all(|pair| pair[0] < pair[1]), "{code}");
        assert!(
            code.contains("yield"),
            "await must survive as a suspension: {code}"
        );
        assert!(!code.contains("await key()"), "raw await leaked: {code}");
    }

    #[test]
    fn es5_async_for_update_increment_lowers() {
        // Synthetic probe pinning the walker/machine contract: a for-update
        // `i++` (Update over an Identifier) counts as zero resumes after the
        // walker fix, so a suspending for-loop still lowers normally with
        // the update emitted as plain machine code.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any, y: any, i: any;\nasync function f() {\n    for (; x; i++) { await y; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function f() {\n    return __awaiter(this, void 0, void 0, function () {\n        return __generator(this, function (_a) {\n            switch (_a.label) {\n                case 0: _a.label = 1;\n                case 1:\n                    if (!x) return [3 /*break*/, 4];\n                    return [4 /*yield*/, y];\n                case 2:\n                    _a.sent();\n                    _a.label = 3;\n                case 3:\n                    i++;\n                    return [3 /*break*/, 1];\n                case 4: return [2 /*return*/];\n            }\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
        assert!(!code.contains("function*"), "{code}");
    }

    #[test]
    fn es5_generator_update_computed_key_refuses() {
        // Synthetic probe pinning the walker/machine contract: a while-test
        // computed-key yield (`o[yield k]++` inside the test) counts as a
        // resume, so the loop cannot stay inline; lowering routes to eval,
        // which refuses with GENERATOR_REQUIRES_ES2015, and the native
        // generator survives — never the inline machine clone.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input =
            "declare var o: any, k: any;\nfunction* g() {\n    while (o[yield k]++ < 3) { }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(code.contains("function* g("), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn es5_async_temp_collision_with_user_var() {
        // Authority: awaitBinaryExpression5_es5 / asyncFunctionDeclaration9 —
        // when a user variable collides with the machine's default temp name,
        // the machine state parameter is renamed to _b and the user's _a stays
        // the hoisted var.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input =
            "async function f(x: any) {\n    var _a = 1;\n    await x;\n    return _a;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function (_b)"), "{code}");
        assert!(code.contains("_b.label"), "{code}");
        assert!(code.contains("_b.sent()"), "{code}");
        assert!(code.contains("var _a;"), "{code}");
        assert!(code.contains("_a = 1;"), "{code}");
    }

    #[test]
    fn es5_async_leaked_await_refuses() {
        // Authority: es5-asyncFunction(target=es5) leaked await in left-hand
        // of property access assignment cannot be lowered, so the native
        // generator fallback is kept.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "async function f(a: any, b: any, c: any) {\n    (await a).b = c;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function* ()"), "{code}");
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(!code.contains(".sent()"), "{code}");
    }

    #[test]
    fn es5_async_binary_expression_await_materializes() {
        // Authority: awaitBinaryExpression5_es5(target=es5) — the awaited
        // operand is evaluated first, then combined with the saved left value
        // through `.sent()`.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "async function f(a: any, b: any) {\n    return a + (await b);\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function (_b)"), "{code}");
        assert!(code.contains("_b.label"), "{code}");
        assert!(code.contains("_a + (_b.sent())"), "{code}");
    }

    #[test]
    fn es5_async_switch_discriminant_await_inline() {
        // Return-bearing cases must not ride the discriminant-inline path:
        // cloning them verbatim embeds a raw `return 10` in the machine's
        // inner function, which drops the value through the protocol. Until
        // the rebuilt-cases path routes returns through machine_statements,
        // this shape refuses with the diagnostic — never a silent clone.
        let output = emit_es5_clean(
            "declare var x: any;\nasync function f() { switch (await x) { case 1: return 10; default: return 20; } }\n",
        );
        let code = &javascript(&output).code;
        assert!(
            !code.contains("__generator(this,"),
            "raw returns must not clone into the machine: {code}"
        );
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must signal: {:?}",
            output.diagnostics
        );
        // A return-free discriminant case still lowers inline.
        let lowered = emit_es5_clean(
            "declare var x: any;\nasync function f() { switch (await x) { case 1: r = 10; } }\n",
        );
        let code = &javascript(&lowered).code;
        assert!(code.contains("switch (_a.sent())"), "{code}");
    }

    #[test]
    fn es5_async_labeled_loop_with_await_and_break_lowers() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5) — a labeled
        // while body with an await and a labeled break lowers to the machine;
        // the break becomes an explicit branch to the exit label.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any, y: any;\nasync function f() {\n    A: while (x) { await y; break A; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(!code.contains("function*"), "{code}");
        assert!(
            code.contains("__awaiter(this, void 0, void 0, function ("),
            "{code}"
        );
        assert!(code.contains("if (!x) return [3 /*break*/, 2];"), "{code}");
        assert!(code.contains("_a.sent();"), "{code}");
        assert!(code.contains("return [3 /*break*/, 2];"), "{code}");
    }

    #[test]
    fn es5_async_identifier_assignment_test_stays_inline() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5) — a while
        // test that only assigns to an identifier carries no resume, so the
        // whole test clones verbatim into the machine instead of routing the
        // loop through eval.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any, y: any;\nasync function f() {\n    while (x = 1) { await y; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("if (!(x = 1))"), "{code}");
        assert_eq!(
            code.matches("return [4 /*yield*/, y];").count(),
            1,
            "{code}"
        );
        assert!(!code.contains("function*"), "{code}");
    }
    #[test]
    fn es5_generator_object_spread_yield_refuses() {
        // Contract pin, not a mutation claim: a while-test object spread
        // carrying a yield (`{ ...(yield x) }`) is refused upstream by the
        // machine's object-member wildcard, so the native generator survives
        // whether or not count_yields tracks the spread — this pins the
        // refusal shape: never the inline machine clone.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any;\nfunction* g() {\n    while ({ ...(yield x) }) { }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function* g("), "{code}");
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn es5_generator_array_spread_yield_never_clones() {
        // Mutation-provable: an array-literal spread carrying a yield
        // (`[...(yield x)]` as a statement) must never lower to the inline
        // machine — contains_yield_array reports the spread's yield, the
        // lowering bails, and the native generator survives with
        // GENERATOR_REQUIRES_ES2015. Reverting the Spread arm resurrects
        // `__generator(this, ...)` wrapping a live yield.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any;\nfunction* g() {\n    [...(yield x)];\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function* g("), "{code}");
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    // ------------------------------------------------------------------
    // Adversarial hardening: the walker-duality contract as an invariant,
    // not a shape list. Assumptions under test (IDs cited per test):
    //   WD-1 duality: no emitted machine embeds a live yield outside a
    //       `return [4 /*yield*/, ...]` split (generic leak detector).
    //   WD-2 sentinel shapes (TaggedTemplate/Satisfies/TypeAssertion/JSX)
    //       are eval-refused, never inline-cloned.
    //   WD-3 count == segments eval mints: machine case labels are
    //       contiguous 0..=max and unique (gap detector; boundaries
    //       0/1/2/3 suspensions).
    //   WD-4 nested function-likes own their suspensions: cloning them
    //       is correct, their internal yield is legal.
    //   WD-5 non-block loop bodies refuse, never miscompile.
    //   WD-6/7 Import (source+options) and Conditional/Logical counts
    //       feed exact label arithmetic.
    //   WD-8 labeled-loop delegation covers nested awaited bodies.
    //   WD-9 recursive walkers survive deep nesting without crashing.
    // ------------------------------------------------------------------

    /// B4: destructuring defaults lower to tsc's ES5 shape - a temp
    /// read then a `=== void 0` ternary - never erasing the default.
    #[test]
    fn destructuring_defaults_lower_to_ternary_declarators() {
        let cases = [
            (
                "var o:any;\nvar { a = 1 } = o;\n",
                "var _a = o.a, a = _a === void 0 ? 1 : _a;",
            ),
            (
                "var o:any;\nvar { p: q = 2 } = o;\n",
                "var _a = o.p, q = _a === void 0 ? 2 : _a;",
            ),
            (
                "var o:any;\nvar { x: { y } = {} } = o;\n",
                "var _a = o.x, _b = _a === void 0 ? {} : _a, y = _b.y;",
            ),
            (
                "var arr:any;\nvar [c = 3, , [d = 4] = []] = arr;\n",
                "var _a = arr[0], c = _a === void 0 ? 3 : _a, _b = arr[2], _c = _b === void 0 ? [] : _b, _d = _c[0], d = _d === void 0 ? 4 : _d;",
            ),
        ];
        for (src, expected) in cases {
            let out = emit_es5_clean(src);
            let code = javascript(&out).code.clone();
            assert!(
                code.contains(expected),
                "missing tsc default shape `{expected}` in:\n{code}"
            );
        }
    }

    /// B4: a default's suspension survives lowering - the machine splits
    /// the default selection and no live yield leaks.
    #[test]
    fn destructuring_default_suspension_splits_the_machine() {
        let out =
            emit_es5_clean("var o:any, k:any;\nfunction* g(){ var { m = (yield k) } = o; }\n");
        let code = javascript(&out).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("=== void 0"),
            "selection test missing:\n{code}"
        );
        assert!(
            code.contains("[4 /*yield*/, k]"),
            "suspension missing:\n{code}"
        );
        assert!(code.contains("m = _b;"), "final bind missing:\n{code}");
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
    }

    /// B4: an await default must not land in a ternary - eval refuses
    /// Conditional, so the __awaiter inner generator would stay native
    /// `function*` at ES5. The branch form keeps the inner machine.
    #[test]
    fn destructuring_default_await_keeps_the_inner_machine() {
        let out = emit_es5_clean(
            "var o:any, k:any;\nasync function h(){ var { n = await k } = o; return n; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(code.contains("__awaiter("), "async wrapper: {code}");
        assert!(
            code.contains("__generator(this,"),
            "inner machine lost - await landed in a ternary:\n{code}"
        );
        assert!(!code.contains("? yield"), "ternary yield:\n{code}");
    }

    /// B4 walker: a suspending for-init binding signals refusal with the
    /// requires-es2015 diagnostic rather than cloning silently.
    #[test]
    fn for_init_suspending_binding_signals_refusal() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(
                "var o:any, k:any;\nfunction* g(){ for (var { a = (yield k) } = o;;) { break; } }\n",
            )
            .expect("fits")),
        ));
        let out = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.message().contains("generators require")),
            "refusal must be signalled"
        );
    }

    /// B1: a suspending computed class key hoists out of the class
    /// IIFE in statement contexts - the arrow is a plain function and
    /// tsc 6.0.2 itself emits a SyntaxError for the in-IIFE form. The
    /// machine splits the hoisted key temp and the arrow stays clean.
    #[test]
    fn class_computed_key_suspension_hoists_out_of_the_iife() {
        let out = emit_es5_clean(
            "var k:any;\nfunction* g(){ var C = class { [yield k]() {} }; return C; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("[4 /*yield*/, k]"),
            "the key's suspension must split:\n{code}"
        );
        assert!(
            code.contains("_b = _c.sent()"),
            "the key temp binds from sent():\n{code}"
        );
        assert!(
            code.contains("[_b]()"),
            "the member reads the hoisted temp:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
    }

    /// B1: expression-position class expressions cannot hoist (no
    /// enclosing statement drains key_prelude), so they keep tsc's
    /// in-IIFE shape but carry the requires-es2015 refusal instead of
    /// breaking silently.
    #[test]
    fn class_computed_key_in_expression_position_signals_refusal() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new("var k:any;\nfunction* h(){ foo(class { [yield k]() {} }); }\n")
                    .expect("fits"),
            ),
        ));
        let out = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.message().contains("generators require")),
            "expression-position suspension must refuse loudly"
        );
    }

    /// B7: if-without-else is the empty else, not a refusal - both the
    /// inline clean clone and the suspending labeled shape must lower.
    #[test]
    fn if_without_else_lowers_in_the_machine() {
        let suspending =
            emit_es5_clean("var c:any, x:any;\nfunction* g(){ if (c) { yield x; } yield 2; }\n");
        let code = javascript(&suspending).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("[4 /*yield*/, x]"),
            "the branch suspension must split:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
        let clean =
            emit_es5_clean("var c:any, x:any;\nfunction* g(){ yield 1; if (c) { x = 1; } }\n");
        let code = javascript(&clean).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(code.contains("if (c)"), "clean if clones inline:\n{code}");
    }

    /// Bot-round B4 gaps: the suspending-declaration path must keep
    /// sibling identifier declarators, declare computed-key temps,
    /// bind array rest, exclude computed keys from object rest with
    /// tsc's runtime coercion, and rewrite awaited sources so the
    /// __awaiter inner generator still machine-converts.
    #[test]
    fn suspending_declarations_keep_sibling_and_rest_semantics() {
        let out = emit_es5_clean(
            "var y:any, obj:any;\nfunction* g(){ var x = 5, { a = (yield y) } = obj; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("x = 5"),
            "sibling declarator dropped:\n{code}"
        );
        let out = emit_es5_clean(
            "var k:any, arr:any;\nfunction* g(){ var [a = (yield k), ...r] = arr; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("r = arr.slice(1)"),
            "array rest discarded:\n{code}"
        );
        let out =
            emit_es5_clean("var k:any, o:any;\nfunction* g(){ var { [k]: v, ...rest } = o; }\n");
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("typeof _a === \"symbol\" ? _a : _a + \"\""),
            "computed key must be excluded at runtime (tsc shape):\n{code}"
        );
        let out = emit_es5_clean("var k:any, o:any;\nfunction* g(){ var { [yield k]: v } = o; }\n");
        let code = javascript(&out).code.clone();
        assert!(code.contains("var v, _a, _b"), "temps declared:\n{code}");
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
        let out = emit_es5_clean("var k:any;\nasync function h(){ var { a } = await k; }\n");
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("__generator(this,"),
            "awaited source must rewrite so the inner machine converts:\n{code}"
        );
    }

    /// B1 order: computed keys evaluate in member order, so hoisting
    /// must move the whole prelude - partitioning suspending keys away
    /// from clean ones reorders evaluation.
    #[test]
    fn class_computed_keys_evaluate_in_member_order() {
        let out = emit_es5_clean(
            "var k1:any, k2:any;\nfunction* g(){ var C = class { [k1()](){} [yield k2()](){} }; }\n",
        );
        let code = javascript(&out).code.clone();
        let clean_first = code.find("k1()").expect("clean key evaluated");
        let suspending = code.find("k2()").expect("suspending key evaluated");
        assert!(
            clean_first < suspending,
            "member order must survive hoisting:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
        let out = emit_es5_clean(
            "var k1:any, k2:any;\nfunction* g(){ var C = class { [yield k1()](){} [k2()](){} }; }\n",
        );
        let code = javascript(&out).code.clone();
        let suspending = code.find("k1()").expect("suspending key evaluated");
        let clean_second = code.find("k2()").expect("clean key evaluated");
        assert!(
            suspending < clean_second,
            "member order must survive hoisting (suspending first):\n{code}"
        );
    }

    /// B1 visibility: an await inside a class computed key or heritage
    /// clause in expression position cannot lower - there is no hoist
    /// channel - and must refuse the generator natively under the
    /// requires-es2015 diagnostic, never bury the raw await inside a
    /// synthesized arrow the machine cannot see through.
    #[test]
    fn class_expression_awaits_refuse_natively() {
        for src in [
            "var k:any;\nasync function h(){ foo(class { [await k](){} }); }\n",
            "var f:any;\nasync function h(){ return class extends (await f()) {}; }\n",
        ] {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(src).expect("fits")),
            ));
            let out = emit_output(
                parsed.product(),
                &EmitOptions {
                    target: ScriptTarget::Es5,
                    no_emit_helpers: true,
                    ..EmitOptions::default()
                },
            );
            let code = javascript(&out).code.clone();
            assert!(
                !code.contains("__generator(this,"),
                "machine must refuse: {src}\n{code}"
            );
            assert!(
                out.diagnostics
                    .iter()
                    .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
                "refusal must be signalled: {src}"
            );
        }
    }

    /// A suspending static-field initializer (postlude) refuses the
    /// same way a key prelude does: the unlowered class keeps the
    /// suspension visible and the generator stays native under the
    /// signal - never a live yield inside the synthesized arrow.
    #[test]
    fn class_static_field_suspension_refuses_natively() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(
                    "var k:any;\nfunction* g(){ var C = class { static x = yield k; }; }\n",
                )
                .expect("fits"),
            ),
        ));
        let out = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&out).code.clone();
        assert!(
            !code.contains("__generator(this,"),
            "machine must refuse the static-field suspension:\n{code}"
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must be signalled"
        );
    }

    /// A for-of body suspending in a generator machine-splits through
    /// the lowered classic loop - the ladder's machine slice composing
    /// with the plain lowering.
    #[test]
    fn for_of_suspension_machine_splits_through_the_lowered_loop() {
        let out =
            emit_es5_clean("var it:any;\nfunction* g(){ for (const k of it) { yield k; } }\n");
        let code = javascript(&out).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("[4 /*yield*/, k]"),
            "the body's suspension must split:\n{code}"
        );
        assert!(
            code.contains("it_1[_i]"),
            "the binding reads the indexed element:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
    }

    /// A braceless for-of body is one statement, not a missing one:
    /// the emitted loop must still contain it.
    #[test]
    fn braceless_for_of_body_survives_lowering() {
        let out =
            emit_es5_clean("var arr:any;\nfunction f(){ for (const k of arr) console.log(k); }\n");
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("console.log(k)"),
            "the braceless body statement must survive:\n{code}"
        );
    }

    /// A destructuring binding in a for-of head composes with the
    /// destructuring lowering: the element read becomes the binding's
    /// initializer inside the loop body.
    #[test]
    fn for_of_pattern_binding_composes_with_destructuring() {
        let out = emit_es5_clean(
            "var arr:any;\nfor (const { a, b = 2 } of arr) { console.log(a + b); }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("void 0 ? 2 :"),
            "the binding default must lower inside the loop:\n{code}"
        );
        assert!(
            code.contains(".a"),
            "the member read must bind from the element:\n{code}"
        );
    }

    /// Emits `input` at es5 without helpers; panics on parse diagnostics.
    fn emit_es5_clean(input: &str) -> EmitOutput {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        )
    }

    /// WD-1: in machine form, every `yield` must sit inside a split marker
    /// `/*yield*/`; a bare yield is a live suspension cloned into a plain
    /// function (the miscompile class). Returns the offending snippet text.
    fn live_yield_leak(code: &str) -> Option<String> {
        if !code.contains("__generator(this,") {
            return None; // native refusal form: the generator owns its yields
        }
        code.lines()
            // Strip the protocol marker spans first: a line can carry both a
            // legitimate `return [4 /*yield*/, x]` split and a cloned live
            // yield; the marker must not exempt the whole line.
            .find(|line| {
                let stripped = line.replace("/*yield*/", "");
                // The match must end as a token: `yielding` is an
                // identifier, not the keyword.
                stripped.match_indices("yield").any(|(i, _)| {
                    stripped[i + 5..]
                        .chars()
                        .next()
                        .is_none_or(|c| !(c.is_alphanumeric() || c == '_' || c == '$'))
                })
            })
            .map(|line| line.trim().to_owned())
    }

    /// WD-1b: in machine form, every return must be a protocol return
    /// (`return [`) — a bare `return expr;` in the machine body exits the
    /// inner function directly and the runtime silently drops the value.
    /// Battery-scoped: snippets are flat (no nested function bodies, whose
    /// returns are legal); the nested-ownership contract has its own pin.
    fn raw_return_leak(code: &str) -> Option<String> {
        if !code.contains("__generator(this,") {
            return None;
        }
        code.lines()
            .find(|line| {
                let l = line.trim();
                // `return` must end as a token: `returning = 1;` is a
                // plain assignment, not a protocol-breaking return.
                let boundary = !l.starts_with("return")
                    || l[6..]
                        .chars()
                        .next()
                        .is_none_or(|c| c.is_whitespace() || c == ';' || c == '}' || c == '(');
                l.starts_with("return")
                    && boundary
                    && !l.starts_with("return [")
                    && !l.starts_with("return __generator")
                    && !l.starts_with("return __awaiter")
                    && l.ends_with(';')
            })
            .map(|line| line.trim().to_owned())
    }

    /// WD-3: the machine switch's case labels must be unique and contiguous
    /// from 0 (a gap or duplicate means count_yields disagreed with the
    /// segments eval actually minted).
    fn machine_case_labels(code: &str) -> Vec<u32> {
        // Any state parameter (_a, or _b after a temp collision); raw
        // labels with no dedup — the caller's equality assert fails on a
        // duplicate, which is the failure this helper guards.
        let start = code
            .match_indices("switch (_")
            .map(|(i, _)| i)
            .find(|&i| code[i..].contains(".label)"))
            .expect("machine switch");
        let body = &code[start..];
        let mut labels: Vec<u32> = body
            .split("case ")
            .skip(1)
            .filter_map(|rest| rest.split(':').next())
            .filter_map(|n| n.parse().ok())
            .collect();
        labels.sort_unstable();
        labels
    }

    #[test]
    fn es5_async_return_in_loop_body_never_drops_value() {
        // A cloned `return y` inside the machine body returns straight out
        // of the inner function; the runtime treats the non-array as done
        // with `void 0` — the value is silently dropped. The loop body
        // cannot lower a return, so the machine must refuse (until a
        // return-protocol slice lands), never clone.
        let output = emit_es5_clean(
            "declare var x: any, y: any;\nasync function f() { while (x) { return y; } }\n",
        );
        let code = &javascript(&output).code;
        assert!(
            !code.contains("__generator(this,"),
            "machine must not embed a raw return: {code}"
        );
        assert!(code.contains("return y;"), "value preserved: {code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must signal: {:?}",
            output.diagnostics
        );
    }

    #[test]
    fn walker_duality_battery_never_clones_live_yield() {
        // WD-1: each snippet puts a suspending shape behind each clone gate,
        // with its derived expectation: `true` lowers to the machine (and
        // must not leak), `false` refuses (native form + the requires-es2015
        // diagnostic + no machine). Expectations were derived from emitted
        // output; all-refusing output fails every `true` row.
        let snippets: [(&str, &str, bool); 31] = [
            (
                "update-computed-while",
                "declare var o: any, k: any;\nfunction* g() { while (o[k ? k : 0][`x`], o[yield k]++ < 3) { } }\n",
                false,
            ),
            (
                "array-spread-statement",
                "declare var x: any;\nfunction* g() { [...(yield x)]; }\n",
                false,
            ),
            (
                "array-spread-while-body",
                "declare var x: any, y: any;\nfunction* g() { while (y) { [...(yield x)]; } }\n",
                false,
            ),
            (
                "object-spread-do-test",
                "declare var x: any;\nfunction* g() { do { } while ({ ...(yield x) }); }\n",
                false,
            ),
            (
                "assignment-pattern-while",
                "declare var x: any, y: any;\nfunction* g() { while ({ a: x } = y) { yield x; } }\n",
                false,
            ),
            (
                "template-expr-statement",
                "declare var x: any;\nfunction* g() { `${yield x}`; }\n",
                true,
            ),
            (
                "conditional-expr-statement",
                "declare var x: any, y: any;\nfunction* g() { return (yield x) ? y : (yield x); }\n",
                true,
            ),
            (
                "logical-expr-statement",
                "declare var x: any, y: any;\nfunction* g() { return (yield x) || (yield y); }\n",
                true,
            ),
            (
                "import-expr-machine",
                "declare var x: any;\nfunction* g() { return import(yield x); }\n",
                true,
            ),
            (
                "new-suspending-args",
                "declare var x: any;\nfunction* g() { return new C(yield x); }\n",
                false,
            ),
            (
                "nested-if-await-while",
                "declare var x: any, y: any, z: any;\nasync function f() { while (x) { if (y) { await z; } } }\n",
                false,
            ),
            (
                "nested-if-await-labeled",
                "declare var x: any, y: any, z: any;\nasync function f() { A: while (x) { if (y) { await z; break A; } } }\n",
                false,
            ),
            (
                "nested-if-await-do",
                "declare var x: any, y: any, z: any;\nasync function f() { do { if (y) { await z; } } while (x); }\n",
                false,
            ),
            (
                "nested-if-await-if-arm",
                "declare var x: any, y: any, z: any;\nasync function f() { if (x) { if (y) { await z; } } }\n",
                false,
            ),
            (
                "return-in-while-body",
                "declare var x: any, y: any;\nasync function f() { while (x) { return y; } }\n",
                false,
            ),
            (
                "return-in-labeled-body",
                "declare var x: any, y: any;\nasync function f() { A: while (x) { return y; } }\n",
                false,
            ),
            (
                "return-in-if-branch",
                "declare var y: any, z: any;\nasync function f() { if (y) { return z; } }\n",
                false,
            ),
            (
                "clean-nested-while-clones",
                "declare var x: any, z: any;\nasync function f() { while (x) { while (z) { } } }\n",
                true,
            ),
            (
                "call-spread-arg",
                "declare var f: any, x: any;\nfunction* g() { f(...(yield x)); }\n",
                false,
            ),
            (
                "method-computed-name",
                "declare var k: any;\nfunction* g() { ({ [yield k]() {} }); }\n",
                false,
            ),
            (
                "nonblock-nested-return",
                "declare var x: any, z: any;\nasync function f() { while (x) { while (z) return z; } }\n",
                false,
            ),
            (
                "as-cast-lowers",
                "declare var k: any;\nfunction* g() { while ((yield k) as any) { } }\n",
                true,
            ),
            (
                "call-spread-while-test",
                "declare var f: any, x: any;\nfunction* g() { while (f(...(yield x)) < 3) { } }\n",
                false,
            ),
            (
                "method-computed-while-test",
                "declare var k: any;\nfunction* g() { while ({ [yield k]() {} }) { } }\n",
                false,
            ),
            (
                "yield-nested-lowers-with-exact-labels",
                "declare var a: any;\nfunction* g() { while (yield (yield a)) {} }\n",
                true,
            ),
            (
                "for-var-init-yield-splits",
                "declare var x: any, c: any;\nfunction* g() { for (var x = yield 1; c;) {} }\n",
                true,
            ),
            (
                "switch-case-return-refuses",
                "declare var x: any, y: any;\nfunction* g() { while (y) { switch (x) { case 1: return 42; } } }\n",
                false,
            ),
            (
                "switch-multi-yield-case-test",
                "declare var d: any, a: any, b: any, x: any;\nfunction* g() { switch (d) { case (yield a) + (yield b): x = 1; break; default: x = 2; } }\n",
                true,
            ),
            (
                "computed-key-temps-are-var-at-es5",
                "declare var x: any, k: any, o: any;\nfunction* g() { while (x) { var { [k]: v } = o; } }\n",
                true,
            ),
            ("bare-yield-lowers", "function* g() { yield; }\n", true),
            (
                "async-arrow-refusal-signals",
                "declare var x: any, y: any, z: any;\nvar f = async () => { while (x) { if (y) { await z; } } };\n",
                false,
            ),
        ];
        for (name, input, lowers) in snippets {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            let machine = code.contains("__generator(this,");
            let native = code.contains("function*");
            let diag = output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015);
            assert_eq!(
                machine, lowers,
                "[{name}] expected lower={lowers}: machine={machine} native={native}\n{code}"
            );
            if let Some(leak) = live_yield_leak(code) {
                panic!("[{name}] live yield cloned into machine: {leak}");
            }
            if let Some(leak) = raw_return_leak(code) {
                panic!("[{name}] raw return in machine body drops value: {leak}");
            }
            if !lowers {
                assert!(native, "[{name}] refusal must keep the native form\n{code}");
                assert!(diag, "[{name}] refusal must signal TS-EMIT-1102\n{code}");
            }
        }
    }

    #[test]
    fn sentinel_shapes_route_to_refusal_not_clone() {
        // WD-2: eval has no accepting arms for these shapes; the sentinel
        // count must send them there, never through the inline clone gate.
        for (name, input) in [
            (
                "tagged-template",
                "declare var tag: any, k: any;\nfunction* g() { while (tag`x ${yield k}`) { } }\n",
            ),
            (
                "type-assertion",
                "declare var k: any;\nfunction* g() { while (<any>(yield k)) { } }\n",
            ),
        ] {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            assert!(
                code.contains("function* g(")
                    && output
                        .diagnostics
                        .iter()
                        .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
                "[{name}] sentinel shape must refuse with the native form + diagnostic:\n{code}"
            );
        }
        // JSX expressions need TypeScriptReact parsing; the same sentinel
        // contract applies: refuse or lower, never a cloned live yield.
        let jsx_input = "declare var k: any;\nfunction* g() { while (<div>{yield k}</div>) { } }\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScriptReact,
            Arc::new(SourceText::new(jsx_input).expect("fits budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = &javascript(&output).code;
        assert!(
            code.contains("function* g(") || live_yield_leak(code).is_none(),
            "jsx row must refuse or lower safely, got:\n{code}"
        );
    }

    #[test]
    fn machine_case_labels_are_contiguous_and_unique() {
        // WD-3 + WD-6 + WD-7, boundaries 0/1/2/3 suspensions on both sides
        // of every count.
        for (name, input) in [
            (
                "zero",
                "declare var x: any;\nasync function f() { while (x) { } }\n",
            ),
            (
                "one",
                "declare var x: any, y: any;\nasync function f() { while (x) { await y; } }\n",
            ),
            (
                "two",
                "declare var x: any, y: any, z: any;\nasync function f() { while (x) { await y; await z; } }\n",
            ),
            (
                "three-test-split",
                "declare var o: any, k: any, y: any;\nasync function f() { while (o[await k]++ < 3) { await y; } }\n",
            ),
            (
                "import-two-suspensions",
                "declare var a: any, b: any;\nasync function f() { return import(await a, { m: await b }); }\n",
            ),
            (
                "conditional-three",
                "declare var a: any, b: any, c: any;\nasync function f() { return (await a) ? await b : await c; }\n",
            ),
            (
                "nested-yield-labels",
                "declare var a: any;\nfunction* g() { while (yield (yield a)) {} }\n",
            ),
            (
                "for-var-init-split-labels",
                "declare var x: any, c: any;\nfunction* g() { for (var x = yield 1; yield c;) { yield x; } }\n",
            ),
            (
                "jump-guard-exact-count",
                "declare var x: any, y: any, z: any;\nasync function f() { while (x) { if (y) continue; await z; } }\n",
            ),
        ] {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            let machine_switch = code
                .match_indices("switch (_")
                .map(|(i, _)| i)
                .find(|&i| code[i..].contains(".label)"));
            if machine_switch.is_none() {
                if !code.contains("__generator(this,") {
                    // Not lowered at all: the only honest alternative is a
                    // signalled refusal — a silent skip would hide a
                    // lowering regression.
                    assert!(
                        code.contains("function*")
                            && output.diagnostics.iter().any(|d| {
                                d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015
                            }),
                        "[{name}] neither machine nor signalled refusal:\n{code}"
                    );
                }
                // A degenerate zero-resume machine needs no dispatch
                // switch; there are no labels to check.
                continue;
            }
            let labels = machine_case_labels(code);
            assert!(!labels.is_empty(), "[{name}] machine without labels");
            let expected: Vec<u32> = (0..=*labels.last().expect("non-empty")).collect();
            assert_eq!(
                labels, expected,
                "[{name}] case labels must be contiguous: {code}"
            );
        }
    }

    #[test]
    fn nested_function_likes_own_suspensions_when_cloned() {
        // WD-4: a method member owns its yields, so the object clones as
        // clean into the machine and the INTERNAL yield stays legal.
        // The method body holds a real suspension: ownership means the
        // machine lowers with exactly one resume (the await) and the
        // method's yield survives verbatim inside the cloned object —
        // a walker that wrongly descended into the body would mint a
        // second resume or refuse outright.
        let output = emit_es5_clean(
            "declare var x: any;\nasync function f() {\n    while ({ *m() { yield 1; } }) { await x; }\n}\n",
        );
        let code = &javascript(&output).code;
        assert!(code.contains("__generator(this,"), "lowers: {code}");
        assert!(
            code.contains("m: function* () {"),
            "generator method cloned intact: {code}"
        );
        assert!(code.contains("yield 1;"), "method owns its yield: {code}");
        assert_eq!(
            code.matches(".sent()").count(),
            1,
            "one machine resume: {code}"
        );
        assert_eq!(
            code.matches("function* (").count(),
            1,
            "only the method stays native: {code}"
        );
    }

    #[test]
    fn non_block_loop_bodies_refuse() {
        // WD-5: single-statement bodies are outside the accepted set; the
        // only valid outcomes are refusal with a diagnostic.
        for (name, input) in [
            (
                "while",
                "declare var x: any, y: any;\nasync function f() { while (x) await y; }\n",
            ),
            (
                "for",
                "declare var x: any, y: any;\nasync function f() { for (; x;) await y; }\n",
            ),
            (
                "do",
                "declare var x: any, y: any;\nasync function f() { do await y; while (x); }\n",
            ),
        ] {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            assert!(
                !code.contains("__generator(this,")
                    && code.contains("function*")
                    && output
                        .diagnostics
                        .iter()
                        .any(|d| { d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015 }),
                "[{name}] non-block body must refuse with the diagnostic, never lower or clone: {code}"
            );
        }
    }

    #[test]
    fn labeled_nested_await_delegation_refuses_until_nested_if_slice() {
        // WD-8: branch_awaits delegates through nested statement shapes.
        let output = emit_es5_clean(
            "declare var x: any, y: any, z: any;\nasync function f() {\n    A: while (x) { if (y) { await z; break A; } }\n}\n",
        );
        let code = &javascript(&output).code;
        // Safety contract: refuse-or-lower, never a live await cloned
        // outside the generator that owns it. (Full lowering of nested
        // control flow inside labeled loop bodies is a banked machine
        // slice; until then the refusal form is the correct output.)
        assert!(
            code.contains("function*") || code.contains("__generator(this,"),
            "must refuse or lower: {code}"
        );
        assert!(live_yield_leak(code).is_none(), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must signal: {:?}",
            output.diagnostics
        );
    }

    #[test]
    fn deep_nesting_walkers_do_not_crash() {
        // WD-9: the parser's nesting bound (MAX_DEPTH = 256) is the
        // boundary, tested from both sides. Below it the fixture parses
        // clean and the recursive walkers emit some form; above it the
        // parser declines with the descriptive P010 diagnostic — never a
        // crash, never a silent skip. (A `-` chain lexes as `--` decrement
        // pairs and never parses; parens give real expression depth.)
        let fixture = |depth: usize| {
            format!(
                "declare var y: any;\nasync function f() {{ {}await y{}; }}\n",
                "(".repeat(depth),
                ")".repeat(depth)
            )
        };
        let parse = |input: String| {
            crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input.as_str()).expect("fits budget")),
            ))
        };
        let below = parse(fixture(56));
        assert!(
            below.diagnostics().is_empty(),
            "depth 56 must parse clean: {:?}",
            below.diagnostics()
        );
        let output = emit_output(
            below.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = &javascript(&output).code;
        assert!(
            code.contains("__generator(this,") || code.contains("function*"),
            "some emitted form at depth 56: {code}"
        );
        let above = parse(fixture(400));
        assert!(
            !above.diagnostics().is_empty(),
            "depth 400 must be rejected, not accepted"
        );
        assert!(
            above
                .diagnostics()
                .iter()
                .any(|d| d.code().as_str().contains("P010")),
            "rejection must be the descriptive nesting-bound diagnostic: {:?}",
            above.diagnostics()
        );
    }
    fn emit_left_deep_chain(
        first: impl FnOnce(&mut Builder) -> Expr,
        link: impl Fn(&mut Builder, Expr, usize) -> Expr,
    ) -> String {
        let mut builder = Builder::new();
        let mut chain = first(&mut builder);
        for index in 1..20000 {
            chain = link(&mut builder, chain, index);
        }
        let file = builder.finish(vec![expr_stmt(chain)]);
        let empty_recovered = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new("").expect("fits")),
        ));
        let empty_checked = crate::checker::check(&empty_recovered);
        let model = empty_checked.product();
        let output = emit_checked(
            &file,
            model,
            &EmitOptions {
                target: ScriptTarget::EsNext,
                remove_comments: true,
                ..EmitOptions::default()
            },
            &EmitFileNames::default(),
        );
        javascript(&output).code.clone()
    }

    #[test]
    fn left_deep_binary_chain_emits_without_overflow() {
        let code = emit_left_deep_chain(
            |builder| builder.number("0"),
            |builder, left, index| {
                let right = builder.number(&index.to_string());
                binary(BinaryOperator::Add, left, right)
            },
        );
        assert!(code.starts_with("0 + 1 + 2"), "{code}");
        assert!(code.trim_end().ends_with("19999;"), "{code}");
        assert_eq!(code.matches(" + ").count(), 19999, "{code}");
    }

    #[test]
    fn left_deep_logical_chain_of_reads_emits_without_overflow() {
        let code = emit_left_deep_chain(
            |builder| builder.ident_expr("x0"),
            |builder, left, index| {
                let right = builder.ident_expr(&format!("x{index}"));
                expr(Expression::Logical(LogicalExpression {
                    operator: LogicalOperator::Or,
                    left: Box::new(left),
                    right: Box::new(right),
                }))
            },
        );
        assert!(code.starts_with("x0 || x1 || x2"), "{code}");
        assert!(code.trim_end().ends_with("x19999;"), "{code}");
        assert_eq!(code.matches(" || ").count(), 19999, "{code}");
    }

    #[test]
    fn left_deep_member_chain_emits_without_overflow() {
        let code = emit_left_deep_chain(
            |builder| builder.ident_expr("x"),
            |builder, object, _| {
                builder.token(TokenKind::Dot, ".");
                let name = builder.ident("p");
                expr(Expression::Member(MemberExpression {
                    object: Box::new(object),
                    property: MemberProperty::Named(name),
                    optional: false,
                }))
            },
        );
        assert!(code.starts_with("x.p.p"), "{code}");
        assert_eq!(code.matches(".p").count(), 19999, "{code}");
    }

    #[test]
    fn left_deep_call_chain_emits_without_overflow() {
        let code = emit_left_deep_chain(
            |builder| builder.ident_expr("f"),
            |builder, callee, index| {
                let argument = builder.number(&index.to_string());
                expr(Expression::Call(CallExpression {
                    callee: Box::new(callee),
                    optional: false,
                    type_arguments: None,
                    arguments: vec![CallArgument::Expression(Box::new(argument))],
                }))
            },
        );
        assert!(code.starts_with("f(1)(2)(3)"), "{code}");
        assert!(code.trim_end().ends_with("(19999);"), "{code}");
        assert_eq!(code.matches(")(").count(), 19998, "{code}");
    }

    #[test]
    fn es5_generator_import_source_materializes_before_options_yield() {
        // A clean source operand with side effects must run before the
        // options suspend: materialize into a temp in the pre-suspension
        // segment, never reassemble it inside the resume where its effects
        // would slip past the suspension.
        let output = emit_es5_clean(
            "declare var f: any, b: any;\nfunction* g() { return import(f(), { m: yield b }); }\n",
        );
        let code = &javascript(&output).code;
        let case0 = code
            .split("case 0:")
            .nth(1)
            .and_then(|rest| rest.split("case 1:").next())
            .expect("two segments");
        let source_pos = case0.find("_a = f();").expect("source temp");
        let yield_pos = case0.find("/*yield*/").expect("split marker");
        assert!(
            source_pos < yield_pos,
            "source materializes before the yield: {code}"
        );
        assert!(
            code.contains("import(_a,"),
            "resume reassembles from the temp: {code}"
        );
    }

    #[test]
    fn es5_async_nested_async_arrow_keeps_its_awaits() {
        // A nested async arrow owns its awaits: the outer function's
        // await-to-yield rewrite must stop at the nested body, and the
        // nested arrow keeps its own `await` for its own lowering pass.
        // (Await inside a NON-async function is invalid input the parser
        // does not yet reject — banked as a checker slice.)
        let output = emit_es5_clean(
            "declare var k: any;\nasync function f() { var g = async () => { return await k; }; }\n",
        );
        let code = &javascript(&output).code;
        // The nested arrow lowers itself: its own __awaiter machine with
        // the await in protocol form ([4 /*yield*/, k]) — no live yield.
        assert_eq!(
            code.matches("__awaiter").count(),
            2,
            "both the outer function and the nested arrow lower: {code}"
        );
        assert!(code.contains("/*yield*/, k"), "protocol form: {code}");
        assert!(live_yield_leak(code).is_none(), "{code}");
    }

    #[test]
    fn machine_state_name_terminates_past_the_alphabet() {
        // Declaring _a.._z plus _state exhausted the old allocator's fixed
        // fallback and hung compilation forever. A regression must fail
        // this test, not wedge the runner, so the emit runs on a thread
        // with a hard timeout.
        // The skip set is built from BODY statements, so the alphabet must
        // be declared inside the generator, not as ambient `declare var`.
        let input = "function* g() { var _a, _b, _c, _d, _e, _f, _g, _h, _i, _j, _k, _l, _m, _n, _o, _p, _q, _r, _s, _t, _u, _v, _w, _x, _y, _z, _state; yield 1; }\n";
        let (tx, rx) = std::sync::mpsc::channel();
        let parsed_input = input.to_owned();
        std::thread::spawn(move || {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(parsed_input.as_str()).expect("fits budget")),
            ));
            let output = emit_output(
                parsed.product(),
                &EmitOptions {
                    target: ScriptTarget::Es5,
                    no_emit_helpers: true,
                    ..EmitOptions::default()
                },
            );
            let _ = tx.send(javascript(&output).code.clone());
        });
        let code = rx
            .recv_timeout(std::time::Duration::from_secs(10))
            .expect("allocator must terminate past the alphabet");
        assert!(code.contains("__generator(this,"), "{code}");
    }
