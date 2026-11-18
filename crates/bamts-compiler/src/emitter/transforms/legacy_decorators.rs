//! Legacy decorators (`experimentalDecorators`): `__decorate` calls replace the
//! decorator syntax.
//!
//! A decorated class becomes `let C = class C {};` followed by the members'
//! `__decorate([...], C.prototype, "m", null);` calls and then
//! `C = __decorate([...], C);`. Class bodies keep their `class` syntax, so
//! only targets that have classes take this path.

use crate::source::TextRange;
use crate::syntax::*;

use super::helpers::HelperKind;
use super::{ExportWrapper, LanguageFeature, Rewriter};

struct Decorations {
    member_statements: Vec<Stmt>,
    class_decorators: Vec<Expr>,
}

fn parameters_decorated(parameters: &[ParameterNode]) -> bool {
    parameters
        .iter()
        .any(|parameter| !parameter.data().decorators.is_empty())
}

pub(super) fn is_decorated(class: &ClassDeclaration) -> bool {
    !class.decorators.is_empty()
        || class.members.iter().any(|member| match member.data() {
            ClassMember::Constructor(constructor) => parameters_decorated(&constructor.parameters),
            ClassMember::Method(method) => {
                !method.function.decorators.is_empty()
                    || parameters_decorated(&method.function.parameters)
            }
            ClassMember::Property(property) => !property.decorators.is_empty(),
            _ => false,
        })
}

fn strip_parameter_decorators(parameters: Vec<ParameterNode>) -> Vec<ParameterNode> {
    parameters
        .into_iter()
        .map(|parameter| {
            let (id, range) = (parameter.id(), parameter.range());
            let mut data = parameter.into_data();
            data.decorators = Vec::new();
            Node::new(id, range, data)
        })
        .collect()
}

fn decorator_expressions(decorators: &[DecoratorNode]) -> Vec<Expr> {
    decorators
        .iter()
        .map(|decorator| (*decorator.data().expression).clone())
        .collect()
}

impl Rewriter<'_> {
    /// Lowers a class whose decorators `experimentalDecorators` turns into
    /// `__decorate` calls; `None` when this class needs no such lowering.
    pub(super) fn lower_legacy_decorated_class(
        &mut self,
        range: TextRange,
        class_range: TextRange,
        class: &ClassDeclaration,
        export: ExportWrapper,
    ) -> Option<Vec<Stmt>> {
        if !self.options.experimental_decorators
            || Self::needs(LanguageFeature::Classes, self.options)
            || !is_decorated(class)
        {
            return None;
        }
        let mut class = class.clone();
        let anonymous = class.name.is_none();
        let (name, name_text) = match &class.name {
            Some(name) => (
                name.clone(),
                self.token_text(name.data().token()).to_owned(),
            ),
            None => (self.ident("default_1"), String::from("default_1")),
        };
        class.name = Some(name.clone());
        let decorations = self.take_decorations(&mut class, &name, class_range);
        let decorated = !decorations.class_decorators.is_empty();
        let alias = if decorated && !anonymous {
            self.alias_class_self_references(&mut class, &name)
        } else {
            None
        };
        let mut lowered = self.lower_class(&class, class_range, None);
        if anonymous && lowered.postlude.is_empty() {
            lowered.class.name = None;
        }
        let mut out = Vec::new();
        if let Some(alias) = &alias {
            out.extend(self.temp_declaration(vec![alias.clone()], class_range));
        }
        out.extend(lowered.prelude);
        let class_statement = if decorated {
            self.class_let(&name, alias.as_ref(), lowered.class, class_range)
        } else {
            self.plain_class_statement(range, class_range, lowered.class, export)
        };
        out.push(class_statement);
        if self.cjs.is_some() && export == ExportWrapper::Named {
            out.push(self.cjs_export_assignment(&name_text, &name_text, range));
        }
        out.extend(lowered.postlude);
        out.extend(decorations.member_statements);
        if decorated {
            let call = self.decorate_call(decorations.class_decorators, &name, None, range);
            out.push(self.class_decoration(&name, alias.as_ref(), &name_text, call, export, range));
        }
        out.extend(self.export_tail(&name, &name_text, export, decorated, range));
        Some(out)
    }

    /// The `__decorate` statements an ES5 class carries inside its function,
    /// after the lowered members and before the class is returned.
    pub(super) fn es5_class_decorations(
        &mut self,
        class: &mut ClassDeclaration,
        name: &IdentifierNode,
        name_text: &str,
        range: TextRange,
    ) -> Vec<Stmt> {
        let decorations = self.take_decorations(class, name, range);
        let mut statements = decorations.member_statements;
        if !decorations.class_decorators.is_empty() {
            let call = self.decorate_call(decorations.class_decorators, name, None, range);
            statements.push(self.class_decoration(
                name,
                None,
                name_text,
                call,
                ExportWrapper::None,
                range,
            ));
        }
        statements
    }

    fn plain_class_statement(
        &mut self,
        range: TextRange,
        class_range: TextRange,
        class: ClassDeclaration,
        export: ExportWrapper,
    ) -> Stmt {
        let exported_in_esm = self.cjs.is_none();
        match export {
            ExportWrapper::Named if exported_in_esm => {
                let statement = self.node(class_range, Statement::Class(class));
                self.node(
                    range,
                    Statement::Export(ExportDeclaration::Named(
                        ExportNamedDeclaration::Declaration(Box::new(statement)),
                    )),
                )
            }
            ExportWrapper::Default if exported_in_esm => self.node(
                range,
                Statement::Export(ExportDeclaration::Default(ExportDefaultDeclaration {
                    value: ExportDefaultValue::Class(class),
                })),
            ),
            _ => self.node(class_range, Statement::Class(class)),
        }
    }

    fn class_let(
        &mut self,
        name: &IdentifierNode,
        alias: Option<&IdentifierNode>,
        class: ClassDeclaration,
        range: TextRange,
    ) -> Stmt {
        let mut value = self.node(range, Expression::Class(ClassExpression { class }));
        if let Some(alias) = alias {
            value = self.store_temp(alias, value, range);
        }
        let declarator = self.make_declarator(name.clone(), Some(value), range);
        self.syn_node(
            range,
            Statement::Variable(VariableDeclaration {
                range,
                kind: VariableKind::Let,
                declarations: vec![declarator],
            }),
        )
    }

    /// `C = __decorate([...], C);`, with the class alias assigned inside it
    /// (`C = C_1 = __decorate(...)`) and the CommonJS export outside it
    /// (`exports.C = C = __decorate(...)`).
    fn class_decoration(
        &mut self,
        name: &IdentifierNode,
        alias: Option<&IdentifierNode>,
        name_text: &str,
        call: Expr,
        export: ExportWrapper,
        range: TextRange,
    ) -> Stmt {
        let mut value = call;
        if let Some(alias) = alias {
            value = self.store_temp(alias, value, range);
        }
        value = self.store_temp(name, value, range);
        if self.cjs.is_some() && export == ExportWrapper::Named {
            value = self.cjs_assign_exports(&[name_text.to_owned()], value, range);
        }
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(value),
            }),
        )
    }

    /// The alias `C_1` a decorated class's body reads in place of `C`, which
    /// the decorators rebind after the class is built; `None` when the body
    /// never names the class.
    fn alias_class_self_references(
        &mut self,
        class: &mut ClassDeclaration,
        name: &IdentifierNode,
    ) -> Option<IdentifierNode> {
        let original = self.identifier_name(name)?;
        let symbol = self.model.and_then(|model| model.reference(name.id()));
        let members = std::mem::take(&mut class.members);
        let probe = self.ident("_");
        let probed = self.rename_class_self_in_members(members.clone(), &original, symbol, &probe);
        if probed == members {
            class.members = members;
            return None;
        }
        let alias = self.source_name_ident(&original);
        class.members = self.rename_class_self_in_members(members, &original, symbol, &alias);
        Some(alias)
    }

    /// The export statement that follows a class the lowering turned into a
    /// `let` binding, or the CommonJS default assignment.
    fn export_tail(
        &mut self,
        name: &IdentifierNode,
        name_text: &str,
        export: ExportWrapper,
        decorated: bool,
        range: TextRange,
    ) -> Vec<Stmt> {
        match (export, self.cjs.is_some()) {
            (ExportWrapper::Default, true) => {
                let value = self.ident_expr(name_text);
                vec![self.cjs_export_default_assignment(range, value)]
            }
            (ExportWrapper::Default, false) if decorated => {
                let value = self.node(range, Expression::Identifier(name.clone()));
                vec![self.node(
                    range,
                    Statement::Export(ExportDeclaration::Default(ExportDefaultDeclaration {
                        value: ExportDefaultValue::Expression(Box::new(value)),
                    })),
                )]
            }
            (ExportWrapper::Named, false) if decorated => {
                vec![self.export_specifier_statement(name, range)]
            }
            _ => Vec::new(),
        }
    }

    fn export_specifier_statement(&mut self, name: &IdentifierNode, range: TextRange) -> Stmt {
        let specifier = self.node(
            range,
            ExportSpecifier {
                mode: ExportSpecifierMode::Value,
                local: ModuleExportName::Identifier(name.clone()),
                exported: ModuleExportName::Identifier(name.clone()),
            },
        );
        self.node(
            range,
            Statement::Export(ExportDeclaration::Named(
                ExportNamedDeclaration::Specifiers {
                    type_only: false,
                    specifiers: vec![specifier],
                    source: None,
                    attributes: None,
                },
            )),
        )
    }

    /// Removes every decorator from the class and returns the `__decorate`
    /// statements for its members and the decorator list for the class.
    fn take_decorations(
        &mut self,
        class: &mut ClassDeclaration,
        name: &IdentifierNode,
        range: TextRange,
    ) -> Decorations {
        let mut class_decorators = decorator_expressions(&class.decorators);
        class.decorators = Vec::new();
        let mut instance_statements = Vec::new();
        let mut static_statements = Vec::new();
        let members = std::mem::take(&mut class.members);
        let mut rebuilt = Vec::with_capacity(members.len());
        for member in members {
            let (id, member_range) = (member.id(), member.range());
            let data = match member.into_data() {
                ClassMember::Constructor(mut constructor) => {
                    for (index, parameter) in constructor.parameters.iter().enumerate() {
                        class_decorators.extend(self.parameter_decorators(index, parameter));
                    }
                    constructor.decorators = Vec::new();
                    constructor.parameters = strip_parameter_decorators(constructor.parameters);
                    ClassMember::Constructor(constructor)
                }
                ClassMember::Method(mut method) => {
                    let mut decorators = Vec::new();
                    if method.function.body.is_some() {
                        decorators = decorator_expressions(&method.function.decorators);
                        for (index, parameter) in method.function.parameters.iter().enumerate() {
                            decorators.extend(self.parameter_decorators(index, parameter));
                        }
                    }
                    if !decorators.is_empty() {
                        let statement = self.member_decoration(
                            name,
                            &method.name,
                            method.modifiers.is_static,
                            decorators,
                            false,
                            range,
                        );
                        match statement {
                            Some(statement) if method.modifiers.is_static => {
                                static_statements.push(statement);
                            }
                            Some(statement) => instance_statements.push(statement),
                            None => {}
                        }
                    }
                    method.function.decorators = Vec::new();
                    method.function.parameters =
                        strip_parameter_decorators(method.function.parameters);
                    ClassMember::Method(method)
                }
                ClassMember::Property(mut property) => {
                    let decorators = decorator_expressions(&property.decorators);
                    if !decorators.is_empty() {
                        let statement = self.member_decoration(
                            name,
                            &property.name,
                            property.modifiers.is_static,
                            decorators,
                            true,
                            range,
                        );
                        match statement {
                            Some(statement) if property.modifiers.is_static => {
                                static_statements.push(statement);
                            }
                            Some(statement) => instance_statements.push(statement),
                            None => {}
                        }
                    }
                    property.decorators = Vec::new();
                    ClassMember::Property(property)
                }
                other => other,
            };
            rebuilt.push(Node::new(id, member_range, data));
        }
        class.members = rebuilt;
        instance_statements.extend(static_statements);
        Decorations {
            member_statements: instance_statements,
            class_decorators,
        }
    }

    /// `__param(index, decorator)` for each decorator on one parameter.
    fn parameter_decorators(&mut self, index: usize, parameter: &ParameterNode) -> Vec<Expr> {
        let range = parameter.range();
        decorator_expressions(&parameter.data().decorators)
            .into_iter()
            .map(|decorator| {
                let callee = self.helper_ident(HelperKind::Param);
                let position = self.number_expr(&index.to_string());
                self.call_expression(range, callee, vec![position, decorator])
            })
            .collect()
    }

    /// `__decorate([...], C.prototype, "m", null);` for one decorated member.
    fn member_decoration(
        &mut self,
        class: &IdentifierNode,
        name: &PropertyName,
        is_static: bool,
        decorators: Vec<Expr>,
        is_property: bool,
        range: TextRange,
    ) -> Option<Stmt> {
        let key = self.decoration_key(name)?;
        let target = self.node(range, Expression::Identifier(class.clone()));
        let target = if is_static {
            target
        } else {
            self.member_access(target, "prototype", range)
        };
        let descriptor = if is_property {
            self.void_zero(range)
        } else {
            self.null_expr()
        };
        let callee = self.helper_ident(HelperKind::Decorate);
        let array = self.decorator_array(decorators, range);
        let call = self.call_expression(range, callee, vec![array, target, key, descriptor]);
        Some(self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        ))
    }

    fn decoration_key(&mut self, name: &PropertyName) -> Option<Expr> {
        match name {
            PropertyName::Identifier(identifier) => {
                let text = self.token_text(identifier.data().token()).to_owned();
                let literal = self.string_literal(&text);
                let range = literal.range();
                Some(self.node(range, Expression::Literal(Literal::String(literal))))
            }
            PropertyName::String(literal) => Some(self.node(
                literal.range(),
                Expression::Literal(Literal::String(literal.clone())),
            )),
            PropertyName::Number(literal) => Some(self.node(
                literal.range(),
                Expression::Literal(Literal::Number(literal.clone())),
            )),
            PropertyName::Private(_) | PropertyName::Computed(_) | PropertyName::Missing(_) => None,
        }
    }

    /// `__decorate([...], C)` for the class itself.
    fn decorate_call(
        &mut self,
        decorators: Vec<Expr>,
        class: &IdentifierNode,
        key: Option<Expr>,
        range: TextRange,
    ) -> Expr {
        let callee = self.helper_ident(HelperKind::Decorate);
        let array = self.decorator_array(decorators, range);
        let target = self.node(range, Expression::Identifier(class.clone()));
        let mut arguments = vec![array, target];
        arguments.extend(key);
        self.call_expression(range, callee, arguments)
    }

    /// The decorator list, printed one decorator per line.
    fn decorator_array(&mut self, decorators: Vec<Expr>, range: TextRange) -> Expr {
        let elements = decorators
            .into_iter()
            .map(|decorator| ArrayElement::Expression(Box::new(decorator)))
            .collect();
        let array = self.node(range, Expression::Array(ArrayLiteral { elements }));
        self.expanded_sequences.insert(array.id());
        array
    }
}
