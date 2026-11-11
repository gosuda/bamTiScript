//! ECMAScript early errors for JavaScript the engine is about to run.
//!
//! `tsc` reports these differently, or not at all, and its diagnostics are held
//! to the TypeScript baselines, so this pass is not part of the compiler's
//! diagnostics. It runs only when a JavaScript source is compiled for execution,
//! where a program the specification calls invalid must never start.
//!
//! Every rule here is a static-semantics rule of the specification. A rule that
//! cannot be decided from the tree is left out: rejecting a valid program is
//! worse than running an invalid one, because the second fails anyway.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    diagnostic::{Diagnostic, DiagnosticCode},
    source::{TextRange, Utf16Pos},
    syntax::{
        ArrayBindingElement, ArrayElement, AssignmentArrayElement, AssignmentOperator,
        AssignmentTarget, AssignmentTargetNode, BinaryOperator, BindingPattern, BlockNode,
        CallArgument, ClassDeclaration, ClassMember, ExportDeclaration, ExportDefaultValue,
        ExportNamedDeclaration, Expr, Expression, ForBinding, ForInitializer, FunctionBody,
        FunctionLike, IdentifierNode, ImportBinding, ImportDeclaration, ImportSpecifierMode,
        Literal, LogicalOperator, MemberProperty, MetaProperty, ObjectMember, ParameterNode,
        Pattern, PrivateIdentifierNode, PropertyModifier, PropertyName, SourceFile, Statement,
        Stmt, Token, TokenKind, UnaryOperator, VariableKind,
    },
};

/// A program the specification rejects before it runs.
pub const EARLY_ERROR: DiagnosticCode = DiagnosticCode::new("BAMTS-P019");

/// Words reserved in strict code that the scanner reads as identifiers.
const STRICT_RESERVED: [&str; 9] = [
    "implements",
    "interface",
    "let",
    "package",
    "private",
    "protected",
    "public",
    "static",
    "yield",
];

/// Words no identifier can spell, even with escapes.
const RESERVED: [&str; 37] = [
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "null",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
];

/// Reports every early error in `file`.
#[must_use]
pub fn check(file: &SourceFile) -> Vec<Diagnostic> {
    let module = is_module(file);
    walk(
        file,
        Context {
            strict: module || has_use_strict(file, file.statements()),
            module,
            // The host did not name a goal, and top-level `await` implies one.
            top_level_await: true,
            ..Context::default()
        },
    )
}

/// Reports every early error in `file`, which the host runs as a Script, so
/// module syntax is one more of them.
#[must_use]
pub fn check_script(file: &SourceFile) -> Vec<Diagnostic> {
    let mut errors = walk(
        file,
        Context {
            strict: has_use_strict(file, file.statements()),
            script: true,
            ..Context::default()
        },
    );
    errors.extend(
        file.statements()
            .iter()
            .filter(|statement| {
                matches!(
                    statement.data(),
                    Statement::Import(_) | Statement::Export(_)
                )
            })
            .map(|statement| {
                Diagnostic::error(
                    EARLY_ERROR,
                    file.source_id(),
                    statement.range(),
                    "module syntax is not allowed in a script",
                )
            }),
    );
    errors
}

fn walk(file: &SourceFile, context: Context) -> Vec<Diagnostic> {
    let mut walker = Walker {
        file,
        errors: Vec::new(),
        labels: Vec::new(),
        private_scopes: Vec::new(),
    };
    let program = Context {
        program_level: true,
        ..context
    };
    walker.scope(file.statements(), ScopeKind::Program, program);
    walker.errors
}

/// What the surrounding code allows at the node being walked.
#[derive(Clone, Copy, Debug, Default)]
struct Context {
    /// A statement of the program itself, where `import` and `export` belong.
    program_level: bool,
    strict: bool,
    module: bool,
    /// The host named the goal, so `import.meta` is decidable.
    script: bool,
    /// Inside a function body, where `return` is available.
    in_function: bool,
    /// At the top of a module, where `await` needs no async function.
    top_level_await: bool,
    /// Inside an async arrow's parameters, through any arrow nested there.
    async_parameters: bool,
    generator: bool,
    /// An arrow inside a generator. Its parameters keep the rules of the
    /// generator for `yield`, and its body does not.
    arrow_in_generator: bool,
    is_async: bool,
    in_parameters: bool,
    /// Inside a class field initializer or static block, where `arguments` is
    /// not available.
    class_initializer: bool,
    static_block: bool,
    super_call: bool,
    super_property: bool,
    new_target: bool,
    in_iteration: bool,
    in_switch: bool,
    /// Arrows and methods never allow a repeated parameter, even in sloppy code.
    unique_parameters: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScopeKind {
    Program,
    Function,
    Block,
}

/// How a private name is declared, which decides what may share it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PrivateKind {
    Getter { is_static: bool },
    Setter { is_static: bool },
    Other,
}

/// One class body's private names, and references it could not yet resolve.
#[derive(Default)]
struct PrivateScope {
    declared: BTreeSet<String>,
    unresolved: Vec<(String, TextRange)>,
}

struct Lexical {
    name: String,
    range: TextRange,
    plain_function: bool,
}

struct Walker<'a> {
    file: &'a SourceFile,
    errors: Vec<Diagnostic>,
    labels: Vec<(String, bool)>,
    private_scopes: Vec<PrivateScope>,
}

/// Whether `file` has the module goal, which only its own syntax can tell.
pub(crate) fn is_module(file: &SourceFile) -> bool {
    file.statements().iter().any(|statement| {
        matches!(
            statement.data(),
            Statement::Import(_) | Statement::Export(_)
        )
    })
}

pub(crate) fn has_use_strict(file: &SourceFile, statements: &[Stmt]) -> bool {
    directives(statements).any(|token| {
        file.token_text(token)
            .is_some_and(|text| text == "'use strict'" || text == "\"use strict\"")
    })
}

/// The string tokens of a directive prologue, in order.
fn directives(statements: &[Stmt]) -> impl Iterator<Item = &crate::syntax::Token> {
    statements.iter().map_while(|statement| {
        let Statement::Expression(expression) = statement.data() else {
            return None;
        };
        let Expression::Literal(Literal::String(literal)) = expression.expression.data() else {
            return None;
        };
        Some(literal.data().token())
    })
}

/// The body statements of `pattern`'s statement, when it is a labeled function.
fn unlabeled(statement: &Stmt) -> &Stmt {
    match statement.data() {
        Statement::Labeled(labeled) => unlabeled(&labeled.body),
        _ => statement,
    }
}

/// The declaration `statement` exports, or `statement` when it exports none.
fn unexported(statement: &Stmt) -> &Stmt {
    match statement.data() {
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) => {
            inner
        }
        _ => statement,
    }
}

const fn is_iteration(statement: &Statement) -> bool {
    matches!(
        statement,
        Statement::For(_)
            | Statement::ForIn(_)
            | Statement::ForOf(_)
            | Statement::While(_)
            | Statement::DoWhile(_)
    )
}

/// The significant token at or after `position`.
fn next_token(file: &SourceFile, position: Utf16Pos) -> Option<&Token> {
    let tokens = file.tokens();
    let start = tokens.partition_point(|token| token.range().start() < position);
    tokens[start..].iter().find(|token| !is_trivia(token))
}

/// The last significant token before `position`.
fn previous_token(file: &SourceFile, position: Utf16Pos) -> Option<&Token> {
    let tokens = file.tokens();
    let end = tokens.partition_point(|token| token.range().start() < position);
    tokens[..end].iter().rev().find(|token| !is_trivia(token))
}

/// Whether parentheses wrap `range`, which the tree drops from a target.
pub(crate) fn is_parenthesized(file: &SourceFile, range: TextRange) -> bool {
    previous_token(file, range.start()).is_some_and(|token| token.kind() == TokenKind::LParen)
        && next_token(file, range.end()).is_some_and(|token| token.kind() == TokenKind::RParen)
}

fn is_trivia(token: &Token) -> bool {
    matches!(
        token.kind(),
        TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
    )
}

/// Whether `text` holds an octal or `\\8`-style escape, which strict code and
/// every untagged template refuse. `\\0` alone is the null character.
fn has_legacy_escape(text: &str) -> bool {
    let mut characters = text.chars().peekable();
    while let Some(character) = characters.next() {
        if character != '\\' {
            continue;
        }
        match characters.next() {
            Some('1'..='9') => return true,
            Some('0') if characters.peek().is_some_and(char::is_ascii_digit) => return true,
            _ => {}
        }
    }
    false
}

/// Whether a member chain passes through `?.`. A tag cannot do this, and a call
/// that does is not an assignment target, even at run time. A `!` stays in the
/// chain: TypeScript erases it.
pub(crate) fn in_optional_chain(expression: &Expr) -> bool {
    match expression.data() {
        Expression::Member(member) => member.optional || in_optional_chain(&member.object),
        Expression::Call(call) => call.optional || in_optional_chain(&call.callee),
        Expression::NonNull(non_null) => in_optional_chain(&non_null.expression),
        _ => false,
    }
}

/// A number with a leading `0` and a digit, which strict code does not allow.
fn is_legacy_octal_number(text: &str) -> bool {
    text.len() > 1 && text.starts_with('0') && text.as_bytes()[1].is_ascii_digit()
}

const fn is_mixed_logical(outer: LogicalOperator, inner: LogicalOperator) -> bool {
    matches!(outer, LogicalOperator::Nullish) != matches!(inner, LogicalOperator::Nullish)
}

/// Whether `expression` reads through an `import()` call, which `new` cannot
/// apply to at any depth of a member chain.
fn rooted_in_import(expression: &Expr) -> bool {
    match expression.data() {
        Expression::Import(_) => true,
        Expression::Member(member) => rooted_in_import(&member.object),
        _ => false,
    }
}

pub(crate) fn strip_parentheses(expression: &Expr) -> &Expr {
    match expression.data() {
        Expression::Parenthesized(inner) => strip_parentheses(inner),
        _ => expression,
    }
}

impl Walker<'_> {
    fn error(&mut self, range: TextRange, message: &'static str) {
        self.errors.push(Diagnostic::error(
            EARLY_ERROR,
            self.file.source_id(),
            range,
            message,
        ));
    }

    /// Whether a comma follows `range`, which a rest element cannot have.
    /// Whether a comma follows `range`. A parenthesized target ends before its `)`.
    fn comma_follows(&self, range: TextRange) -> bool {
        let mut end = range.end();
        while let Some(token) = next_token(self.file, end) {
            if token.kind() != TokenKind::RParen {
                return token.kind() == TokenKind::Comma;
            }
            end = token.range().end();
        }
        false
    }

    fn token_of(&self, token: &Token) -> &str {
        self.file.token_text(token).unwrap_or_default()
    }

    /// The word after `import.` or `new.`, exactly as written.
    fn meta_word(&self, expression: &Expr) -> &str {
        previous_token(self.file, expression.range().end())
            .and_then(|token| self.file.token_text(token))
            .unwrap_or_default()
    }

    /// Whether `callee` is `import.defer` or `import.source`, which exist only
    /// as the callee of a call. The parser reads every `import.x` as a meta
    /// property, as `tsc` does, so the word is all that tells them apart.
    fn is_import_phase(&self, callee: &Expr) -> bool {
        matches!(callee.data(), Expression::Meta(MetaProperty::ImportMeta))
            && matches!(self.meta_word(callee), "defer" | "source")
    }

    fn import_phase_call(
        &mut self,
        arguments: &[CallArgument],
        range: TextRange,
        context: Context,
    ) {
        if !(1..=2).contains(&arguments.len())
            || arguments
                .iter()
                .any(|argument| matches!(argument, CallArgument::Spread(_)))
        {
            self.error(range, "an import call takes a specifier and options");
        }
        self.arguments(arguments, context);
    }

    fn name(&self, identifier: &IdentifierNode) -> String {
        self.file
            .identifier_text(identifier.data().token())
            .map_or_else(String::new, std::borrow::Cow::into_owned)
    }

    /// A private name as it compares: `#\u{6F}` and `#o` are the same name.
    fn private_name(&self, private: &PrivateIdentifierNode) -> String {
        Self::cooked_private(
            self.file
                .token_text(private.data().token())
                .unwrap_or_default(),
        )
    }

    fn cooked_private(text: &str) -> String {
        let tail = text.strip_prefix('#').unwrap_or(text);
        let cooked = crate::syntax::cook_identifier_text(tail);
        format!("#{}", cooked.as_deref().unwrap_or(tail))
    }

    fn property_text(&self, name: &PropertyName) -> Option<String> {
        match name {
            PropertyName::Identifier(identifier) => Some(self.name(identifier)),
            PropertyName::String(literal) => self
                .file
                .token_text(literal.data().token())
                .and_then(crate::literal::string_value)
                .map(|value| value.to_utf8_lossy()),
            _ => None,
        }
    }

    // --- Names -----------------------------------------------------------

    fn check_identifier(&mut self, name: &str, range: TextRange, context: Context) {
        if name != "yield" && RESERVED.contains(&name) {
            self.error(range, "a reserved word cannot name anything");
        }
        if context.strict && STRICT_RESERVED.contains(&name) {
            self.error(range, "this name is reserved in strict mode code");
        }
        if name == "yield" && context.generator {
            self.error(range, "`yield` cannot name anything in a generator");
        }
        if name == "await"
            && (context.is_async
                || context.module
                || context.static_block
                || context.async_parameters)
        {
            self.error(range, "`await` cannot name anything here");
        }
    }

    fn check_binding(&mut self, name: &str, range: TextRange, context: Context) {
        self.check_identifier(name, range, context);
        if context.strict && (name == "eval" || name == "arguments") {
            self.error(
                range,
                "`eval` and `arguments` cannot be bound in strict mode",
            );
        }
    }

    fn reference(&mut self, identifier: &IdentifierNode, context: Context) {
        let token = self
            .file
            .token_text(identifier.data().token())
            .unwrap_or_default();
        if token.starts_with('#') {
            self.error(identifier.range(), "a private name needs `in` after it");
            return;
        }
        let name = self.name(identifier);
        self.check_identifier(&name, identifier.range(), context);
        if name == "arguments" && context.class_initializer {
            self.error(
                identifier.range(),
                "`arguments` is not available in a class initializer",
            );
        }
    }

    /// The name of a private identifier standing alone as an operand.
    fn private_operand(&self, expression: &Expr) -> Option<String> {
        let Expression::Identifier(identifier) = expression.data() else {
            return None;
        };
        let token = self.file.token_text(identifier.data().token())?;
        token.starts_with('#').then(|| Self::cooked_private(token))
    }

    fn private_reference(&mut self, name: String, range: TextRange) {
        match self.private_scopes.last_mut() {
            Some(scope) => scope.unresolved.push((name, range)),
            None => self.error(range, "this private name is not declared in a class"),
        }
    }

    fn bound_names(&self, pattern: &Pattern, names: &mut Vec<(String, TextRange)>) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                names.push((self.name(identifier), identifier.range()));
            }
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.bound_names(&property.binding, names);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let ArrayBindingElement::Binding(binding) = element {
                        self.bound_names(binding, names);
                    }
                }
            }
            BindingPattern::Rest(rest) => self.bound_names(&rest.argument, names),
            BindingPattern::Assignment(assignment) => self.bound_names(&assignment.left, names),
            BindingPattern::Missing(_) => {}
        }
    }

    /// Checks one binding pattern and walks the expressions inside it.
    fn pattern(&mut self, pattern: &Pattern, context: Context) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                let name = self.name(identifier);
                self.check_binding(&name, identifier.range(), context);
            }
            BindingPattern::Object(object) => {
                let last = object.properties.len().saturating_sub(1);
                for (position, property) in object.properties.iter().enumerate() {
                    if let PropertyName::Computed(key) = &property.name {
                        self.expression(key, context);
                    }
                    self.literal_name(&property.name, context);
                    if let BindingPattern::Rest(rest) = property.binding.data() {
                        if position != last || self.comma_follows(property.binding.range()) {
                            self.error(property.binding.range(), "a rest property must come last");
                        }
                        if !matches!(rest.argument.data(), BindingPattern::Identifier(_)) {
                            self.error(
                                property.binding.range(),
                                "a rest property must bind an identifier",
                            );
                        }
                    }
                    self.pattern(&property.binding, context);
                    if let Some(initializer) = &property.initializer {
                        self.expression(initializer, context);
                    }
                }
            }
            BindingPattern::Array(array) => {
                let last = array.elements.len().saturating_sub(1);
                for (position, element) in array.elements.iter().enumerate() {
                    if let ArrayBindingElement::Binding(binding) = element {
                        if matches!(binding.data(), BindingPattern::Rest(_))
                            && (position != last || self.comma_follows(binding.range()))
                        {
                            self.error(binding.range(), "a rest element must come last");
                        }
                        self.pattern(binding, context);
                    }
                }
            }
            BindingPattern::Rest(rest) => {
                if matches!(rest.argument.data(), BindingPattern::Assignment(_)) {
                    self.error(pattern.range(), "a rest element cannot have an initializer");
                }
                self.pattern(&rest.argument, context);
            }
            BindingPattern::Assignment(assignment) => {
                self.pattern(&assignment.left, context);
                self.expression(&assignment.right, context);
            }
            BindingPattern::Missing(_) => {}
        }
    }

    // --- Scopes ----------------------------------------------------------

    fn var_names(&self, statements: &[Stmt], names: &mut Vec<(String, TextRange)>) {
        for statement in statements {
            self.statement_var_names(statement, names);
        }
    }

    fn declarator_names(
        &self,
        declaration: &crate::syntax::VariableDeclaration,
        names: &mut Vec<(String, TextRange)>,
    ) {
        if matches!(declaration.kind, VariableKind::Var) {
            for declarator in &declaration.declarations {
                self.bound_names(&declarator.data().binding, names);
            }
        }
    }

    fn statement_var_names(&self, statement: &Stmt, names: &mut Vec<(String, TextRange)>) {
        match unexported(statement).data() {
            Statement::Variable(declaration) => self.declarator_names(declaration, names),
            Statement::Block(block) => self.var_names(&block.data().statements, names),
            Statement::If(conditional) => {
                self.statement_var_names(&conditional.consequent, names);
                if let Some(alternate) = &conditional.alternate {
                    self.statement_var_names(alternate, names);
                }
            }
            Statement::For(for_statement) => {
                if let Some(ForInitializer::Variable(declaration)) = &for_statement.initializer {
                    self.declarator_names(declaration, names);
                }
                self.statement_var_names(&for_statement.body, names);
            }
            Statement::ForIn(for_in) => {
                if let ForBinding::Variable(declaration) = &for_in.binding {
                    self.declarator_names(declaration, names);
                }
                self.statement_var_names(&for_in.body, names);
            }
            Statement::ForOf(for_of) => {
                if let ForBinding::Variable(declaration) = &for_of.binding {
                    self.declarator_names(declaration, names);
                }
                self.statement_var_names(&for_of.body, names);
            }
            Statement::While(while_statement) => {
                self.statement_var_names(&while_statement.body, names);
            }
            Statement::DoWhile(do_while) => self.statement_var_names(&do_while.body, names),
            Statement::With(with) => self.statement_var_names(&with.body, names),
            Statement::Labeled(labeled) => self.statement_var_names(&labeled.body, names),
            Statement::Try(try_statement) => {
                self.var_names(&try_statement.block.data().statements, names);
                if let Some(handler) = &try_statement.handler {
                    self.var_names(&handler.data().body.data().statements, names);
                }
                if let Some(finalizer) = &try_statement.finalizer {
                    self.var_names(&finalizer.data().statements, names);
                }
            }
            Statement::Switch(switch) => {
                for case in &switch.cases {
                    self.var_names(&case.data().consequent, names);
                }
            }
            _ => {}
        }
    }

    fn lexical_names(&self, statements: &[Stmt], functions_are_lexical: bool) -> Vec<Lexical> {
        let mut lexical = Vec::new();
        for statement in statements {
            let statement = unexported(unlabeled(statement));
            match statement.data() {
                Statement::Variable(declaration)
                    if !matches!(declaration.kind, VariableKind::Var) =>
                {
                    let mut names = Vec::new();
                    for declarator in &declaration.declarations {
                        self.bound_names(&declarator.data().binding, &mut names);
                    }
                    lexical.extend(names.into_iter().map(|(name, range)| Lexical {
                        name,
                        range,
                        plain_function: false,
                    }));
                }
                Statement::Class(class) => self.class_name(class, &mut lexical),
                Statement::Function(function) if functions_are_lexical => {
                    self.function_name(&function.function, &mut lexical);
                }
                Statement::Import(import) => self.import_names(import, &mut lexical),
                Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
                    ExportDefaultValue::Function(function) => {
                        self.function_name(function, &mut lexical);
                    }
                    ExportDefaultValue::Class(class) => self.class_name(class, &mut lexical),
                    _ => {}
                },
                _ => {}
            }
        }
        lexical
    }

    /// The names an import binds in the module. A type-only import binds no value.
    fn import_names(&self, import: &ImportDeclaration, lexical: &mut Vec<Lexical>) {
        let Some(clause) = import.clause.as_ref().filter(|_| !import.type_only) else {
            return;
        };
        let (namespace, specifiers) = match &clause.binding {
            Some(ImportBinding::Namespace(local)) => (Some(local), &[][..]),
            Some(ImportBinding::Named(specifiers)) => (None, specifiers.as_slice()),
            None => (None, &[][..]),
        };
        let named = specifiers
            .iter()
            .map(|specifier| specifier.data())
            .filter(|specifier| specifier.mode == ImportSpecifierMode::Value)
            .map(|specifier| &specifier.local);
        for local in clause.default.iter().chain(namespace).chain(named) {
            lexical.push(Lexical {
                name: self.name(local),
                range: local.range(),
                plain_function: false,
            });
        }
    }

    fn class_name(&self, class: &ClassDeclaration, lexical: &mut Vec<Lexical>) {
        if let Some(name) = &class.name {
            lexical.push(Lexical {
                name: self.name(name),
                range: name.range(),
                plain_function: false,
            });
        }
    }

    fn function_name(&self, function: &FunctionLike, lexical: &mut Vec<Lexical>) {
        if let Some(name) = &function.name {
            lexical.push(Lexical {
                name: self.name(name),
                range: name.range(),
                plain_function: !function.is_async && !function.is_generator,
            });
        }
    }

    /// Reports redeclarations in one scope. `extra_vars` are var-like names from
    /// outside the statement list, such as a function's parameters.
    fn check_scope(
        &mut self,
        statements: &[Stmt],
        kind: ScopeKind,
        extra_vars: &[(String, TextRange)],
        context: Context,
    ) {
        let functions_are_lexical = match kind {
            ScopeKind::Block => true,
            ScopeKind::Program => context.module,
            ScopeKind::Function => false,
        };
        let lexical = self.lexical_names(statements, functions_are_lexical);
        let mut seen: BTreeMap<&str, bool> = BTreeMap::new();
        let mut reports = Vec::new();
        for entry in &lexical {
            match seen.get(entry.name.as_str()) {
                Some(previous_plain)
                    if !(kind == ScopeKind::Block
                        && !context.strict
                        && *previous_plain
                        && entry.plain_function) =>
                {
                    reports.push(entry.range);
                }
                _ => {
                    seen.insert(&entry.name, entry.plain_function);
                }
            }
        }
        let mut vars = Vec::new();
        self.var_names(statements, &mut vars);
        if !functions_are_lexical {
            for statement in statements {
                if let Statement::Function(function) = unlabeled(statement).data()
                    && let Some(name) = &function.function.name
                {
                    vars.push((self.name(name), name.range()));
                }
            }
        }
        for (name, range) in vars.iter().chain(extra_vars) {
            if seen.contains_key(name.as_str()) {
                reports.push(*range);
            }
        }
        for range in reports {
            self.error(range, "this name is already declared in this scope");
        }
    }

    fn scope(&mut self, statements: &[Stmt], kind: ScopeKind, context: Context) {
        self.check_scope(statements, kind, &[], context);
        for statement in statements {
            self.statement(statement, context);
        }
    }

    fn block(&mut self, block: &BlockNode, context: Context) {
        self.scope(&block.data().statements, ScopeKind::Block, context);
    }

    /// Checks a declaration that a loop or `if` holds without a block.
    fn substatement(&mut self, statement: &Stmt, allow_function: bool, context: Context) {
        match unlabeled(statement).data() {
            Statement::Class(_) => {
                self.error(statement.range(), "a class declaration needs a block here");
            }
            Statement::Variable(declaration) if self.is_lexical_declaration(declaration) => {
                self.error(
                    statement.range(),
                    "a lexical declaration needs a block here",
                );
            }
            Statement::Function(function)
                if !allow_function
                    || context.strict
                    || function.function.is_async
                    || function.function.is_generator =>
            {
                self.error(
                    statement.range(),
                    "a function declaration needs a block here",
                );
            }
            _ => {}
        }
        self.statement(statement, context);
    }

    /// Checks a branch of an `if`, where Annex B allows a function declaration
    /// only if no label stands in front of it.
    fn branch(&mut self, statement: &Stmt, context: Context) {
        if matches!(statement.data(), Statement::Labeled(_))
            && matches!(unlabeled(statement).data(), Statement::Function(_))
        {
            self.error(statement.range(), "a labeled function needs a block here");
        }
        self.substatement(statement, true, context);
    }

    /// Whether a declaration in statement position is really one. `let` before
    /// a line break there is an identifier followed by a new statement, unless
    /// `[` comes next, which no statement may start after `let`.
    fn is_lexical_declaration(&self, declaration: &crate::syntax::VariableDeclaration) -> bool {
        if matches!(declaration.kind, VariableKind::Var) {
            return false;
        }
        if !matches!(declaration.kind, VariableKind::Let) {
            return true;
        }
        let Some(first) = declaration.declarations.first() else {
            return true;
        };
        let source = self.file.source_text();
        let line_break = match (
            source.utf16_to_byte(declaration.range.start()),
            source.utf16_to_byte(first.data().binding.range().start()),
        ) {
            (Ok(start), Ok(end)) => source.as_str()[start..end].contains(['\n', '\r']),
            _ => false,
        };
        !line_break || matches!(first.data().binding.data(), BindingPattern::Array(_))
    }

    fn variable(&mut self, declaration: &crate::syntax::VariableDeclaration, context: Context) {
        let lexical = !matches!(declaration.kind, VariableKind::Var);
        let mut names = Vec::new();
        for declarator in &declaration.declarations {
            let declarator = declarator.data();
            self.pattern(&declarator.binding, context);
            if lexical {
                self.bound_names(&declarator.binding, &mut names);
            }
            if let Some(initializer) = &declarator.initializer {
                self.expression(initializer, context);
            }
        }
        let mut seen = BTreeSet::new();
        for (name, range) in names {
            if name == "let" {
                self.error(range, "`let` cannot name a lexical binding");
            }
            if !seen.insert(name) {
                self.error(range, "this name is already declared in this scope");
            }
        }
    }

    /// Reports a declarator a `const` or `using` statement cannot have. A
    /// `for-in` or `for-of` head gets its value from the loop, so it is exempt.
    fn check_declarators(&mut self, declaration: &crate::syntax::VariableDeclaration) {
        let needs_value = !matches!(declaration.kind, VariableKind::Var | VariableKind::Let);
        let using = matches!(
            declaration.kind,
            VariableKind::Using | VariableKind::AwaitUsing
        );
        for declarator in &declaration.declarations {
            let declarator = declarator.data();
            if needs_value && declarator.initializer.is_none() {
                self.error(declarator.binding.range(), "this declaration needs a value");
            }
            if using && !matches!(declarator.binding.data(), BindingPattern::Identifier(_)) {
                self.error(declarator.binding.range(), "`using` binds a single name");
            }
        }
    }

    /// Reports a name a `for` head binds lexically that its body redeclares.
    fn check_for_head(&mut self, declaration: &crate::syntax::VariableDeclaration, body: &Stmt) {
        if matches!(declaration.kind, VariableKind::Var) {
            return;
        }
        let mut bound = Vec::new();
        for declarator in &declaration.declarations {
            self.bound_names(&declarator.data().binding, &mut bound);
        }
        let mut vars = Vec::new();
        self.statement_var_names(body, &mut vars);
        for (name, range) in vars {
            if bound.iter().any(|(head, _)| *head == name) {
                self.error(range, "this name is already declared in this scope");
            }
        }
    }

    // --- Statements ------------------------------------------------------

    fn statement(&mut self, statement: &Stmt, context: Context) {
        let program_level = context.program_level;
        let context = Context {
            program_level: false,
            ..context
        };
        if !program_level
            && matches!(
                statement.data(),
                Statement::Import(_) | Statement::Export(_)
            )
        {
            self.error(statement.range(), "module syntax needs the top level");
        }
        let looping = Context {
            in_iteration: true,
            ..context
        };
        match statement.data() {
            Statement::Variable(declaration) => {
                if program_level
                    && context.script
                    && matches!(
                        declaration.kind,
                        VariableKind::Using | VariableKind::AwaitUsing
                    )
                {
                    self.error(
                        statement.range(),
                        "`using` is not allowed at the top level of a script",
                    );
                }
                self.check_declarators(declaration);
                self.variable(declaration, context);
            }
            Statement::Function(function) => {
                self.function(&function.function, false, false, context);
            }
            Statement::Class(class) => self.class(class, context),
            Statement::Block(block) => self.block(block, context),
            Statement::Expression(expression) => self.expression(&expression.expression, context),
            Statement::If(conditional) => {
                self.expression(&conditional.test, context);
                self.branch(&conditional.consequent, context);
                if let Some(alternate) = &conditional.alternate {
                    self.branch(alternate, context);
                }
            }
            Statement::Switch(switch) => {
                self.expression(&switch.discriminant, context);
                let statements: Vec<Stmt> = switch
                    .cases
                    .iter()
                    .flat_map(|case| case.data().consequent.iter().cloned())
                    .collect();
                self.check_scope(&statements, ScopeKind::Block, &[], context);
                let inner = Context {
                    in_switch: true,
                    ..context
                };
                for case in &switch.cases {
                    if let Some(test) = &case.data().test {
                        self.expression(test, context);
                    }
                    for statement in &case.data().consequent {
                        if let Statement::Variable(declaration) = statement.data()
                            && matches!(
                                declaration.kind,
                                VariableKind::Using | VariableKind::AwaitUsing
                            )
                        {
                            self.error(statement.range(), "`using` needs a block here");
                        }
                        self.statement(statement, inner);
                    }
                }
            }
            Statement::For(for_statement) => {
                match &for_statement.initializer {
                    Some(ForInitializer::Variable(declaration)) => {
                        self.check_declarators(declaration);
                        self.check_for_head(declaration, &for_statement.body);
                        self.variable(declaration, context);
                    }
                    Some(ForInitializer::Expression(expression)) => {
                        self.expression(expression, context);
                    }
                    None => {}
                }
                if let Some(test) = &for_statement.test {
                    self.expression(test, context);
                }
                if let Some(update) = &for_statement.update {
                    self.expression(update, context);
                }
                self.substatement(&for_statement.body, false, looping);
            }
            Statement::ForIn(for_in) => {
                if let ForBinding::Variable(declaration) = &for_in.binding
                    && matches!(
                        declaration.kind,
                        VariableKind::Using | VariableKind::AwaitUsing
                    )
                {
                    self.error(statement.range(), "`using` cannot head a `for-in` loop");
                }
                self.for_binding(&for_in.binding, &for_in.body, context);
                self.expression(&for_in.object, context);
                self.substatement(&for_in.body, false, looping);
            }
            Statement::ForOf(for_of) => {
                self.for_binding(&for_of.binding, &for_of.body, context);
                self.expression(&for_of.iterable, context);
                self.substatement(&for_of.body, false, looping);
            }
            Statement::While(while_statement) => {
                self.expression(&while_statement.test, context);
                self.substatement(&while_statement.body, false, looping);
            }
            Statement::DoWhile(do_while) => {
                self.substatement(&do_while.body, false, looping);
                self.expression(&do_while.test, context);
            }
            Statement::Try(try_statement) => {
                self.block(&try_statement.block, context);
                if let Some(handler) = &try_statement.handler {
                    let handler = handler.data();
                    if let Some(binding) = &handler.binding {
                        self.pattern(binding, context);
                        let mut names = Vec::new();
                        self.bound_names(binding, &mut names);
                        let mut seen = BTreeSet::new();
                        for (name, range) in &names {
                            if !seen.insert(name.clone()) {
                                self.error(*range, "this name is already declared in this scope");
                            }
                        }
                        let body = &handler.body.data().statements;
                        for entry in self.lexical_names(body, true) {
                            if seen.contains(&entry.name) {
                                self.error(
                                    entry.range,
                                    "this name is already declared in this scope",
                                );
                            }
                        }
                    }
                    self.block(&handler.body, context);
                }
                if let Some(finalizer) = &try_statement.finalizer {
                    self.block(finalizer, context);
                }
            }
            Statement::With(with) => {
                if context.strict {
                    self.error(statement.range(), "`with` is not allowed in strict mode");
                }
                self.expression(&with.object, context);
                self.substatement(&with.body, false, context);
            }
            Statement::Labeled(labeled) => {
                let name = self.name(&labeled.label);
                self.check_identifier(&name, labeled.label.range(), context);
                if self.labels.iter().any(|(existing, _)| *existing == name) {
                    self.error(labeled.label.range(), "this label is already in use");
                }
                let target = is_iteration(unlabeled(&labeled.body).data());
                self.labels.push((name, target));
                self.substatement(&labeled.body, true, context);
                self.labels.pop();
            }
            Statement::Break(jump) => match &jump.label {
                Some(label) => {
                    let name = self.name(label);
                    if !self.labels.iter().any(|(existing, _)| *existing == name) {
                        self.error(label.range(), "`break` names an undefined label");
                    }
                }
                None if !context.in_iteration && !context.in_switch => {
                    self.error(statement.range(), "`break` needs a loop or switch");
                }
                None => {}
            },
            Statement::Continue(jump) => match &jump.label {
                Some(label) => {
                    let name = self.name(label);
                    if !self
                        .labels
                        .iter()
                        .any(|(existing, target)| *existing == name && *target)
                    {
                        self.error(label.range(), "`continue` needs a label on a loop");
                    }
                }
                None if !context.in_iteration => {
                    self.error(statement.range(), "`continue` needs a loop");
                }
                None => {}
            },
            Statement::Return(return_statement) => {
                if !context.in_function {
                    self.error(statement.range(), "`return` needs a function");
                }
                if let Some(argument) = &return_statement.argument {
                    self.expression(argument, context);
                }
            }
            Statement::Throw(throw) => self.expression(&throw.argument, context),
            Statement::Import(import) => self.import(import, context),
            Statement::Export(export) => self.export(export, context),
            _ => {}
        }
    }

    fn import(&mut self, import: &ImportDeclaration, context: Context) {
        let mut names = Vec::new();
        self.import_names(import, &mut names);
        for name in names {
            self.check_binding(&name.name, name.range, context);
        }
    }

    fn for_binding(&mut self, binding: &ForBinding, body: &Stmt, context: Context) {
        match binding {
            ForBinding::Variable(declaration) => {
                if context.strict
                    && declaration.kind == VariableKind::Var
                    && declaration.declarations.len() == 1
                    && declaration.declarations[0].data().initializer.is_some()
                {
                    self.error(
                        declaration.declarations[0].range(),
                        "a for-in head cannot have an initializer in strict mode",
                    );
                }
                self.check_for_head(declaration, body);
                self.variable(declaration, context);
            }
            ForBinding::Target(target) => self.target(target, true, context),
        }
    }

    fn export(&mut self, export: &ExportDeclaration, context: Context) {
        match export {
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(declaration)) => {
                self.statement(declaration, context);
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    self.function(function, false, false, context);
                }
                ExportDefaultValue::Class(class) => self.class(class, context),
                ExportDefaultValue::Expression(expression) => {
                    self.expression(expression, context);
                }
                _ => {}
            },
            _ => {}
        }
    }

    // --- Functions and classes -------------------------------------------

    /// Walks a non-arrow function. `method` allows `super.x` in it. An `expression`
    /// binds its own name, so its own kind decides what that name can be; a
    /// declaration's name belongs to the code around it.
    fn function(
        &mut self,
        function: &FunctionLike,
        method: bool,
        expression: bool,
        context: Context,
    ) {
        let inner = Context {
            generator: function.is_generator,
            is_async: function.is_async,
            super_property: method,
            unique_parameters: method,
            ..Self::function_context(context)
        };
        self.callable(&function.parameters, function.body.as_ref(), inner);
        if let Some(name) = &function.name {
            let text = self.name(name);
            let strict = inner.strict
                || function
                    .body
                    .as_ref()
                    .is_some_and(|body| self.body_is_strict(body));
            let around = if expression {
                Context {
                    generator: function.is_generator,
                    is_async: function.is_async,
                    ..context
                }
            } else {
                context
            };
            self.check_binding(&text, name.range(), Context { strict, ..around });
        }
    }

    /// What a new function scope resets. Strictness and the module goal carry in.
    fn function_context(context: Context) -> Context {
        Context {
            strict: context.strict,
            module: context.module,
            script: context.script,
            new_target: true,
            in_function: true,
            ..Context::default()
        }
    }

    fn body_is_strict(&self, body: &FunctionBody) -> bool {
        match body {
            FunctionBody::Block(block) => has_use_strict(self.file, &block.data().statements),
            _ => false,
        }
    }

    fn callable(
        &mut self,
        parameters: &[ParameterNode],
        body: Option<&FunctionBody>,
        context: Context,
    ) {
        let saved_labels = std::mem::take(&mut self.labels);
        let simple = parameters.iter().all(|parameter| {
            parameter.data().initializer.is_none()
                && matches!(
                    parameter.data().binding.data(),
                    BindingPattern::Identifier(_)
                )
        });
        let strict = context.strict || body.is_some_and(|body| self.body_is_strict(body));
        if !simple
            && body.is_some_and(|body| self.body_is_strict(body))
            && let Some(FunctionBody::Block(block)) = body
        {
            self.error(block.range(), "`use strict` needs simple parameters");
        }
        let inner = Context { strict, ..context };
        let parameter_context = Context {
            in_parameters: true,
            generator: inner.generator || inner.arrow_in_generator,
            ..inner
        };
        let mut names = Vec::new();
        let last = parameters.len().saturating_sub(1);
        for (position, parameter) in parameters.iter().enumerate() {
            let data = parameter.data();
            if let BindingPattern::Rest(rest) = data.binding.data() {
                if position != last || self.comma_follows(parameter.range()) {
                    self.error(parameter.range(), "a rest parameter must come last");
                }
                if data.initializer.is_some()
                    || matches!(rest.argument.data(), BindingPattern::Assignment(_))
                {
                    self.error(
                        parameter.range(),
                        "a rest parameter cannot have an initializer",
                    );
                }
            }
            self.pattern(&data.binding, parameter_context);
            if let Some(initializer) = &data.initializer {
                self.expression(initializer, parameter_context);
            }
            self.bound_names(&data.binding, &mut names);
        }
        let mut seen = BTreeSet::new();
        let duplicates_allowed = simple && !strict && !context.unique_parameters;
        for (name, range) in &names {
            if !seen.insert(name.clone()) && !duplicates_allowed {
                self.error(*range, "this parameter name is already used");
            }
        }
        match body {
            Some(FunctionBody::Block(block)) => {
                self.check_scope(&block.data().statements, ScopeKind::Function, &[], inner);
                let lexical = self.lexical_names(&block.data().statements, false);
                for entry in lexical {
                    if seen.contains(&entry.name) {
                        self.error(entry.range, "this name is already declared in this scope");
                    }
                }
                for statement in &block.data().statements {
                    self.statement(statement, inner);
                }
            }
            Some(FunctionBody::Expression(expression)) => self.expression(expression, inner),
            _ => {}
        }
        self.labels = saved_labels;
    }

    fn accessor_parameters(
        &mut self,
        modifier: PropertyModifier,
        parameters: &[ParameterNode],
        range: TextRange,
    ) {
        match modifier {
            PropertyModifier::Get if !parameters.is_empty() => {
                self.error(range, "a getter takes no parameters");
            }
            PropertyModifier::Set
                if parameters.len() != 1
                    || matches!(parameters[0].data().binding.data(), BindingPattern::Rest(_)) =>
            {
                self.error(range, "a setter takes exactly one parameter");
            }
            _ => {}
        }
    }

    fn class(&mut self, class: &ClassDeclaration, context: Context) {
        let context = Context {
            strict: true,
            ..context
        };
        if let Some(name) = &class.name {
            let text = self.name(name);
            self.check_binding(&text, name.range(), context);
        }
        if let Some(heritage) = &class.extends {
            self.expression(&heritage.expression, context);
        }
        let derived = class.extends.is_some();
        self.private_scopes.push(PrivateScope::default());
        self.declare_private_names(class);
        let mut constructors = 0;
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(constructor) => {
                    constructors += 1;
                    if constructors > 1 {
                        self.error(member.range(), "a class has one constructor");
                    }
                    let inner = Context {
                        super_call: derived,
                        super_property: true,
                        unique_parameters: true,
                        ..Self::function_context(context)
                    };
                    let body = FunctionBody::Block(constructor.body.clone());
                    self.callable(&constructor.parameters, Some(&body), inner);
                }
                ClassMember::Method(method) => {
                    self.literal_name(&method.name, context);
                    self.check_method_name(method, member.range());
                    self.accessor_parameters(
                        method.modifier,
                        &method.function.parameters,
                        member.range(),
                    );
                    if let PropertyName::Computed(key) = &method.name {
                        self.expression(key, context);
                    }
                    self.function(&method.function, true, false, context);
                }
                ClassMember::Property(property) => {
                    self.literal_name(&property.name, context);
                    self.check_field_name(
                        &property.name,
                        property.modifiers.is_static,
                        member.range(),
                    );
                    if let PropertyName::Computed(key) = &property.name {
                        self.expression(key, context);
                    }
                    if let Some(initializer) = &property.initializer {
                        self.expression(initializer, Self::initializer_context(context));
                    }
                }
                ClassMember::AutoAccessor(accessor) => {
                    self.literal_name(&accessor.name, context);
                    self.check_field_name(
                        &accessor.name,
                        accessor.modifiers.is_static,
                        member.range(),
                    );
                    if let PropertyName::Computed(key) = &accessor.name {
                        self.expression(key, context);
                    }
                    if let Some(initializer) = &accessor.initializer {
                        self.expression(initializer, Self::initializer_context(context));
                    }
                }
                ClassMember::StaticBlock(block) => {
                    let inner = Context {
                        static_block: true,
                        in_function: false,
                        ..Self::initializer_context(context)
                    };
                    let saved_labels = std::mem::take(&mut self.labels);
                    self.check_scope(&block.data().statements, ScopeKind::Function, &[], inner);
                    for statement in &block.data().statements {
                        self.statement(statement, inner);
                    }
                    self.labels = saved_labels;
                }
                _ => {}
            }
        }
        let scope = self.private_scopes.pop().unwrap_or_default();
        for (name, range) in scope.unresolved {
            if !scope.declared.contains(&name) {
                self.private_reference(name, range);
            }
        }
    }

    /// A field initializer behaves as a method body with no arguments object.
    fn initializer_context(context: Context) -> Context {
        Context {
            super_property: true,
            class_initializer: true,
            ..Self::function_context(context)
        }
    }

    fn check_method_name(&mut self, method: &crate::syntax::MethodDeclaration, range: TextRange) {
        let special = method.modifier != PropertyModifier::None
            || method.function.is_async
            || method.function.is_generator;
        let name = self.property_text(&method.name);
        if method.modifiers.is_static {
            if name.as_deref() == Some("prototype") {
                self.error(range, "a static method cannot be named `prototype`");
            }
        } else if special && name.as_deref() == Some("constructor") {
            self.error(range, "`constructor` must be a plain method");
        }
    }

    fn check_field_name(&mut self, name: &PropertyName, is_static: bool, range: TextRange) {
        let text = self.property_text(name);
        if text.as_deref() == Some("constructor")
            || (is_static && text.as_deref() == Some("prototype"))
        {
            self.error(range, "a field cannot have this name");
        }
    }

    fn declare_private_names(&mut self, class: &ClassDeclaration) {
        let mut declared: BTreeMap<String, Vec<PrivateKind>> = BTreeMap::new();
        for member in &class.members {
            let (name, kind) = match member.data() {
                ClassMember::Method(method) => {
                    let is_static = method.modifiers.is_static;
                    let kind = match method.modifier {
                        PropertyModifier::Get => PrivateKind::Getter { is_static },
                        PropertyModifier::Set => PrivateKind::Setter { is_static },
                        PropertyModifier::None => PrivateKind::Other,
                    };
                    (&method.name, kind)
                }
                ClassMember::Property(property) => (&property.name, PrivateKind::Other),
                ClassMember::AutoAccessor(accessor) => (&accessor.name, PrivateKind::Other),
                _ => continue,
            };
            let PropertyName::Private(private) = name else {
                continue;
            };
            let text = self.private_name(private);
            if text == "#constructor" {
                self.error(
                    private.range(),
                    "`#constructor` is not a valid private name",
                );
            }
            let existing = declared.entry(text).or_default();
            let compatible = existing.iter().all(|previous| match (previous, &kind) {
                (
                    PrivateKind::Getter { is_static: first },
                    PrivateKind::Setter { is_static: second },
                )
                | (
                    PrivateKind::Setter { is_static: first },
                    PrivateKind::Getter { is_static: second },
                ) => first == second,
                _ => false,
            });
            if !compatible {
                self.error(private.range(), "this private name is already declared");
            }
            existing.push(kind);
        }
        if let Some(scope) = self.private_scopes.last_mut() {
            scope.declared = declared.into_keys().collect();
        }
    }

    // --- Expressions -----------------------------------------------------

    fn target(&mut self, target: &AssignmentTargetNode, patterns_allowed: bool, context: Context) {
        match target.data() {
            AssignmentTarget::Identifier(identifier) => {
                let name = self.name(identifier);
                if context.strict && (name == "eval" || name == "arguments") {
                    self.error(
                        identifier.range(),
                        "`eval` and `arguments` cannot be assigned in strict mode",
                    );
                }
                self.reference(identifier, context);
            }
            AssignmentTarget::Member(member) => {
                self.member(&member.object, &member.property, context);
            }
            AssignmentTarget::Object(object) => {
                if !patterns_allowed || is_parenthesized(self.file, target.range()) {
                    self.error(target.range(), "this operator cannot assign to a pattern");
                }
                let last = object.properties.len().saturating_sub(1);
                for (position, property) in object.properties.iter().enumerate() {
                    if property.rest
                        && (position != last || self.comma_follows(property.target.range()))
                    {
                        self.error(property.target.range(), "a rest property must come last");
                    }
                    if property.rest
                        && matches!(
                            property.target.data(),
                            AssignmentTarget::Object(_) | AssignmentTarget::Array(_)
                        )
                    {
                        self.error(
                            property.target.range(),
                            "a rest property cannot be a pattern",
                        );
                    }
                    if let PropertyName::Computed(key) = &property.name {
                        self.expression(key, context);
                    }
                    self.literal_name(&property.name, context);
                    self.pattern_target(&property.target, context);
                    if let Some(initializer) = &property.initializer {
                        self.expression(initializer, context);
                    }
                }
            }
            AssignmentTarget::Array(array) => {
                if !patterns_allowed || is_parenthesized(self.file, target.range()) {
                    self.error(target.range(), "this operator cannot assign to a pattern");
                }
                let last = array.elements.len().saturating_sub(1);
                for (position, element) in array.elements.iter().enumerate() {
                    match element {
                        AssignmentArrayElement::Target(element) => {
                            self.array_element(element, context);
                        }
                        AssignmentArrayElement::Rest(element) => {
                            if position != last || self.comma_follows(element.range()) {
                                self.error(element.range(), "a rest element must come last");
                            }
                            if matches!(element.data(), AssignmentTarget::Invalid(_)) {
                                self.error(
                                    element.range(),
                                    "a rest element cannot have an initializer",
                                );
                            }
                            self.pattern_target(element, context);
                        }
                        AssignmentArrayElement::Elision | AssignmentArrayElement::Missing(_) => {}
                    }
                }
            }
            AssignmentTarget::Invalid(expression) => {
                // Annex B keeps `f() = 1` and `(f()) += 1` a runtime error in sloppy
                // code, but not a call in an optional chain.
                let call = strip_parentheses(expression);
                if context.strict
                    || !matches!(call.data(), Expression::Call(_))
                    || in_optional_chain(call)
                {
                    self.error(target.range(), "this cannot be assigned to");
                }
                self.expression(expression, context);
            }
            // A method or accessor folds to this, and reaching the walker means
            // the parser reported nothing else here.
            AssignmentTarget::Missing(_) => {
                self.error(target.range(), "this cannot be assigned to")
            }
        }
    }

    /// An element of an array pattern, which may carry a default: the parser
    /// keeps `[a = 1]`'s element as the assignment it was read as.
    fn array_element(&mut self, element: &AssignmentTargetNode, context: Context) {
        if let AssignmentTarget::Invalid(expression) = element.data()
            && let Expression::Assignment(assignment) = expression.data()
            && assignment.operator == AssignmentOperator::Assign
        {
            self.pattern_target(&assignment.left, context);
            self.expression(&assignment.right, context);
        } else {
            self.pattern_target(element, context);
        }
    }

    /// A target inside a pattern. Annex B covers `f() = 1` alone, so a call here
    /// is an early error in sloppy code too.
    fn pattern_target(&mut self, target: &AssignmentTargetNode, context: Context) {
        // `target` reports a call in an optional chain itself.
        if !context.strict
            && let AssignmentTarget::Invalid(expression) = target.data()
            && matches!(expression.data(), Expression::Call(_))
            && !in_optional_chain(expression)
        {
            self.error(target.range(), "this cannot be assigned to");
        }
        self.target(target, true, context);
    }

    fn member(&mut self, object: &Expr, property: &MemberProperty, context: Context) {
        if matches!(object.data(), Expression::Super) {
            if !context.super_property {
                self.error(object.range(), "`super` is not available here");
            }
        } else {
            self.expression(object, context);
        }
        match property {
            MemberProperty::Private(private) => {
                let name = self.private_name(private);
                self.private_reference(name, private.range());
            }
            MemberProperty::Computed(key) => self.expression(key, context),
            MemberProperty::Named(_) => {}
        }
    }

    fn arguments(&mut self, arguments: &[CallArgument], context: Context) {
        for argument in arguments {
            match argument {
                CallArgument::Expression(expression) => self.expression(expression, context),
                CallArgument::Spread(spread) => self.expression(&spread.argument, context),
                CallArgument::Missing(_) => {}
            }
        }
    }

    /// A string or a number that names a property is still a literal in strict
    /// code.
    fn literal_name(&mut self, name: &PropertyName, context: Context) {
        if !context.strict {
            return;
        }
        let range = match name {
            PropertyName::String(literal)
                if has_legacy_escape(self.token_of(literal.data().token())) =>
            {
                literal.range()
            }
            PropertyName::Number(literal)
                if is_legacy_octal_number(self.token_of(literal.data().token())) =>
            {
                literal.range()
            }
            _ => return,
        };
        self.error(range, "legacy octal is not allowed in strict code");
    }

    fn object(&mut self, members: &[crate::syntax::ObjectMemberNode], context: Context) {
        let mut proto = 0;
        for member in members {
            match member.data() {
                ObjectMember::Property(property) => {
                    self.literal_name(&property.name, context);
                    if property.shorthand
                        && (!matches!(property.name, PropertyName::Identifier(_))
                            || matches!(property.value.data(), Expression::Assignment(_)))
                    {
                        self.error(member.range(), "this shorthand needs a pattern around it");
                    }
                    if let PropertyName::Computed(key) = &property.name {
                        self.expression(key, context);
                    }
                    if !property.shorthand
                        && self.property_text(&property.name).as_deref() == Some("__proto__")
                    {
                        proto += 1;
                        if proto > 1 {
                            self.error(member.range(), "`__proto__` is set twice");
                        }
                    }
                    self.expression(&property.value, context);
                }
                ObjectMember::Method(method) => {
                    self.literal_name(&method.name, context);
                    self.accessor_parameters(
                        method.modifier,
                        &method.function.parameters,
                        member.range(),
                    );
                    if let PropertyName::Computed(key) = &method.name {
                        self.expression(key, context);
                    }
                    self.function(&method.function, true, false, context);
                }
                ObjectMember::Spread(spread) => self.expression(&spread.argument, context),
                ObjectMember::Missing(_) => {}
            }
        }
    }

    fn expression(&mut self, expression: &Expr, context: Context) {
        match expression.data() {
            Expression::Identifier(identifier) => self.reference(identifier, context),
            Expression::Super => self.error(expression.range(), "`super` is not available here"),
            Expression::Literal(Literal::Number(literal)) if context.strict => {
                if is_legacy_octal_number(self.token_of(literal.data().token())) {
                    self.error(
                        expression.range(),
                        "legacy octal is not allowed in strict code",
                    );
                }
            }
            Expression::Literal(Literal::Regex(literal)) => {
                if let Some(text) = self.file.token_text(literal.data().token()) {
                    if crate::regexp::validate_regex_literal(text).is_some() {
                        self.error(expression.range(), "invalid regular expression");
                    }
                }
            }
            Expression::Literal(Literal::String(literal)) if context.strict => {
                if has_legacy_escape(self.token_of(literal.data().token())) {
                    self.error(
                        expression.range(),
                        "legacy octal is not allowed in strict code",
                    );
                }
            }
            Expression::Template(template) => {
                for element in &template.elements {
                    if has_legacy_escape(self.token_of(element.data().token())) {
                        self.error(element.range(), "a template cannot use a legacy escape");
                    }
                }
                for inner in &template.expressions {
                    self.expression(inner, context);
                }
            }
            Expression::TaggedTemplate(tagged) => {
                if in_optional_chain(&tagged.tag) {
                    self.error(expression.range(), "a template cannot follow `?.`");
                }
                self.expression(&tagged.tag, context);
                for inner in &tagged.template.expressions {
                    self.expression(inner, context);
                }
            }
            Expression::Array(array) => {
                for element in &array.elements {
                    match element {
                        ArrayElement::Expression(inner) => self.expression(inner, context),
                        ArrayElement::Spread(spread) => self.expression(&spread.argument, context),
                        ArrayElement::Elision | ArrayElement::Missing(_) => {}
                    }
                }
            }
            Expression::Object(object) => self.object(&object.members, context),
            // A function expression's name is bound inside it, so a static block
            // around it has no say.
            Expression::Function(function) => self.function(
                &function.function,
                false,
                true,
                Context {
                    static_block: false,
                    ..context
                },
            ),
            Expression::Class(class) => self.class(&class.class, context),
            Expression::Arrow(arrow) => {
                let inner = Context {
                    generator: false,
                    arrow_in_generator: context.generator,
                    is_async: arrow.is_async,
                    static_block: false,
                    unique_parameters: true,
                    in_iteration: false,
                    in_switch: false,
                    in_parameters: false,
                    in_function: true,
                    top_level_await: false,
                    async_parameters: context.async_parameters
                        || (context.in_parameters && context.is_async),
                    ..context
                };
                self.callable(&arrow.parameters, Some(&arrow.body), inner);
            }
            Expression::Call(call) if self.is_import_phase(&call.callee) => {
                self.import_phase_call(&call.arguments, expression.range(), context);
            }
            Expression::Call(call) => {
                if matches!(call.callee.data(), Expression::Super) {
                    if !context.super_call {
                        self.error(call.callee.range(), "`super()` is not available here");
                    }
                } else {
                    self.expression(&call.callee, context);
                }
                self.arguments(&call.arguments, context);
            }
            Expression::Member(member) => self.member(&member.object, &member.property, context),
            Expression::New(new) => {
                if rooted_in_import(&new.callee) {
                    self.error(new.callee.range(), "`import()` cannot be constructed");
                }
                self.expression(&new.callee, context);
                self.arguments(&new.arguments, context);
            }
            Expression::Await(await_expression) => {
                if context.in_parameters {
                    self.error(expression.range(), "`await` cannot appear in parameters");
                }
                if !context.is_async && !context.top_level_await {
                    self.error(expression.range(), "`await` needs an async function");
                }
                self.expression(&await_expression.argument, context);
            }
            Expression::Yield(yield_expression) => {
                if context.in_parameters && context.generator {
                    self.error(expression.range(), "`yield` cannot appear in parameters");
                }
                if let Some(argument) = &yield_expression.argument {
                    self.expression(argument, context);
                }
            }
            Expression::Unary(unary) => {
                if unary.operator == UnaryOperator::Delete {
                    match strip_parentheses(&unary.argument).data() {
                        Expression::Identifier(_) if context.strict => {
                            self.error(
                                expression.range(),
                                "`delete` of a name is not allowed in strict mode",
                            );
                        }
                        Expression::Member(member)
                            if matches!(member.property, MemberProperty::Private(_)) =>
                        {
                            self.error(expression.range(), "a private name cannot be deleted");
                        }
                        _ => {}
                    }
                }
                self.expression(&unary.argument, context);
            }
            Expression::Update(update) => self.target(&update.argument, false, context),
            Expression::Binary(binary) => {
                match self.private_operand(&binary.left) {
                    Some(name) if binary.operator == BinaryOperator::In => {
                        self.private_reference(name, binary.left.range());
                    }
                    _ => self.expression(&binary.left, context),
                }
                self.expression(&binary.right, context);
            }
            Expression::Logical(logical) => {
                for side in [&logical.left, &logical.right] {
                    if let Expression::Logical(inner) = side.data()
                        && is_mixed_logical(logical.operator, inner.operator)
                    {
                        self.error(side.range(), "`??` cannot mix with `&&` or `||`");
                    }
                }
                self.expression(&logical.left, context);
                self.expression(&logical.right, context);
            }
            Expression::Conditional(conditional) => {
                self.expression(&conditional.test, context);
                self.expression(&conditional.consequent, context);
                self.expression(&conditional.alternate, context);
            }
            Expression::Assignment(assignment) => {
                if matches!(
                    assignment.operator,
                    AssignmentOperator::LogicalAndAssign
                        | AssignmentOperator::LogicalOrAssign
                        | AssignmentOperator::NullishAssign
                ) && matches!(assignment.left.data(), AssignmentTarget::Invalid(_))
                {
                    self.error(assignment.left.range(), "this cannot be assigned to");
                }
                let patterns_allowed = assignment.operator == AssignmentOperator::Assign;
                self.target(&assignment.left, patterns_allowed, context);
                self.expression(&assignment.right, context);
            }
            Expression::Sequence(sequence) => {
                for inner in &sequence.expressions {
                    self.expression(inner, context);
                }
            }
            Expression::Parenthesized(inner) => self.expression(inner, context),
            Expression::Import(import) => {
                self.expression(&import.source, context);
                if let Some(options) = &import.options {
                    self.expression(options, context);
                }
            }
            Expression::Meta(MetaProperty::NewTarget) => {
                if self.meta_word(expression) != "target" {
                    self.error(expression.range(), "`new.target` cannot contain an escape");
                }
                if !context.new_target {
                    self.error(expression.range(), "`new.target` needs a function");
                }
            }
            Expression::Meta(MetaProperty::ImportMeta) => {
                if self.meta_word(expression) != "meta" {
                    self.error(expression.range(), "this `import` form is not valid here");
                }
                if context.script {
                    self.error(expression.range(), "`import.meta` needs a module");
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::{
        parser::parse,
        scanner::scan,
        source::{ScriptKind, SourceId, SourceText},
    };

    fn errors(source: &str) -> Vec<String> {
        let text = Arc::new(SourceText::new(source).expect("source fits"));
        let parsed = parse(scan(SourceId::new(0), ScriptKind::JavaScript, text));
        check(parsed.product())
            .iter()
            .map(|diagnostic| diagnostic.message().to_owned())
            .collect()
    }

    #[test]
    fn invalid_programs_are_rejected() {
        for source in [
            "{ let a; let a; }",
            "{ let a; var a; }",
            "{ var a; class a {} }",
            "let a; function a() {}",
            "function f(a) { let a; }",
            "for (let a;;) { var a; }",
            "try {} catch (e) { let e; }",
            "switch (0) { case 1: let f; default: function* f() {} }",
            "'use strict'; { function f() {} function f() {} }",
            "a: a: ;",
            "break;",
            "continue;",
            "x: { continue x; }",
            "while (1) { break missing; }",
            "'use strict'; var public;",
            "'use strict'; eval = 1;",
            "'use strict'; delete x;",
            "'use strict'; with (a) {}",
            "function f() { 'use strict'; var static; }",
            "function f(a = 1) { 'use strict'; }",
            "function* g() { var yield; }",
            "async function f() { var await; }",
            "function* g(x = yield) {}",
            "async function f(x = await 1) {}",
            "class C { #a; #a; }",
            "class C { get #a() {} get #a() {} }",
            "class C { static get #a() {} set #a(v) {} }",
            "class C { #constructor; }",
            "class C { m() { this.#missing; } }",
            "class C { #a; m() { delete this.#a; } }",
            "class C { #a; m() { delete ((this.#a)); } }",
            "this.#outside;",
            "class C { constructor() {} constructor() {} }",
            "class C { get constructor() {} }",
            "class C { *constructor() {} }",
            "class C { async constructor() {} }",
            "class C { static prototype() {} }",
            "class C { constructor; }",
            "class C { static prototype; }",
            "class C { x = arguments; }",
            "class C { x = () => arguments; }",
            "class C { m() { super(); } }",
            "class C { constructor() { super(); } }",
            "function f() { super.x; }",
            "class let {}",
            "let let = 1;",
            "let [a, a] = [];",
            "1 = 2;",
            "'use strict'; f() = 1;",
            "class C { static { function await() {} } }",
            "a + b = c;",
            "[...a, b] = c;",
            "[...a = 1] = c;",
            "[a] += 1;",
            "var [...a, b] = c;",
            "var [...a = 1] = c;",
            "var {...a, b} = c;",
            "var {...{a}} = c;",
            "function f(...a, b) {}",
            "function f(...a = []) {}",
            "function f(a, a) { 'use strict'; }",
            "(a, a) => 1;",
            "({ get a(b) {} });",
            "({ set a() {} });",
            "({ set a(...b) {} });",
            "({ __proto__: 1, __proto__: 2 });",
            "if (1) class C {}",
            "while (1) function f() {}",
            "if (1) async function f() {}",
            "if (1) let [a] = b;",
            "if (1) let\n[a] = b;",
            "new.target;",
            "new import('a');",
        ] {
            let found = errors(source);
            assert!(!found.is_empty(), "{source:?} must be rejected");
        }
    }

    #[test]
    fn valid_programs_are_accepted() {
        for source in [
            "{ function f() {} function f() {} }",
            "function f() {} function f() {}",
            "var a; var a;",
            "function a() {} var a;",
            "function f(a) { var a; }",
            "function f(a, a) {}",
            "try {} catch (e) { var e; }",
            "for (var a;;) { var a; }",
            "a: b: while (1) { continue a; }",
            "a: { break a; }",
            "a: ; a: ;",
            "while (1) { function f() { a: ; } break; }",
            "var public, static, let, yield, await;",
            "eval = 1; arguments = 2;",
            "delete x;",
            "with (a) {}",
            "if (1) function f() {}",
            "a: function f() {}",
            "function* g() { yield 1; function h(x = 1) { var yield; } }",
            "async function f() { await 1; function g() { var await; } }",
            "class C { #a; m() { this.#a; #a in this; } }",
            "class C { get #a() {} set #a(v) {} static #b; }",
            "class C { #a; m() { class D { n(x) { x.#a; } } } }",
            "class C { static async *g() {} static x = 1; constructor() {} }",
            "class C { 'constructor'() {} }",
            "class C { static constructor() {} static get constructor() {} }",
            "class C { m() { super.m(); } x = super.y; static { super.z; } }",
            "class B {} class C extends B { constructor() { super(); () => super(); } }",
            "({ m() { super.x; } });",
            "({ __proto__: 1, ['__proto__']: 2, __proto__() {}, get __proto__() { return 1; } });",
            "({ __proto__ });",
            "var [a, ...b] = c, {d, ...e} = f;",
            "[a, ...b] = c;",
            "({ a, ...b } = c);",
            "function f(a = 1, ...b) {}",
            "(function () { new.target; });",
            "class C { x = new.target; }",
            "function f() { 'use strict'; }",
            "function f(a) { 'use strict'; }",
            "'use strict'; class C { static x = 1; }",
            "a ? b : c; `x${a}y`; a`b${c}`;",
            "if (1) let\na;",
            "while (0) let\n{}",
            "yield = 1; function f(a = yield) {}",
            "class C { static { () => { var await; }; (function await(await) {}); } }",
            "f() = 1; f()++; for (f() of []) ;",
            "class C { #\\u{6F}; m() { this.#o; } }",
            "class C { constructor() {} static constructor() {} static *constructor() {} }",
            "[a = 1, [b = 2]] = c;",
            "[...a] = b; [...[c, d]] = e; [...f.g] = h;",
            "for (var a of b) ({ x: [c = 1] } = a);",
            "for (let a of b) { let a; }",
            "for (var a in b) var c;",
            "switch (0) { case 1: var a; default: var a; }",
            "class C { x = function () { arguments; }; }",
            "class C { static { var await_ = 1; } }",
            "async () => { await 1; };",
            "async function f() { () => 1; }",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source:?}");
        }
    }

    #[test]
    fn syntax_the_grammar_alone_cannot_refuse_is_refused() {
        for source in [
            "var x = ({ bre\\u0061k }) => {};",
            "var this = 1;",
            "\"use strict\"; 010;",
            "\"use strict\"; '\\1';",
            "\"use strict\"; '\\8';",
            "function f() { '\\1'; 'use strict'; }",
            "`\\8`;",
            "`\\00`;",
            "({ a = 1 });",
            "({ 0 });",
            "({ [a] });",
            "(...a,) => {};",
            "function f(...a,) {}",
            "[...a,] = b;",
            "let [...a,] = b;",
            "const a;",
            "for (const a;;) {}",
            "{ using a; }",
            "{ using a = null, [] = null; }",
            "for (using a in b) {}",
            "switch (0) { case 0: using a = null; }",
            "return;",
            "class C { static { return; } }",
            "0 && 0 ?? 1;",
            "0 ?? 0 || 1;",
            "a?.b`c`;",
            "f() &&= 1;",
            "({}) = 1;",
            "[a, ({ b })] = c;",
            "if (0) a: function f() {}",
            "class C { #a; m() { #a in #a in this; } }",
            "class C { #a; m() { for (#a in []); } }",
            "async(a = await => {}) => {};",
            "(async function* await() {});",
            "(async function* yield() {});",
            "(function* yield() {});",
            "async function f() { function await() {} }",
        ] {
            assert!(!errors(source).is_empty(), "{source} must be rejected");
        }
        for source in [
            "'\\0'; 010; '\\1'; 09;",
            "\"use strict\"; '\\0';",
            "`\\0`;",
            "a`\\8`;",
            "({ a = 1 } = b);",
            "[{ a = 1 }] = b;",
            "({ a = 1 }) => a;",
            "(...a) => {};",
            "[...a, ] ;",
            "for (const a of b) {}",
            "for (const a in b) {}",
            "{ using a = null; }",
            "for (using a of b) {}",
            "function f() { return; }",
            "() => { return; };",
            "class C { static { (() => { return; })(); } }",
            "0 && (0 ?? 1);",
            "(0 && 0) ?? 1;",
            "a?.b.c;",
            "f() = 1;",
            "({ a } = b);",
            "if (0) function f() {}",
            "a: function f() {}",
            "class C { #a; m() { return #a in this; } }",
            "async function f() { await 0; }",
            "async(a = 1) => {};",
            "function await() {}",
            "(function await() {});",
            "(async function () { function yield() {} });",
            "async function f() { (function await() {}); }",
            "export {}; await 0;",
            "function f() { return await(null); }",
            "function await() {} await(1);",
            "var await; await instanceof f;",
            "await 0;",
            "await f();",
            "function f() { return g(await); }",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn only_import_calls_use_a_phase() {
        for source in [
            "import.UNKNOWN('a');",
            "import.defer();",
            "import.source(...a);",
            "new import.defer('a');",
            "new import.source('a').b;",
            "new import('a').b;",
            "typeof import.source;",
            "import.m\\u0065ta;",
            "function f() { new.t\\u0061rget; }",
        ] {
            assert!(!errors(source).is_empty(), "{source} must be rejected");
        }
        for source in [
            "import.defer('a');",
            "import.source('a', {});",
            "import . /* a.b */ meta;",
            "function f() { new . target; }",
            "new (import('a'));",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn an_object_pattern_keeps_its_rest_rules() {
        for source in [
            "({ ...a, b } = c);",
            "({ ...{ a } } = b);",
            "({ ...[a] } = b);",
            "({ get a() {} } = b);",
            "[{ m() {} }] = a;",
            "var { ...a, } = b;",
            "let { c, ...a, } = b;",
            "function f({ ...a, }) {}",
            "({ ...a, }) => 1;",
            "({ ...a, } = b);",
            "({ ...(a), } = b);",
            "({ ...((a)), } = b);",
            "({ ...(a.b), } = c);",
            "[...(a),] = b;",
        ] {
            assert!(!errors(source).is_empty(), "{source} must be rejected");
        }
        for source in [
            "({ a, ...b } = c);",
            "({ ...a.b } = c);",
            "({ ...a[0] } = c);",
            "var { ...a } = b;",
            "var { a, } = b;",
            "({ a, } = b);",
            "({ ...a, });",
            "({ ...(a) } = b);",
            "[...(a)] = b;",
            "[...((a))] = b;",
            "f((...a) => 1, 2);",
            "f(function (...a) {}, 2);",
            "({ m(...a) {}, });",
            "[(...a) => 1, 2];",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn an_exported_declaration_is_checked_like_any_other() {
        for source in [
            "export function f() { break; }",
            "export function f(a, a) {}",
            "export function f() { with (a) {} }",
            "export function f() {} function f() {}",
            "export class C { constructor() {} constructor() {} }",
            "export class C { #a; #a; }",
            "export const a;",
            "export let a, a;",
            "export let a; let a;",
            "export var a; let a;",
            "let a; export var a;",
            "export default function f() {} let f;",
            "export default class C {} let C;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "export function f() { return 1; }",
            "export class C { constructor() {} }",
            "export const a = 1;",
            "export let a, b;",
            "export var a; var a;",
            "export default function f() {} let g;",
            "export default function () {}",
            "export default class {}",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn an_import_binds_a_lexical_name_of_the_module() {
        for source in [
            "import a from 'x'; let a;",
            "import { a } from 'x'; function a() {}",
            "import * as a from 'x'; var a;",
            "import a from 'x'; class a {}",
            "import a from 'x'; import a from 'y';",
            "import { a, a } from 'x';",
            "import { b as a, c as a } from 'x';",
            "import { default as a } from 'x'; let a;",
            "import a, { a } from 'x';",
            "import a, * as a from 'x';",
            "import a from 'x'; { var a; }",
            "let a; import a from 'x';",
            "var a; import a from 'x';",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "import a from 'x'; { let a; }",
            "import a from 'x'; function f() { let a; }",
            "import { a as b } from 'x'; let a;",
            "import 'x'; let a;",
            "import type a from 'x'; let a;",
            "import { type a } from 'x'; let a;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn a_call_is_never_a_target_inside_a_pattern() {
        for source in [
            "[f()] = [];",
            "[...f()] = [];",
            "[f() = 1] = [];",
            "[(f())] = [];",
            "({ a: (f()) } = {});",
            "({ a: f() } = {});",
            "({ a: f() = 1 } = {});",
            "for ([f()] of []) ;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "f() = 1;",
            "(f()) = 1;",
            "f()++;",
            "for (f() of []) ;",
            "for (f() in {}) ;",
            "[f().x] = [];",
            "({ a: f().x } = {});",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    /// Annex B keeps a plain call a target in sloppy code, but Node refuses a call
    /// in an optional chain before the program runs.
    #[test]
    fn a_call_in_an_optional_chain_is_never_a_target() {
        for source in [
            "a?.b() = 1;",
            "f?.() = 1;",
            "a.b?.c() += 1;",
            "a?.b()++;",
            "--a?.b();",
            "for (a?.b() of []) ;",
            "for (a?.b() in {}) ;",
            "a?.b().c = 1;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in ["(a?.b)() = 1;", "(a?.b)()++;"] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
        for source in ["[a?.b()] = [];", "({ x: a?.b() } = {});"] {
            assert_eq!(errors(source).len(), 1, "one error for {source}");
        }
    }

    /// Parentheses pass a name or a member through to every assignment operator,
    /// and a call through to the runtime error of Annex B, as Node reads them.
    #[test]
    fn a_parenthesized_target_takes_every_assignment_operator() {
        for source in [
            "(x) += 1;",
            "((x)) -= 1;",
            "(a.b) *= 2;",
            "(a['b']) **= 2;",
            "(x) &&= 1;",
            "(a.b) ||= 1;",
            "(x) ??= 1;",
            "(eval) += 1;",
            "(f()) += 1;",
            "((f())) <<= 1;",
            "(a?.b)() += 1;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
        for source in [
            "(f()) &&= 1;",
            "(a?.b) += 1;",
            "(a?.b()) += 1;",
            "(this) += 1;",
            "(a, b) += 1;",
            "([x]) += 1;",
            "({ x }) += 1;",
            "'use strict'; (f()) += 1;",
            "'use strict'; (eval) += 1;",
            "'use strict'; (arguments) &&= 1;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
    }

    #[test]
    fn a_number_that_names_a_property_follows_strict_code() {
        for source in [
            r#""use strict"; ({ 01: 1 });"#,
            r#""use strict"; ({ 08: 1 });"#,
            r#""use strict"; ({ 00() {} });"#,
            r#""use strict"; var { 01: x } = {};"#,
            r#""use strict"; ({ 01: x } = {});"#,
            "class C { 01() {} }",
            "class C { 07 = 1; }",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "({ 01: 1 });",
            "var { 01: x } = {};",
            r#""use strict"; ({ 0: 1, 0.5: 2, 1e3: 3, 0x10: 4, 0o7: 5 });"#,
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn a_yield_never_reaches_the_parameters_of_an_arrow() {
        for source in [
            "function* g() { (x = yield) => 1; }",
            "function* g() { (x, y = yield) => 1; }",
            "function* g() { (x = [yield]) => 1; }",
            "function* g() { (x = (yield)) => 1; }",
            "function* g() { (yield) => 1; }",
            "function* g() { ({ x = yield }) => 1; }",
            "function* g() { ([x = yield]) => 1; }",
            "function* g() { (x = { [yield]: 1 }) => 1; }",
            "function* g() { (x = class { [yield]() {} }) => 1; }",
            "function* g() { (x = (y = yield) => 1) => 1; }",
            "function* g() { async (x = yield) => 1; }",
            "async function* g() { (x = yield) => 1; }",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "function* g() { (x = yield); }",
            "function* g() { function h(x = yield) {} }",
            "function* g() { (x = function () { yield; }) => 1; }",
            "function* g() { (x = function* () { yield; }) => 1; }",
            "function* g() { () => { yield; }; }",
            "function* g() { () => { var yield; }; }",
            "function* g() { (x = () => { yield; }) => 1; }",
            "function* g() { (x) => yield; }",
            "(x = yield) => 1;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn module_syntax_belongs_to_the_top_level() {
        for source in [
            "{ import a from 'x'; }",
            "function f() { import a from 'x'; }",
            "if (1) import a from 'x';",
            "if (1) { export { a }; } var a;",
            "{ export default 1; }",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "import a from 'x';",
            "export { a }; var a;",
            "import('x');",
            "{ import('x'); }",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn an_import_cannot_bind_eval_or_arguments() {
        for source in [
            "import { x as eval } from 'y';",
            "import { x as arguments } from 'y';",
            "import eval from 'y';",
            "import * as arguments from 'y';",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "import { eval as x } from 'y';",
            "import { x as y } from 'y';",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn a_string_that_names_a_property_follows_strict_code() {
        for source in [
            r#""use strict"; ({ "\1": 1 });"#,
            r#""use strict"; ({ "\8": 1 });"#,
            r#""use strict"; ({ "\1"() {} });"#,
            r#""use strict"; ({ get "\1"() { return 1; } });"#,
            r#""use strict"; class C { "\1"() {} }"#,
            r#"class C { "\1"() {} }"#,
            r#"class C { "\1" = 1; }"#,
            r#"class C { accessor "\1" = 1; }"#,
            r#"function f() { "\1"; "use strict"; }"#,
            r#""\1"; "use strict";"#,
            r#""use strict"; ({ "\1": x } = {});"#,
            r#""use strict"; for ({ "\8": x } of []);"#,
            r#""use strict"; var { "\1": x } = {};"#,
            r#""use strict"; function f({ "\1": x }) {}"#,
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            r#"({ "\1": 1 });"#,
            r#"({ "\1": x } = {});"#,
            r#"var { "\1": x } = {};"#,
            r#""use strict"; ({ "\0": 1 });"#,
            r#""use strict"; ({ "\x41": 1 });"#,
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn a_string_property_name_is_read_as_its_value() {
        for source in [
            r#"({ "__proto__": 1, __proto__: 2 });"#,
            r#"({ "\x5f_proto__": 1, "__proto__": 2 });"#,
            r#"class C { static "\x70rototype"() {} }"#,
            r#"class C { get "\x63onstructor"() {} }"#,
            r#"class C { "\x63onstructor"; }"#,
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            r#"({ "'__proto__'": 1, __proto__: 2 });"#,
            r#"class C { static "'prototype'"() {} }"#,
            r#"class C { get "'constructor'"() { return 1; } }"#,
            r#"class C { "'constructor'"; }"#,
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn a_string_named_constructor_counts_as_the_constructor() {
        assert!(!errors("class C { 'constructor'() {} constructor() {} }").is_empty());
        assert_eq!(
            errors("class C { 'constructor'() {} }"),
            Vec::<String>::new()
        );
    }

    #[test]
    fn a_module_is_strict_and_reserves_await() {
        for source in [
            "export {}; var public;",
            "export {}; var await;",
            "export {}; with (a) {}",
            "export {}; function f() {} function f() {}",
        ] {
            assert!(!errors(source).is_empty(), "{source:?} must be rejected");
        }
        assert_eq!(errors("export {}; import.meta;"), Vec::<String>::new());
    }

    #[test]
    fn invalid_regex_flags_are_rejected() {
        for source in ["/./gig;", "/./G;", "/./uv;", "/./uu;", "/./sG;"] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in ["/./g;", "/./gi;", "/./d;", "/./s;", "/./y;", "/./v;", "/./u;"] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn invalid_regex_modifiers_are_rejected() {
        for source in [
            "/(?I:a)/;",
            "/(?i-i:a)/;",
            "/(?m-m:a)/;",
            "/(?d:a)/;",
            "/(?-:a)/;",
            "/(?ms-i)/;",
            "/(?-s)/;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in ["/(?i:a)/;", "/(?m:a)/;", "/(?i-m:a)/;", "/(?-i:a)/;"] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }
    #[test]
    fn invalid_regex_properties_are_rejected() {
        for source in [
            "/\\p{Script=FooBarBazInvalid}/u;",
            "/\\p{ASCII=F}/u;",
            "/\\p{General_Category = Uppercase_Letter}/u;",
            "/\\p/u;",
            "/[\\P{}]/u;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/\\p{Hex}/u;",
            "/\\p{ASCII_Hex_Digit}/u;",
            "/\\p{Script=Greek}/u;",
            "/[\\p{Hex}\\P{Hex}]/u;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn invalid_regex_named_groups_are_rejected() {
        for source in [
            "/(?<a>.)\\k<b>/;",
            "/(?<a>a)(?<a>a)/u;",
            "/(?<>a)/u;",
            "/(?<a>.)\\k/u;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/(?<a>a)/;",
            "/\\k<a>(?<a>x)/;",
            "/^(?:(?<a>x)|(?<a>y)|z)\\k<a>$/;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn invalid_regex_group_names_are_rejected() {
        for source in [
            "/(?<:a>a)/;",
            "/(?<:a>a)/u;",
            "/(?<a:>a)/;",
            "/(?<a:>a)/u;",
            "/(?<42a>a)/;",
            "/(?<\u{2764}>a)/;",
            "/(?<a\\uD801>b)/u;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/(?<a>a)/;",
            "/(?<$a_1>x)/;",
            "/(?<\\u0041>a)/;",
            "/(?<a\\uD801\\uDCA4>b)/u;",
            "/\\k<a>(?<a>x)/;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn invalid_regex_unicode_atoms_are_rejected() {
        for source in [
            "/{/u;",
            "/[\\d-a]/u;",
            "/[\\s-\\d]/u;",
            "/[%-\\d]/u;",
            "/[--\\d]/u;",
            "/[\\p{Hex}-\\uFFFF]/u;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in ["/[\\p{Hex}\\P{Hex}]/u;"] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn invalid_regex_unicode_escapes_are_rejected() {
        for source in [
            "/\\c0/u;",
            "/\\8/u;",
            "/\\M/u;",
            "/.(?=.)?/u;",
            "/.(?<=.)?/;",
            "/{2}/;",
            "/\\u{110000}/u;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/\\cA/u;",
            "/\\n/u;",
            "/\\d/u;",
            "/a{2,3}/;",
            "/(?=a)/;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn invalid_regex_unicode_sets_are_rejected() {
        for source in [
            "/[(]/v;",
            "/[-]/v;",
            "/[&&]/v;",
            "/[!!]/v;",
            "/[^^^]/v;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/^[[0-9]--_]+$/v;",
            "/^[\\d--_]+$/v;",
            "/[\\(]/v;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn string_property_escapes_are_rejected_when_negated() {
        for source in [
            "/\\P{RGI_Emoji}/v;",
            "/[\\P{RGI_Emoji}]/v;",
            "/[^\\p{RGI_Emoji}]/v;",
            "/[[^\\p{RGI_Emoji}]]/v;",
            "/[^\\p{Basic_Emoji}]/v;",
            "/[^\\p{RGI_Emoji_Flag_Sequence}]/v;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/\\p{RGI_Emoji}/v;",
            "/[\\p{RGI_Emoji}]/v;",
            "/[[\\p{RGI_Emoji}]]/v;",
            "/[\\p{Basic_Emoji}]/v;",
            "/[\\P{Hex}]/u;",
            "/[^\\p{Hex}]/v;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn unicode_sets_class_operands_are_validated() {
        for source in [
            "/[a--]/v;",
            "/[--a]/v;",
            "/[a&&]/v;",
            "/[&&b]/v;",
            "/[a-]/v;",
            "/[-]/v;",
            "/[a--b&&c]/v;",
            "/[a&&b--c]/v;",
            "/[a-b--c]/v;",
            "/[0-9--_]/v;",
            "/[a-z-b]/v;",
            "/[a-z-_]/v;",
            "/[a-b-c]/v;",
            "/[a-b&&b]/v;",
            "/[a-\\d]/v;",
            "/[\\d-\\d]/v;",
            "/[[a]-[b]]/v;",
            "/[a-[b]]/v;",
            "/[a-&&b]/v;",
            "/[a&&bc]/v;",
            "/[a--bc]/v;",
            "/[a&&b\\d]/v;",
            "/[[a]c&&a]/v;",
            "/[a{2}]/v;",
            "/[\\q{]}]/v;",
            "/[\\q{-}]/v;",
            "/[\\q{[}]/v;",
        ] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in [
            "/[a--b]/v;",
            "/[a--b--c]/v;",
            "/[a--b--c--d]/v;",
            "/[a&&b&&c]/v;",
            "/[a-z]/v;",
            "/[[a]--[b]]/v;",
            "/[\\w--a]/v;",
            "/[\\d&&\\w]/v;",
            "/[\\q{a}&&b]/v;",
            "/[b--\\q{ab}]/v;",
            "/[\\q{ab}--\\q{cd}]/v;",
            "/[\\-a]/v;",
            "/[\\-]/v;",
            "/[a^]/v;",
            "/[a*b]/v;",
            "/[\\x41-\\x45]/v;",
            "/[\\n-\\x7F]/v;",
            "/[𐀀-𐫫]/v;",
            "/[\\q{}]/v;",
            "/[\\q{a}]/v;",
            "/[\\q{a|}]/v;",
            "/[\\q{ab|c}]/v;",
            "/[\\q{^}]/v;",
            "/[\\q{ }]/v;",
            "/[\\q{\\uD800}]/v;",
            "/[\\q{𐀀}]/v;",
        ] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn sloppy_var_initializer_in_for_in_follows_annex_b() {
        assert_eq!(errors("for (var a = 0 in {});"), Vec::<String>::new());
        assert!(!errors("\"use strict\"; for (var a = 0 in {});").is_empty());
    }

    fn script_errors(source: &str) -> Vec<String> {
        let text = Arc::new(SourceText::new(source).expect("source fits"));
        let parsed = parse(scan(SourceId::new(0), ScriptKind::JavaScript, text));
        check_script(parsed.product())
            .iter()
            .map(|diagnostic| diagnostic.message().to_owned())
            .collect()
    }

    #[test]
    fn out_of_order_braced_quantifiers_are_rejected() {
        for source in ["/0{2,1}/;", "/0{2,1}/u;", "/0{2,1}/v;"] {
            assert!(!errors(source).is_empty(), "{source}");
        }
        for source in ["/0{2,1/;", "/0{,2}/;", "/0{/;", "/0{2,1", "/a{2,3}/;"] {
            assert_eq!(errors(source), Vec::<String>::new(), "{source}");
        }
    }

    #[test]
    fn using_at_script_top_level_is_rejected() {
        for source in ["using x = null;", "await using x = null;"] {
            assert!(!script_errors(source).is_empty(), "{source}");
        }
        for source in [
            "{ using x = null; }",
            "function f() { using x = null; }",
        ] {
            assert_eq!(script_errors(source), Vec::<String>::new(), "{source}");
        }
        assert_eq!(errors("using x = null;"), Vec::<String>::new());
    }
}
