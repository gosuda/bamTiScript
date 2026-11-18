//! Object rest pattern lowering for targets that bind destructuring
//! natively but lack `...rest` (es2015 through es2017). Binding patterns
//! split into sibling declarators or comma-sequence assignments: the
//! non-rest properties stay a pattern, every rest target becomes a
//! `__rest` call, and subpatterns that carry rest read through fresh
//! temporaries.

use super::Rewriter;
use super::helpers::HelperKind;
use crate::source::TextRange;
use crate::syntax::*;

/// One key inside a `__rest` exclusion array.
enum ExcludeKey {
    /// An identifier or numeric key, emitted as `"name"`.
    Name(String),
    /// A string-literal key, emitted with its written quote style.
    Quoted(String),
    /// A computed key evaluated once into a temporary.
    Key(IdentifierNode),
}

/// Whether the pattern binds an object rest somewhere below it. Array rest
/// stays native at these targets and never counts.
pub(super) fn object_rest_in_pattern(pattern: &Pattern) -> bool {
    match pattern.data() {
        BindingPattern::Object(object) => object.properties.iter().any(|property| {
            matches!(property.binding.data(), BindingPattern::Rest(_))
                || object_rest_in_pattern(&property.binding)
        }),
        BindingPattern::Array(array) => array.elements.iter().any(|element| match element {
            ArrayBindingElement::Binding(binding) => {
                !matches!(binding.data(), BindingPattern::Rest(_))
                    && object_rest_in_pattern(binding)
            }
            _ => false,
        }),
        BindingPattern::Assignment(assignment) => object_rest_in_pattern(&assignment.left),
        _ => false,
    }
}

/// The assignment-target counterpart of [`object_rest_in_pattern`].
pub(super) fn object_rest_in_target(target: &AssignmentTargetNode) -> bool {
    match target.data() {
        AssignmentTarget::Object(object) => object
            .properties
            .iter()
            .any(|property| property.rest || object_rest_in_target(&property.target)),
        AssignmentTarget::Array(array) => array.elements.iter().any(|element| match element {
            AssignmentArrayElement::Target(target) | AssignmentArrayElement::Rest(target) => {
                object_rest_in_target(target)
            }
            _ => false,
        }),
        _ => false,
    }
}

fn dynamic_key(name: &PropertyName) -> bool {
    match name {
        PropertyName::Computed(expr) => !matches!(
            expr.data(),
            Expression::Literal(Literal::String(_)) | Expression::Literal(Literal::Number(_))
        ),
        _ => false,
    }
}

/// A rest property binds only in last position; earlier ones are dropped
/// but their argument name still lands in later exclusion lists.
fn rest_is_last(index: usize, len: usize) -> bool {
    index + 1 == len
}

/// The identifier a rest argument binds, whose name joins the exclusion
/// list of a later rest.
fn rest_argument_name(pattern: &Pattern) -> Option<&IdentifierNode> {
    match pattern.data() {
        BindingPattern::Identifier(ident) => Some(ident),
        _ => None,
    }
}

/// An object pattern whose only property is `...ident`: it lowers to a
/// direct `__rest` read of the member expression, with no temporary.
fn pure_rest_binding(pattern: &Pattern) -> Option<&IdentifierNode> {
    let BindingPattern::Object(object) = pattern.data() else {
        return None;
    };
    if object.properties.len() != 1 {
        return None;
    }
    let property = &object.properties[0];
    if property.initializer.is_some() {
        return None;
    }
    let BindingPattern::Rest(rest) = property.binding.data() else {
        return None;
    };
    rest_argument_name(&rest.argument)
}

impl Rewriter<'_> {
    /// Entry hook for variable statements at es2015 through es2017.
    pub(super) fn lower_rest_variable_statement(
        &mut self,
        statement: &Stmt,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        let range = statement.range();
        let mut declarations = Vec::with_capacity(declaration.declarations.len());
        for declarator in &declaration.declarations {
            let needs = declarator.data().initializer.is_some()
                && object_rest_in_pattern(&declarator.data().binding);
            if needs {
                declarations.extend(self.lower_rest_declarator(declarator));
            } else {
                declarations.push(self.rewrite_declarator_initializer(declarator));
            }
        }
        vec![self.node(
            range,
            Statement::Variable(VariableDeclaration {
                range: declaration.range,
                kind: declaration.kind,
                declarations,
            }),
        )]
    }

    /// Declarators for one binding pattern read from `source`, shared by
    /// parameter, catch, and for-of lowering.
    pub(super) fn flatten_binding_declarators(
        &mut self,
        binding: &Pattern,
        source: &IdentifierNode,
        range: TextRange,
    ) -> Vec<VariableDeclaratorNode> {
        match binding.data() {
            BindingPattern::Object(object) => {
                self.flatten_object_properties(&object.properties, source, true, range)
            }
            BindingPattern::Array(array) => {
                let init = self.identifier_expr_of(source);
                self.flatten_array_elements(&array.elements, init, range)
            }
            _ => vec![self.kept_pattern_declarator(binding, source, range)],
        }
    }

    /// Assignment-target counterpart of [`Self::flatten_binding_declarators`],
    /// producing the comma-sequence parts of a destructuring assignment.
    pub(super) fn flatten_assignment_target_parts(
        &mut self,
        target: &AssignmentTargetNode,
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        match target.data() {
            AssignmentTarget::Object(object) => self.flatten_assignment_object(
                &object.properties,
                source,
                object.properties.iter().any(|p| dynamic_key(&p.name)),
                range,
                parts,
            ),
            AssignmentTarget::Array(array) => {
                let init = self.identifier_expr_of(source);
                self.flatten_assignment_array(&array.elements, init, range, parts)
            }
            _ => {
                let rewritten = self.rewrite_assignment_target(target);
                let value = self.identifier_expr_of(source);
                parts.push(self.assign_target(rewritten, value, range));
            }
        }
    }

    /// Entry point for `({...rest} = value)` at es2015 through es2017. The
    /// result is a comma sequence; in statement position the trailing
    /// source read is omitted because nothing consumes the value.
    pub(super) fn lower_rest_assignment(
        &mut self,
        assignment: &AssignmentExpression,
        range: TextRange,
        for_value: bool,
    ) -> Expr {
        let right = self.rewrite_expr(&assignment.right);
        let result = match assignment.left.data() {
            AssignmentTarget::Object(object) => {
                if !for_value && object.properties.len() == 1 && object.properties[0].rest {
                    let property = &object.properties[0];
                    let excluded = self.exclusion_array(&[], range);
                    let call = self.rest_call_expr(&right, excluded, range);
                    let target = self.rewrite_assignment_target(&property.target);
                    let assign = self.assign_target(target, call, range);
                    self.rest_sequence(vec![assign], range)
                } else {
                    let has_dynamic = object
                        .properties
                        .iter()
                        .any(|property| dynamic_key(&property.name));
                    let mut parts = Vec::new();
                    let source = self.assignment_source(&right, has_dynamic, range, &mut parts);
                    self.flatten_assignment_object(
                        &object.properties,
                        &source,
                        has_dynamic,
                        range,
                        &mut parts,
                    );
                    if for_value {
                        parts.push(self.identifier_expr_of(&source));
                    }
                    self.rest_sequence(parts, range)
                }
            }
            AssignmentTarget::Array(array) => {
                let mut parts = Vec::new();
                let source = self.assignment_source(&right, false, range, &mut parts);
                let init = self.identifier_expr_of(&source);
                self.flatten_assignment_array(&array.elements, init, range, &mut parts);
                if for_value {
                    parts.push(self.identifier_expr_of(&source));
                }
                self.rest_sequence(parts, range)
            }
            _ => unreachable!("rest assignment lowering only sees object and array targets"),
        };
        if !for_value && matches!(result.data(), Expression::Sequence(_)) {
            return self.syn_node(range, Expression::Parenthesized(Box::new(result)));
        }
        result
    }

    /// The identifier every flattened read shares. A dynamic-key level
    /// always snapshots the source; a static level only when the right-hand
    /// side is not already an identifier.
    fn assignment_source(
        &mut self,
        right: &Expr,
        force_temp: bool,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) -> IdentifierNode {
        if !force_temp && let Expression::Identifier(ident) = right.data() {
            return ident.clone();
        }
        let temp = self.expression_temp();
        parts.push(self.store_temp(&temp, right.clone(), range));
        temp
    }

    /// The comma sequence a flattened rest pattern evaluates to. A single
    /// part needs no sequence wrapper.
    pub(super) fn rest_sequence(&mut self, expressions: Vec<Expr>, range: TextRange) -> Expr {
        if expressions.len() == 1
            && let Some(single) = expressions.first()
        {
            return single.clone();
        }
        self.node(
            range,
            Expression::Sequence(SequenceExpression { expressions }),
        )
    }

    fn assign_target(
        &mut self,
        target: AssignmentTargetNode,
        value: Expr,
        range: TextRange,
    ) -> Expr {
        self.node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left: target,
                right: Box::new(value),
            }),
        )
    }

    fn lower_rest_declarator(
        &mut self,
        declarator: &VariableDeclaratorNode,
    ) -> Vec<VariableDeclaratorNode> {
        let range = declarator.range();
        let data = declarator.data();
        let initializer = match data.initializer.as_deref() {
            Some(initializer) => initializer,
            None => return vec![declarator.clone()],
        };
        let source = self.rewrite_expr(initializer);
        let mut parts: Vec<VariableDeclaratorNode> = Vec::new();
        let (source_ident, source_is_temp) = match source.data() {
            Expression::Identifier(ident) => (ident.clone(), false),
            _ => {
                let temp = self.temp_ident();
                parts.push(self.make_declarator(temp.clone(), Some(source), range));
                (temp, true)
            }
        };
        match data.binding.data() {
            BindingPattern::Object(object) => parts.extend(self.flatten_object_properties(
                &object.properties,
                &source_ident,
                source_is_temp,
                range,
            )),
            BindingPattern::Array(array) => {
                let init = self.identifier_expr_of(&source_ident);
                parts.extend(self.flatten_array_elements(&array.elements, init, range))
            }
            _ => parts.push(self.kept_pattern_declarator(&data.binding, &source_ident, range)),
        }
        parts
    }

    /// Splits one object-pattern level into kept, deep, and rest declarators.
    /// A level with a dynamic computed key flattens every property into
    /// member reads so the key evaluates once.
    fn flatten_object_properties(
        &mut self,
        properties: &[ObjectBindingProperty],
        source: &IdentifierNode,
        source_is_temp: bool,
        range: TextRange,
    ) -> Vec<VariableDeclaratorNode> {
        let mut parts = Vec::new();
        if properties
            .iter()
            .any(|property| dynamic_key(&property.name))
        {
            self.flatten_every_property(properties, source, source_is_temp, range, &mut parts);
        } else {
            self.flatten_with_kept_pattern(properties, source, range, &mut parts);
        }
        parts
    }

    fn flatten_every_property(
        &mut self,
        properties: &[ObjectBindingProperty],
        source: &IdentifierNode,
        source_is_temp: bool,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
    ) {
        let mut source = source.clone();
        if !source_is_temp {
            let temp = self.temp_ident();
            let value = self.identifier_expr_of(&source);
            parts.push(self.make_declarator(temp.clone(), Some(value), range));
            source = temp;
        }
        let mut exclusions: Vec<ExcludeKey> = Vec::new();
        for (index, property) in properties.iter().enumerate() {
            match property.binding.data() {
                BindingPattern::Rest(rest) => {
                    if rest_is_last(index, properties.len()) {
                        let excluded = self.exclusion_array(&exclusions, range);
                        let call = self.rest_call(&source, excluded, range);
                        self.bind_rest_argument(&rest.argument, call, range, parts);
                    } else if let Some(ident) = rest_argument_name(&rest.argument) {
                        let name = self.token_text(ident.data().token()).to_owned();
                        exclusions.push(ExcludeKey::Name(name));
                    }
                }
                _ => {
                    let member =
                        self.level_member(property, &source, range, parts, &mut exclusions);
                    self.flatten_leaf(property, member, range, parts);
                }
            }
        }
    }

    fn flatten_with_kept_pattern(
        &mut self,
        properties: &[ObjectBindingProperty],
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
    ) {
        let mut kept: Vec<ObjectBindingProperty> = Vec::new();
        let mut exclusions: Vec<ExcludeKey> = Vec::new();
        for (index, property) in properties.iter().enumerate() {
            match property.binding.data() {
                BindingPattern::Rest(rest) => {
                    if rest_is_last(index, properties.len()) {
                        self.flush_kept_pattern(&kept, source, range, parts);
                        kept.clear();
                        let excluded = self.exclusion_array(&exclusions, range);
                        let call = self.rest_call(source, excluded, range);
                        self.bind_rest_argument(&rest.argument, call, range, parts);
                    } else if let Some(ident) = rest_argument_name(&rest.argument) {
                        let name = self.token_text(ident.data().token()).to_owned();
                        exclusions.push(ExcludeKey::Name(name));
                    }
                }
                _ => {
                    if object_rest_in_pattern(&property.binding) {
                        self.flush_kept_pattern(&kept, source, range, parts);
                        kept.clear();
                        let member =
                            self.level_member(property, source, range, parts, &mut exclusions);
                        self.flatten_leaf(property, member, range, parts);
                    } else {
                        exclusions.push(self.exclusion_for_name(&property.name));
                        kept.push(property.clone());
                    }
                }
            }
        }
        self.flush_kept_pattern(&kept, source, range, parts);
    }

    /// Binds a `__rest` result: directly for an identifier argument, through
    /// a temporary and subpattern flattening otherwise.
    fn bind_rest_argument(
        &mut self,
        argument: &Pattern,
        call: Expr,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
    ) {
        match argument.data() {
            BindingPattern::Identifier(ident) => {
                parts.push(self.make_declarator(ident.clone(), Some(call), range));
            }
            _ => {
                let temp = self.temp_ident();
                parts.push(self.make_declarator(temp.clone(), Some(call), range));
                parts.extend(self.flatten_subpattern(argument, &temp, range));
            }
        }
    }

    /// The member read for one property plus its exclusion key. A dynamic
    /// computed key evaluates once into a fresh declarator.
    fn level_member(
        &mut self,
        property: &ObjectBindingProperty,
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
        exclusions: &mut Vec<ExcludeKey>,
    ) -> Expr {
        match &property.name {
            PropertyName::Computed(key) if dynamic_key(&property.name) => {
                let temp = self.temp_ident();
                let value = self.rewrite_expr(key);
                parts.push(self.make_declarator(temp.clone(), Some(value), range));
                exclusions.push(ExcludeKey::Key(temp.clone()));
                let reference = self.identifier_expr_of(&temp);
                self.member_computed(source, &reference, range)
            }
            name => {
                let member = self.member_for_name(source, name, range);
                exclusions.push(self.exclusion_for_name(name));
                member
            }
        }
    }

    fn identifier_expr_of(&mut self, ident: &IdentifierNode) -> Expr {
        self.node(ident.range(), Expression::Identifier(ident.clone()))
    }

    /// `source.name` for named keys, `source["b"]` for string and numeric
    /// keys written as literals.
    fn member_for_name(
        &mut self,
        source: &IdentifierNode,
        name: &PropertyName,
        range: TextRange,
    ) -> Expr {
        match name {
            PropertyName::Identifier(ident) => {
                let text = self.token_text(ident.data().token()).to_owned();
                self.member_ident(source, &text, range)
            }
            PropertyName::String(literal) => {
                let raw = self.token_text(literal.data().token()).to_owned();
                self.member_literal_key(source, &raw, range)
            }
            PropertyName::Number(number) => {
                let raw = self.token_text(number.data().token()).to_owned();
                self.member_literal_key(source, &raw, range)
            }
            PropertyName::Computed(expr) => match self.literal_key_lexeme(expr) {
                Some(raw) => self.member_literal_key(source, &raw, range),
                None => self.member_computed(source, expr, range),
            },
            PropertyName::Private(_) | PropertyName::Missing(_) => {
                unreachable!("binding property names are identifiers, literals, or computed")
            }
        }
    }

    fn member_literal_key(&mut self, source: &IdentifierNode, raw: &str, range: TextRange) -> Expr {
        let value = raw.trim_matches(['"', '\'']).to_owned();
        let literal = self.string_literal(&value);
        let key = self.node(
            literal.range(),
            Expression::Literal(Literal::String(literal)),
        );
        let object = self.identifier_expr_of(source);
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object),
                property: MemberProperty::Computed(Box::new(key)),
                optional: false,
            }),
        )
    }

    fn exclusion_for_name(&mut self, name: &PropertyName) -> ExcludeKey {
        match name {
            PropertyName::Identifier(ident) => {
                ExcludeKey::Name(self.token_text(ident.data().token()).to_owned())
            }
            PropertyName::String(literal) => {
                ExcludeKey::Quoted(self.token_text(literal.data().token()).to_owned())
            }
            PropertyName::Number(number) => {
                ExcludeKey::Name(self.token_text(number.data().token()).to_owned())
            }
            PropertyName::Computed(expr) => match self.literal_key_lexeme(expr) {
                Some(raw) if raw.starts_with('\'') || raw.starts_with('"') => {
                    ExcludeKey::Quoted(raw)
                }
                Some(raw) => ExcludeKey::Name(raw),
                None => ExcludeKey::Name(String::new()),
            },
            _ => ExcludeKey::Name(String::new()),
        }
    }

    /// The written lexeme of a string or numeric literal expression.
    fn literal_key_lexeme(&mut self, expr: &Expr) -> Option<String> {
        match expr.data() {
            Expression::Literal(Literal::String(literal)) => {
                Some(self.token_text(literal.data().token()).to_owned())
            }
            Expression::Literal(Literal::Number(number)) => {
                Some(self.token_text(number.data().token()).to_owned())
            }
            _ => None,
        }
    }

    /// Binds one flattened leaf: a plain declarator, or a default selection
    /// over a temporary read.
    fn flatten_leaf(
        &mut self,
        property: &ObjectBindingProperty,
        member: Expr,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
    ) {
        match property.binding.data() {
            BindingPattern::Identifier(ident) => {
                let value = self.defaulted_read(&property.initializer, member, range, parts);
                parts.push(self.make_declarator(ident.clone(), Some(value), range));
            }
            BindingPattern::Assignment(assignment) => match assignment.left.data() {
                BindingPattern::Identifier(ident) => {
                    let value =
                        self.defaulted_read(&Some(assignment.right.clone()), member, range, parts);
                    parts.push(self.make_declarator(ident.clone(), Some(value), range));
                }
                _ => {
                    let read = self.temp_ident();
                    parts.push(self.make_declarator(read.clone(), Some(member), range));
                    let value = self.default_ternary(&read, &assignment.right, range);
                    let temp = self.temp_ident();
                    parts.push(self.make_declarator(temp.clone(), Some(value), range));
                    parts.extend(self.flatten_subpattern(&assignment.left, &temp, range));
                }
            },
            BindingPattern::Object(_) | BindingPattern::Array(_) => {
                if property.initializer.is_none()
                    && let Some(arg) = pure_rest_binding(&property.binding)
                {
                    let empty = self.exclusion_array(&[], range);
                    let call = self.rest_call_expr(&member, empty, range);
                    parts.push(self.make_declarator(arg.clone(), Some(call), range));
                    return;
                }
                if property.initializer.is_none()
                    && let BindingPattern::Array(array) = property.binding.data()
                {
                    parts.extend(self.flatten_array_elements(&array.elements, member, range));
                    return;
                }
                let read = self.temp_ident();
                parts.push(self.make_declarator(read.clone(), Some(member), range));
                let mut source = read;
                if let Some(initializer) = &property.initializer {
                    let defined = self.temp_ident();
                    let value = self.default_ternary(&source, initializer, range);
                    parts.push(self.make_declarator(defined.clone(), Some(value), range));
                    source = defined;
                }
                parts.extend(self.flatten_subpattern(&property.binding, &source, range));
            }
            BindingPattern::Rest(_) | BindingPattern::Missing(_) => {}
        }
    }

    /// `temp = read` plus `target === void 0 ? default : temp` when a
    /// default exists, otherwise the read itself.
    fn defaulted_read(
        &mut self,
        default: &Option<Box<Expr>>,
        member: Expr,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
    ) -> Expr {
        match default {
            Some(default) => {
                let temp = self.temp_ident();
                parts.push(self.make_declarator(temp.clone(), Some(member), range));
                self.default_ternary(&temp, default, range)
            }
            None => member,
        }
    }

    fn flatten_subpattern(
        &mut self,
        binding: &Pattern,
        source: &IdentifierNode,
        range: TextRange,
    ) -> Vec<VariableDeclaratorNode> {
        match binding.data() {
            BindingPattern::Object(object) => {
                if object_rest_in_pattern(binding) {
                    self.flatten_object_properties(&object.properties, source, true, range)
                } else {
                    vec![self.kept_pattern_declarator(binding, source, range)]
                }
            }
            BindingPattern::Array(array) => {
                if object_rest_in_pattern(binding) {
                    let init = self.identifier_expr_of(source);
                    self.flatten_array_elements(&array.elements, init, range)
                } else {
                    vec![self.kept_pattern_declarator(binding, source, range)]
                }
            }
            _ => Vec::new(),
        }
    }

    /// Array surgery: elements that carry object rest or a default move to
    /// fresh identifiers inside the kept pattern; their bindings follow as
    /// deferred declarators once the kept pattern has run. The kept pattern
    /// binds `init` directly, so an arbitrary member read is consumed once
    /// by the pattern itself.
    fn flatten_array_elements(
        &mut self,
        elements: &[ArrayBindingElement],
        init: Expr,
        range: TextRange,
    ) -> Vec<VariableDeclaratorNode> {
        let mut deferred: Vec<VariableDeclaratorNode> = Vec::new();
        let mut kept: Vec<ArrayBindingElement> = Vec::new();
        for element in elements {
            let ArrayBindingElement::Binding(binding) = element else {
                kept.push(element.clone());
                continue;
            };
            if let BindingPattern::Assignment(assignment) = binding.data() {
                let temp = self.temp_ident();
                let ident = self.node(binding.range(), BindingPattern::Identifier(temp.clone()));
                kept.push(ArrayBindingElement::Binding(ident));
                deferred.extend(self.deferred_default_binding(
                    &assignment.left,
                    &assignment.right,
                    &temp,
                    range,
                ));
            } else if object_rest_in_pattern(binding) {
                let temp = self.temp_ident();
                let ident = self.node(binding.range(), BindingPattern::Identifier(temp.clone()));
                kept.push(ArrayBindingElement::Binding(ident));
                deferred.extend(self.flatten_subpattern(binding, &temp, range));
            } else {
                kept.push(element.clone());
            }
        }
        let mut parts = Vec::new();
        let binds = kept.iter().any(|element| {
            !matches!(
                element,
                ArrayBindingElement::Elision | ArrayBindingElement::Missing(_)
            )
        });
        if binds {
            let pattern = self.node(
                range,
                BindingPattern::Array(ArrayBindingPattern { elements: kept }),
            );
            let declarator = self.node(
                range,
                VariableDeclarator {
                    binding: pattern,
                    definite: false,
                    type_annotation: None,
                    initializer: Some(Box::new(init)),
                },
            );
            parts.push(self.rewrite_declarator_initializer(&declarator));
        }
        parts.extend(deferred);
        parts
    }

    /// `left = temp === void 0 ? default : temp` for an array element that
    /// carried a default into the kept pattern's temporary.
    fn deferred_default_binding(
        &mut self,
        left: &Pattern,
        right: &Expr,
        temp: &IdentifierNode,
        range: TextRange,
    ) -> Vec<VariableDeclaratorNode> {
        let value = self.default_ternary(temp, right, range);
        match left.data() {
            BindingPattern::Identifier(ident) => {
                vec![self.make_declarator(ident.clone(), Some(value), range)]
            }
            _ => {
                let defined = self.temp_ident();
                let mut parts = vec![self.make_declarator(defined.clone(), Some(value), range)];
                if object_rest_in_pattern(left) {
                    parts.extend(self.flatten_subpattern(left, &defined, range));
                } else {
                    parts.push(self.kept_pattern_declarator(left, &defined, range));
                }
                parts
            }
        }
    }

    fn kept_pattern_declarator(
        &mut self,
        binding: &Pattern,
        source: &IdentifierNode,
        range: TextRange,
    ) -> VariableDeclaratorNode {
        let init = self.identifier_expr_of(source);
        let declarator = self.node(
            range,
            VariableDeclarator {
                binding: binding.clone(),
                definite: false,
                type_annotation: None,
                initializer: Some(Box::new(init)),
            },
        );
        self.rewrite_declarator_initializer(&declarator)
    }

    fn flush_kept_pattern(
        &mut self,
        kept: &[ObjectBindingProperty],
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<VariableDeclaratorNode>,
    ) {
        if kept.is_empty() {
            return;
        }
        let pattern = self.node(
            range,
            BindingPattern::Object(ObjectBindingPattern {
                properties: kept.to_vec(),
            }),
        );
        let init = self.identifier_expr_of(source);
        let declarator = self.node(
            range,
            VariableDeclarator {
                binding: pattern,
                definite: false,
                type_annotation: None,
                initializer: Some(Box::new(init)),
            },
        );
        parts.push(self.rewrite_declarator_initializer(&declarator));
    }

    // ================= assignment targets =================

    /// Splits one assignment-object level into kept-group, deep, and rest
    /// assignment expressions.
    fn flatten_assignment_object(
        &mut self,
        properties: &[AssignmentObjectProperty],
        source: &IdentifierNode,
        has_dynamic: bool,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        if has_dynamic {
            self.flatten_assignment_every_property(properties, source, range, parts);
        } else {
            self.flatten_assignment_with_kept(properties, source, range, parts);
        }
    }

    fn flatten_assignment_every_property(
        &mut self,
        properties: &[AssignmentObjectProperty],
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        let mut exclusions: Vec<ExcludeKey> = Vec::new();
        for (index, property) in properties.iter().enumerate() {
            if property.rest {
                if rest_is_last(index, properties.len()) {
                    let excluded = self.exclusion_array(&exclusions, range);
                    let object = self.identifier_expr_of(source);
                    let call = self.rest_call_expr(&object, excluded, range);
                    let target = self.rewrite_assignment_target(&property.target);
                    parts.push(self.assign_target(target, call, range));
                } else if let Some(name) = self.assignment_rest_name(&property.target) {
                    exclusions.push(ExcludeKey::Name(name));
                }
                continue;
            }
            let member =
                self.assignment_level_member(property, source, range, parts, &mut exclusions);
            self.flatten_assignment_leaf(property, member, range, parts);
        }
    }

    fn flatten_assignment_with_kept(
        &mut self,
        properties: &[AssignmentObjectProperty],
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        let mut kept: Vec<AssignmentObjectProperty> = Vec::new();
        let mut exclusions: Vec<ExcludeKey> = Vec::new();
        for (index, property) in properties.iter().enumerate() {
            if property.rest {
                if rest_is_last(index, properties.len()) {
                    self.flush_assignment_kept(&kept, source, range, parts);
                    kept.clear();
                    let excluded = self.exclusion_array(&exclusions, range);
                    let object = self.identifier_expr_of(source);
                    let call = self.rest_call_expr(&object, excluded, range);
                    let target = self.rewrite_assignment_target(&property.target);
                    parts.push(self.assign_target(target, call, range));
                } else if let Some(name) = self.assignment_rest_name(&property.target) {
                    exclusions.push(ExcludeKey::Name(name));
                }
                continue;
            }
            if object_rest_in_target(&property.target) {
                self.flush_assignment_kept(&kept, source, range, parts);
                kept.clear();
                let member =
                    self.assignment_level_member(property, source, range, parts, &mut exclusions);
                self.flatten_assignment_subtarget(property, member, range, parts);
            } else {
                exclusions.push(self.exclusion_for_name(&property.name));
                kept.push(property.clone());
            }
        }
        self.flush_assignment_kept(&kept, source, range, parts);
    }

    /// The member read for one assignment property; a dynamic computed key
    /// evaluates once into a hoisted temporary.
    fn assignment_level_member(
        &mut self,
        property: &AssignmentObjectProperty,
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<Expr>,
        exclusions: &mut Vec<ExcludeKey>,
    ) -> Expr {
        match &property.name {
            PropertyName::Computed(key) if dynamic_key(&property.name) => {
                let temp = self.expression_temp();
                let value = self.rewrite_expr(key);
                parts.push(self.store_temp(&temp, value, range));
                exclusions.push(ExcludeKey::Key(temp.clone()));
                let reference = self.identifier_expr_of(&temp);
                self.member_computed(source, &reference, range)
            }
            name => {
                let member = self.member_for_name(source, name, range);
                exclusions.push(self.exclusion_for_name(name));
                member
            }
        }
    }

    /// The name a dropped assignment rest contributes to later exclusions.
    fn assignment_rest_name(&mut self, target: &AssignmentTargetNode) -> Option<String> {
        match target.data() {
            AssignmentTarget::Identifier(ident) => {
                Some(self.token_text(ident.data().token()).to_owned())
            }
            _ => None,
        }
    }

    /// A property whose target carries object rest: pure-rest object
    /// targets read `__rest` straight off the member, everything else
    /// snapshots the member into a temporary and recurses.
    fn flatten_assignment_subtarget(
        &mut self,
        property: &AssignmentObjectProperty,
        member: Expr,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        if property.initializer.is_none()
            && let AssignmentTarget::Array(array) = property.target.data()
        {
            self.flatten_assignment_array(&array.elements, member, range, parts);
            return;
        }
        if property.initializer.is_none()
            && let AssignmentTarget::Object(object) = property.target.data()
            && object.properties.len() == 1
            && object.properties[0].rest
        {
            let inner = &object.properties[0];
            let empty = self.exclusion_array(&[], range);
            let call = self.rest_call_expr(&member, empty, range);
            let target = self.rewrite_assignment_target(&inner.target);
            parts.push(self.assign_target(target, call, range));
            return;
        }
        let temp = self.expression_temp();
        parts.push(self.store_temp(&temp, member, range));
        let mut source = temp;
        if let Some(initializer) = &property.initializer {
            let defined = self.expression_temp();
            let value = self.default_ternary(&source, initializer, range);
            parts.push(self.store_temp(&defined, value, range));
            source = defined;
        }
        self.flatten_assignment_target_parts(&property.target, &source, range, parts);
    }

    /// One property in the flattened (dynamic-key) assignment path: every
    /// target binds the member read directly, patterns recurse through a
    /// temporary.
    fn flatten_assignment_leaf(
        &mut self,
        property: &AssignmentObjectProperty,
        member: Expr,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        match property.target.data() {
            AssignmentTarget::Object(_) | AssignmentTarget::Array(_) => {
                let temp = self.expression_temp();
                parts.push(self.store_temp(&temp, member, range));
                let mut source = temp;
                if let Some(initializer) = &property.initializer {
                    let defined = self.expression_temp();
                    let value = self.default_ternary(&source, initializer, range);
                    parts.push(self.store_temp(&defined, value, range));
                    source = defined;
                }
                self.flatten_assignment_target_parts(&property.target, &source, range, parts);
            }
            _ => {
                if let Some(initializer) = &property.initializer {
                    let temp = self.expression_temp();
                    parts.push(self.store_temp(&temp, member, range));
                    let value = self.default_ternary(&temp, initializer, range);
                    let target = self.rewrite_assignment_target(&property.target);
                    parts.push(self.assign_target(target, value, range));
                } else {
                    let target = self.rewrite_assignment_target(&property.target);
                    parts.push(self.assign_target(target, member, range));
                }
            }
        }
    }

    /// Array-target surgery mirroring [`Self::flatten_array_elements`]:
    /// rest-carrying and defaulted elements become temporaries inside the
    /// kept pattern, their bindings follow as sequence parts. The kept
    /// pattern is assigned `value` directly, so an arbitrary member read is
    /// consumed once by the pattern itself.
    fn flatten_assignment_array(
        &mut self,
        elements: &[AssignmentArrayElement],
        value: Expr,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        let mut kept: Vec<AssignmentArrayElement> = Vec::new();
        let mut deferred: Vec<DeferredElement> = Vec::new();
        for element in elements {
            match element {
                AssignmentArrayElement::Target(target) if object_rest_in_target(target) => {
                    let temp = self.expression_temp();
                    kept.push(AssignmentArrayElement::Target(
                        self.node(target.range(), AssignmentTarget::Identifier(temp.clone())),
                    ));
                    deferred.push(DeferredElement::Rest(target, temp));
                }
                AssignmentArrayElement::Target(target) => {
                    let Some((left, right)) = default_assignment_target(target) else {
                        kept.push(element.clone());
                        continue;
                    };
                    let temp = self.expression_temp();
                    kept.push(AssignmentArrayElement::Target(
                        self.node(target.range(), AssignmentTarget::Identifier(temp.clone())),
                    ));
                    deferred.push(DeferredElement::Default(left, right, temp));
                }
                other => kept.push(other.clone()),
            }
        }
        let elements = kept
            .iter()
            .map(|element| match element {
                AssignmentArrayElement::Target(target) => {
                    AssignmentArrayElement::Target(self.rewrite_assignment_target(target))
                }
                AssignmentArrayElement::Rest(target) => {
                    AssignmentArrayElement::Rest(self.rewrite_assignment_target(target))
                }
                other => other.clone(),
            })
            .collect();
        let pattern = self.node(
            range,
            AssignmentTarget::Array(AssignmentArrayPattern { elements }),
        );
        parts.push(self.assign_target(pattern, value, range));
        for deferred_element in deferred {
            match deferred_element {
                DeferredElement::Rest(target, temp) => {
                    self.flatten_assignment_target_parts(target, &temp, range, parts);
                }
                DeferredElement::Default(left, right, temp) => {
                    self.flatten_assignment_default(left, right, &temp, range, parts);
                }
            }
        }
    }

    /// `left = temp === void 0 ? default : temp` for an array element whose
    /// default moved into the kept pattern's temporary.
    fn flatten_assignment_default(
        &mut self,
        target: &AssignmentTargetNode,
        right: &Expr,
        temp: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        let value = self.default_ternary(temp, right, range);
        match target.data() {
            AssignmentTarget::Identifier(_) | AssignmentTarget::Member(_) => {
                let rewritten = self.rewrite_assignment_target(target);
                parts.push(self.assign_target(rewritten, value, range));
            }
            _ => {
                let defined = self.expression_temp();
                parts.push(self.store_temp(&defined, value, range));
                self.flatten_assignment_target_parts(target, &defined, range, parts);
            }
        }
    }

    fn flush_assignment_kept(
        &mut self,
        kept: &[AssignmentObjectProperty],
        source: &IdentifierNode,
        range: TextRange,
        parts: &mut Vec<Expr>,
    ) {
        if kept.is_empty() {
            return;
        }
        let properties = kept
            .iter()
            .map(|property| AssignmentObjectProperty {
                name: self.rewrite_property_name(&property.name),
                target: self.rewrite_assignment_target(&property.target),
                initializer: property
                    .initializer
                    .as_deref()
                    .map(|value| Box::new(self.rewrite_expr(value))),
                rest: property.rest,
            })
            .collect();
        let pattern = self.node(
            range,
            AssignmentTarget::Object(AssignmentObjectPattern { properties }),
        );
        let source_value = self.identifier_expr_of(source);
        parts.push(self.assign_target(pattern, source_value, range));
    }

    // ================= helpers =================

    fn exclusion_array(&mut self, keys: &[ExcludeKey], range: TextRange) -> Expr {
        let mut elements = Vec::new();
        for key in keys {
            let expr = match key {
                ExcludeKey::Name(name) => {
                    let literal = self.string_literal(name);
                    self.node(
                        literal.range(),
                        Expression::Literal(Literal::String(literal)),
                    )
                }
                ExcludeKey::Quoted(lexeme) => {
                    let literal = self.raw_string_literal(lexeme);
                    self.node(
                        literal.range(),
                        Expression::Literal(Literal::String(literal)),
                    )
                }
                ExcludeKey::Key(temp) => {
                    let reference = self.identifier_expr_of(temp);
                    let symbol = self.string_literal("symbol");
                    let symbol_expr =
                        self.node(symbol.range(), Expression::Literal(Literal::String(symbol)));
                    let typeof_expr = self.node(
                        temp.range(),
                        Expression::Unary(UnaryExpression {
                            operator: UnaryOperator::Typeof,
                            argument: Box::new(reference.clone()),
                        }),
                    );
                    let test = self.node(
                        temp.range(),
                        Expression::Binary(BinaryExpression {
                            operator: BinaryOperator::StrictEqual,
                            left: Box::new(typeof_expr),
                            right: Box::new(symbol_expr),
                        }),
                    );
                    let empty = self.string_literal("");
                    let empty_expr =
                        self.node(empty.range(), Expression::Literal(Literal::String(empty)));
                    let concat = self.node(
                        temp.range(),
                        Expression::Binary(BinaryExpression {
                            operator: BinaryOperator::Add,
                            left: Box::new(reference),
                            right: Box::new(empty_expr),
                        }),
                    );
                    let consequent = self.identifier_expr_of(temp);
                    self.node(
                        temp.range(),
                        Expression::Conditional(ConditionalExpression {
                            test: Box::new(test),
                            consequent: Box::new(consequent),
                            alternate: Box::new(concat),
                        }),
                    )
                }
            };
            elements.push(ArrayElement::Expression(Box::new(expr)));
        }
        self.node(range, Expression::Array(ArrayLiteral { elements }))
    }

    /// `__rest(object, excluded)` over an arbitrary object expression.
    fn rest_call_expr(&mut self, object: &Expr, excluded: Expr, range: TextRange) -> Expr {
        let callee = self.helper_ident(HelperKind::Rest);
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(object.clone())),
                    CallArgument::Expression(Box::new(excluded)),
                ],
            }),
        )
    }

    /// A string literal emitted with the lexeme it carries, so a key written
    /// `'b'` keeps single quotes in the exclusion array.
    fn raw_string_literal(&mut self, lexeme: &str) -> StringLiteralNode {
        let range = self.bank.intern(lexeme);
        let token = Token::new(TokenKind::StringLiteral, range);
        Node::new(self.alloc_id(), range, StringLiteral::new(token))
    }
}

/// One deferred array-element binding, kept in source order behind the
/// kept pattern's assignment.
enum DeferredElement<'a> {
    Rest(&'a AssignmentTargetNode, IdentifierNode),
    Default(&'a AssignmentTargetNode, &'a Expr, IdentifierNode),
}

/// The default an assignment array element folded into its target carries:
/// `[b = a]` arrives as an invalid target wrapping the assignment.
fn default_assignment_target(
    target: &AssignmentTargetNode,
) -> Option<(&AssignmentTargetNode, &Expr)> {
    let AssignmentTarget::Invalid(expr) = target.data() else {
        return None;
    };
    let Expression::Assignment(assignment) = expr.data() else {
        return None;
    };
    if assignment.operator != AssignmentOperator::Assign {
        return None;
    }
    Some((&assignment.left, &assignment.right))
}
