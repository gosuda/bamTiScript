//! Overload declaration validation and call-signature resolution.
//!
//! The resolver consumes already-bound types. It preserves declaration order,
//! instantiates generic candidates through the checker inference engine, and
//! attributes argument failures to the argument that made a candidate fail.

use std::collections::BTreeMap;

use crate::checker::{SymbolId, TypeId, TypeTable};
use crate::diagnostic::{Diagnostic, DiagnosticCode, SecondarySpan};
use crate::source::{SourceId, TextRange};

use super::enum_namespace::DeclarationSite;
use super::inference::{
    InferenceContext, InferenceParameter, InferenceProvenance, InferredTypeArgument,
    InferredTypeArguments,
};

/// No declared overload accepted the call.
pub const NO_OVERLOAD_MATCHES: DiagnosticCode = DiagnosticCode::new("BAMTS-C050");
/// A call supplied too few or too many arguments.
pub const ARGUMENT_COUNT_MISMATCH: DiagnosticCode = DiagnosticCode::new("BAMTS-C051");
/// A call argument is not assignable to its corresponding parameter.
pub const ARGUMENT_NOT_ASSIGNABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C052");
/// Explicit type arguments do not satisfy a candidate's type parameters.
pub const TYPE_ARGUMENT_COUNT_MISMATCH: DiagnosticCode = DiagnosticCode::new("BAMTS-C053");
/// An implementation signature cannot implement one of its overloads.
pub const IMPLEMENTATION_NOT_COMPATIBLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C054");
/// Overload declarations have no implementation signature.
pub const OVERLOAD_MISSING_IMPLEMENTATION: DiagnosticCode = DiagnosticCode::new("BAMTS-C055");

const NO_MATCH_MESSAGE: &str = "No overload matches this call.";
const ARGUMENT_COUNT_MESSAGE: &str = "No overload expects this number of arguments.";
const ARGUMENT_TYPE_MESSAGE: &str = "Argument type is not assignable to the parameter type.";
const TYPE_ARGUMENT_COUNT_MESSAGE: &str =
    "Type argument count does not match the overload's type parameters.";
const IMPLEMENTATION_MESSAGE: &str =
    "Implementation signature is not compatible with the overload signature.";
const MISSING_IMPLEMENTATION_MESSAGE: &str =
    "Overload declarations must be followed by an implementation signature.";

/// The arity behavior of one parameter.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ParameterKind {
    /// The caller must supply this argument.
    Required,
    /// The caller may omit this trailing argument.
    Optional,
    /// Zero or more trailing arguments use this element type.
    Rest,
}

/// One parameter in an overload or implementation signature.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Parameter {
    type_id: TypeId,
    kind: ParameterKind,
}

impl Parameter {
    /// Creates a required parameter.
    #[must_use]
    pub const fn required(type_id: TypeId) -> Self {
        Self {
            type_id,
            kind: ParameterKind::Required,
        }
    }

    /// Creates an optional parameter.
    #[must_use]
    pub const fn optional(type_id: TypeId) -> Self {
        Self {
            type_id,
            kind: ParameterKind::Optional,
        }
    }

    /// Creates a rest parameter whose type is the repeated element type.
    #[must_use]
    pub const fn rest(type_id: TypeId) -> Self {
        Self {
            type_id,
            kind: ParameterKind::Rest,
        }
    }

    /// Returns the declared parameter type.
    #[must_use]
    pub const fn type_id(self) -> TypeId {
        self.type_id
    }
}

/// A bound callable signature and its declaration site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Signature {
    parameters: Vec<Parameter>,
    return_type: TypeId,
    type_parameters: Vec<InferenceParameter>,
    declaration: DeclarationSite,
}

impl Signature {
    /// Creates a non-generic signature.
    #[must_use]
    pub fn new(
        parameters: Vec<Parameter>,
        return_type: TypeId,
        declaration: DeclarationSite,
    ) -> Self {
        Self {
            parameters,
            return_type,
            type_parameters: Vec::new(),
            declaration,
        }
    }

    /// Adds the signature's generic type parameters in declaration order.
    #[must_use]
    pub fn with_type_parameters(mut self, type_parameters: Vec<InferenceParameter>) -> Self {
        self.type_parameters = type_parameters;
        self
    }

    /// Returns this signature's parameters.
    #[must_use]
    pub fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }

    /// Returns this signature's return type before generic instantiation.
    #[must_use]
    pub const fn return_type(&self) -> TypeId {
        self.return_type
    }

    fn minimum_arity(&self) -> usize {
        self.parameters
            .iter()
            .take_while(|parameter| parameter.kind == ParameterKind::Required)
            .count()
    }

    fn maximum_arity(&self) -> Option<usize> {
        if self
            .parameters
            .last()
            .is_some_and(|parameter| parameter.kind == ParameterKind::Rest)
        {
            None
        } else {
            Some(self.parameters.len())
        }
    }

    fn parameter_at(&self, index: usize) -> Option<Parameter> {
        self.parameters.get(index).copied().or_else(|| {
            self.parameters
                .last()
                .copied()
                .filter(|parameter| parameter.kind == ParameterKind::Rest)
        })
    }
}

/// An ordered overload declaration set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OverloadSet {
    signatures: Vec<Signature>,
}

impl OverloadSet {
    /// Creates an overload set. Declaration order is resolution order.
    #[must_use]
    pub fn new(signatures: Vec<Signature>) -> Self {
        Self { signatures }
    }
}

/// One bound call argument and the source span that produced it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallArgument {
    type_id: TypeId,
    range: TextRange,
}

impl CallArgument {
    /// Creates a call argument.
    #[must_use]
    pub const fn new(type_id: TypeId, range: TextRange) -> Self {
        Self { type_id, range }
    }
}

/// Already-bound inputs for one call expression.
#[derive(Clone, Copy, Debug)]
pub struct CallSite<'a> {
    source: SourceId,
    range: TextRange,
    arguments: &'a [CallArgument],
    explicit_type_arguments: Option<&'a [TypeId]>,
    contextual_return: Option<TypeId>,
}

impl<'a> CallSite<'a> {
    /// Creates a call without explicit type arguments or contextual return type.
    #[must_use]
    pub const fn new(source: SourceId, range: TextRange, arguments: &'a [CallArgument]) -> Self {
        Self {
            source,
            range,
            arguments,
            explicit_type_arguments: None,
            contextual_return: None,
        }
    }

    /// Supplies explicit type arguments, including an explicitly empty list.
    #[must_use]
    pub const fn with_type_arguments(mut self, arguments: &'a [TypeId]) -> Self {
        self.explicit_type_arguments = Some(arguments);
        self
    }
    #[cfg(test)]
    /// Supplies a contextual return type for generic inference.
    #[must_use]
    pub const fn with_contextual_return(mut self, return_type: TypeId) -> Self {
        self.contextual_return = Some(return_type);
        self
    }
}

/// The selected call signature or the recovered error result.
#[derive(Clone, Debug)]
pub struct CallResolution {
    signature_index: Option<usize>,
    return_type: TypeId,
    substitution: BTreeMap<SymbolId, TypeId>,
    diagnostics: Vec<Diagnostic>,
}

impl CallResolution {
    /// Returns the selected declaration index.
    #[must_use]
    pub const fn signature_index(&self) -> Option<usize> {
        self.signature_index
    }

    /// Returns the selected, instantiated return type.
    #[must_use]
    pub const fn return_type(&self) -> TypeId {
        self.return_type
    }

    /// Returns inferred or explicit generic substitutions.
    #[must_use]
    pub const fn substitution(&self) -> &BTreeMap<SymbolId, TypeId> {
        &self.substitution
    }

    /// Returns call diagnostics.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Returns whether resolution failed.
    #[must_use]
    pub const fn has_errors(&self) -> bool {
        !self.diagnostics.is_empty()
    }
}

#[derive(Clone, Copy, Debug)]
enum CandidateFailure {
    Arity,
    TypeArguments,
    Argument(usize),
}

impl CandidateFailure {
    fn range(self, call: CallSite<'_>) -> TextRange {
        match self {
            Self::Argument(index) => call.arguments[index].range,
            Self::Arity | Self::TypeArguments => call.range,
        }
    }
}

struct CandidateMatch {
    return_type: TypeId,
    substitution: BTreeMap<SymbolId, TypeId>,
}

/// Resolves a call against overloads in declaration order.
///
/// The first applicable signature wins. A rejected generic candidate does not
/// leak inference diagnostics when a later overload succeeds.
#[must_use]
pub fn resolve_call(
    table: &mut TypeTable,
    overloads: &OverloadSet,
    call: CallSite<'_>,
) -> CallResolution {
    let mut failures = Vec::with_capacity(overloads.signatures.len());
    for (index, signature) in overloads.signatures.iter().enumerate() {
        match match_candidate(table, signature, call) {
            Ok(candidate) => {
                return CallResolution {
                    signature_index: Some(index),
                    return_type: candidate.return_type,
                    substitution: candidate.substitution,
                    diagnostics: Vec::new(),
                };
            }
            Err(failure) => failures.push((signature, failure)),
        }
    }

    let diagnostic = no_match_diagnostic(call, &failures);
    CallResolution {
        signature_index: None,
        return_type: table.error_type(),
        substitution: BTreeMap::new(),
        diagnostics: vec![diagnostic],
    }
}

fn match_candidate(
    table: &mut TypeTable,
    signature: &Signature,
    call: CallSite<'_>,
) -> Result<CandidateMatch, CandidateFailure> {
    if call.arguments.len() < signature.minimum_arity()
        || signature
            .maximum_arity()
            .is_some_and(|maximum| call.arguments.len() > maximum)
    {
        return Err(CandidateFailure::Arity);
    }

    let substitution = match call.explicit_type_arguments {
        Some(arguments) => explicit_substitution(table, signature, arguments)?,
        None if signature.type_parameters.is_empty() => BTreeMap::new(),
        None => inferred_substitution(table, signature, call)?,
    };

    for (index, argument) in call.arguments.iter().enumerate() {
        let parameter = signature
            .parameter_at(index)
            .expect("arity validation guarantees a parameter");
        let expected = instantiate_type(table, parameter.type_id, &substitution);
        if !table.assignable(argument.type_id, expected) {
            return Err(CandidateFailure::Argument(index));
        }
    }

    Ok(CandidateMatch {
        return_type: instantiate_type(table, signature.return_type, &substitution),
        substitution,
    })
}

fn explicit_substitution(
    table: &mut TypeTable,
    signature: &Signature,
    arguments: &[TypeId],
) -> Result<BTreeMap<SymbolId, TypeId>, CandidateFailure> {
    let required = signature
        .type_parameters
        .iter()
        .filter(|parameter| parameter.default().is_none())
        .count();
    if arguments.len() < required || arguments.len() > signature.type_parameters.len() {
        return Err(CandidateFailure::TypeArguments);
    }

    let mut substitution = BTreeMap::new();
    for (index, parameter) in signature.type_parameters.iter().enumerate() {
        let type_id = match arguments.get(index).copied() {
            Some(type_id) => type_id,
            None => {
                let default = parameter
                    .default()
                    .expect("required type argument count was validated");
                instantiate_type(table, default, &substitution)
            }
        };
        if let Some(constraint) = parameter.constraint() {
            let constraint = instantiate_type(table, constraint, &substitution);
            if !table.assignable(type_id, constraint) {
                return Err(CandidateFailure::TypeArguments);
            }
        }
        substitution.insert(parameter.symbol(), type_id);
    }
    Ok(substitution)
}

fn inferred_substitution(
    table: &mut TypeTable,
    signature: &Signature,
    call: CallSite<'_>,
) -> Result<BTreeMap<SymbolId, TypeId>, CandidateFailure> {
    let mut inference = InferenceContext::new(table, &signature.type_parameters);
    for (index, argument) in call.arguments.iter().enumerate() {
        let parameter = signature
            .parameter_at(index)
            .expect("arity validation guarantees a parameter");
        inference.infer_from_argument(parameter.type_id, argument.type_id, index as u32);
    }
    if let Some(contextual_return) = call.contextual_return {
        inference.infer_from_argument(signature.return_type, contextual_return, u32::MAX);
    }
    let mut inferred = inference.resolve();
    inferred.widen_unconstrained_literals(table, &signature.type_parameters, signature.return_type);
    Ok(inferred
        .arguments()
        .iter()
        .map(|argument| (argument.symbol(), argument.type_id()))
        .collect())
}

fn no_match_diagnostic(
    call: CallSite<'_>,
    failures: &[(&Signature, CandidateFailure)],
) -> Diagnostic {
    let Some((signature, failure)) = failures
        .iter()
        .find(|(_, failure)| matches!(failure, CandidateFailure::Argument(_)))
        .or_else(|| failures.first())
    else {
        return Diagnostic::error(
            NO_OVERLOAD_MATCHES,
            call.source,
            call.range,
            NO_MATCH_MESSAGE,
        )
        .with_note("The callable has no overload declarations.");
    };

    let code = if failures.len() == 1 {
        match failure {
            CandidateFailure::Arity => ARGUMENT_COUNT_MISMATCH,
            CandidateFailure::TypeArguments => TYPE_ARGUMENT_COUNT_MISMATCH,
            CandidateFailure::Argument(_) => ARGUMENT_NOT_ASSIGNABLE,
        }
    } else {
        NO_OVERLOAD_MATCHES
    };
    let message = match code {
        ARGUMENT_COUNT_MISMATCH => ARGUMENT_COUNT_MESSAGE,
        TYPE_ARGUMENT_COUNT_MISMATCH => TYPE_ARGUMENT_COUNT_MESSAGE,
        ARGUMENT_NOT_ASSIGNABLE => ARGUMENT_TYPE_MESSAGE,
        _ => NO_MATCH_MESSAGE,
    };
    Diagnostic::error(code, call.source, failure.range(call), message).with_secondary_span(
        SecondarySpan::new(
            signature.declaration.source(),
            signature.declaration.range(),
            "Candidate overload is declared here.",
        ),
    )
}

/// Validates overload declarations against their implementation signature.
///
/// Parameter domains are contravariant: an implementation must accept every
/// argument accepted by each overload. Return types may be narrower or broader
/// when one is assignable to the other, matching TypeScript's implementation
/// compatibility concession for overload declarations.
#[must_use]
pub fn check_implementation(
    table: &mut TypeTable,
    overloads: &OverloadSet,
    implementation: Option<&Signature>,
) -> Vec<Diagnostic> {
    let Some(implementation) = implementation else {
        let Some(first) = overloads.signatures.first() else {
            return Vec::new();
        };
        return vec![Diagnostic::error(
            OVERLOAD_MISSING_IMPLEMENTATION,
            first.declaration.source(),
            first.declaration.range(),
            MISSING_IMPLEMENTATION_MESSAGE,
        )];
    };

    let mut diagnostics = Vec::new();
    for overload in &overloads.signatures {
        if implementation_accepts(table, implementation, overload) {
            continue;
        }
        diagnostics.push(
            Diagnostic::error(
                IMPLEMENTATION_NOT_COMPATIBLE,
                overload.declaration.source(),
                overload.declaration.range(),
                IMPLEMENTATION_MESSAGE,
            )
            .with_secondary_span(SecondarySpan::new(
                implementation.declaration.source(),
                implementation.declaration.range(),
                "Implementation signature is declared here.",
            )),
        );
    }
    diagnostics
}

fn implementation_accepts(
    table: &mut TypeTable,
    implementation: &Signature,
    overload: &Signature,
) -> bool {
    if implementation.minimum_arity() > overload.minimum_arity() {
        return false;
    }
    if let Some(overload_maximum) = overload.maximum_arity() {
        if implementation
            .maximum_arity()
            .is_some_and(|implementation_maximum| implementation_maximum < overload_maximum)
        {
            return false;
        }
    } else if implementation.maximum_arity().is_some() {
        return false;
    }

    let implementation_types = erased_substitution(table, &implementation.type_parameters);
    let overload_types = erased_substitution(table, &overload.type_parameters);
    for (index, overload_parameter) in overload.parameters.iter().enumerate() {
        let Some(implementation_parameter) = implementation.parameter_at(index) else {
            return false;
        };
        let overload_type = instantiate_type(table, overload_parameter.type_id, &overload_types);
        let implementation_type = instantiate_type(
            table,
            implementation_parameter.type_id,
            &implementation_types,
        );
        if !table.assignable(overload_type, implementation_type) {
            return false;
        }
    }

    let implementation_return =
        instantiate_type(table, implementation.return_type, &implementation_types);
    let overload_return = instantiate_type(table, overload.return_type, &overload_types);
    table.assignable(implementation_return, overload_return)
        || table.assignable(overload_return, implementation_return)
}

fn erased_substitution(
    table: &mut TypeTable,
    parameters: &[InferenceParameter],
) -> BTreeMap<SymbolId, TypeId> {
    let mut substitution = BTreeMap::new();
    for parameter in parameters {
        let erased = parameter
            .constraint()
            .map(|constraint| instantiate_type(table, constraint, &substitution))
            .unwrap_or_else(|| table.any());
        substitution.insert(parameter.symbol(), erased);
    }
    substitution
}

fn instantiate_type(
    table: &mut TypeTable,
    type_id: TypeId,
    substitution: &BTreeMap<SymbolId, TypeId>,
) -> TypeId {
    let arguments = substitution
        .iter()
        .map(|(&symbol, &type_id)| {
            InferredTypeArgument::new(symbol, type_id, InferenceProvenance::Inferred)
        })
        .collect();
    InferredTypeArguments::new(arguments).instantiate(table, type_id)
}

#[cfg(test)]
mod tests {
    use super::{
        ARGUMENT_COUNT_MISMATCH, ARGUMENT_NOT_ASSIGNABLE, CallArgument, CallSite,
        IMPLEMENTATION_NOT_COMPATIBLE, NO_OVERLOAD_MATCHES, OVERLOAD_MISSING_IMPLEMENTATION,
        OverloadSet, Parameter, Signature, TYPE_ARGUMENT_COUNT_MISMATCH, check_implementation,
        resolve_call,
    };
    use crate::checker::{PropertyType, SymbolId, TypeTable};
    use crate::source::{SourceId, TextRange, Utf16Pos};

    use super::super::enum_namespace::DeclarationSite;
    use super::super::inference::InferenceParameter;

    fn range(start: usize, end: usize) -> TextRange {
        TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered range")
    }

    fn site(start: usize) -> DeclarationSite {
        DeclarationSite::new(SourceId::new(1), range(start, start + 1))
    }

    fn type_parameter(
        symbol: SymbolId,
        constraint: Option<crate::checker::TypeId>,
        default: Option<crate::checker::TypeId>,
    ) -> InferenceParameter {
        let parameter = InferenceParameter::new(symbol);
        let parameter = constraint.map_or(parameter, |constraint| {
            parameter.with_constraint(constraint)
        });
        default.map_or(parameter, |default| parameter.with_default(default))
    }

    fn argument(type_id: crate::checker::TypeId, start: usize) -> CallArgument {
        CallArgument::new(type_id, range(start, start + 1))
    }

    fn call<'a>(arguments: &'a [CallArgument]) -> CallSite<'a> {
        CallSite::new(SourceId::new(1), range(10, 20), arguments)
    }

    fn codes(resolution: &super::CallResolution) -> Vec<&str> {
        resolution
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    #[test]
    fn declaration_order_is_first_match_wins() {
        let mut table = TypeTable::new();
        let any = table.any();
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![Parameter::required(any)], string, site(1)),
            Signature::new(vec![Parameter::required(number)], number, site(2)),
        ]);
        let arguments = [argument(number, 12)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));
        assert_eq!(resolution.signature_index(), Some(0));
        assert_eq!(resolution.return_type(), string);
    }

    #[test]
    fn later_candidate_is_selected_after_type_rejection() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![Parameter::required(string)], string, site(1)),
            Signature::new(vec![Parameter::required(number)], number, site(2)),
        ]);
        let arguments = [argument(number, 12)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));
        assert_eq!(resolution.signature_index(), Some(1));
        assert_eq!(resolution.return_type(), number);
        assert!(!resolution.has_errors());
    }

    #[test]
    fn required_parameter_rejects_too_few_arguments() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::required(number)],
            number,
            site(1),
        )]);
        let resolution = resolve_call(&mut table, &overloads, call(&[]));
        assert_eq!(codes(&resolution), [ARGUMENT_COUNT_MISMATCH.as_str()]);
    }

    #[test]
    fn fixed_arity_rejects_too_many_arguments() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::required(number)],
            number,
            site(1),
        )]);
        let arguments = [argument(number, 12), argument(number, 14)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));
        assert_eq!(codes(&resolution), [ARGUMENT_COUNT_MISMATCH.as_str()]);
    }

    #[test]
    fn optional_parameter_may_be_omitted() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::required(number), Parameter::optional(number)],
            number,
            site(1),
        )]);
        let arguments = [argument(number, 12)];
        assert!(!resolve_call(&mut table, &overloads, call(&arguments)).has_errors());
    }

    #[test]
    fn rest_parameter_accepts_zero_or_many_arguments() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::rest(number)],
            number,
            site(1),
        )]);
        assert!(!resolve_call(&mut table, &overloads, call(&[])).has_errors());
        let arguments = [
            argument(number, 12),
            argument(number, 14),
            argument(number, 16),
        ];
        assert!(!resolve_call(&mut table, &overloads, call(&arguments)).has_errors());
    }

    #[test]
    fn rest_parameter_checks_each_argument() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::rest(number)],
            number,
            site(1),
        )]);
        let arguments = [argument(number, 12), argument(string, 14)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));
        assert_eq!(codes(&resolution), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
        assert_eq!(resolution.diagnostics()[0].range(), range(14, 15));
    }

    #[test]
    fn generic_candidate_infers_and_instantiates_return_type() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(
                vec![Parameter::required(parameter_type)],
                parameter_type,
                site(1),
            )
            .with_type_parameters(vec![type_parameter(parameter_symbol, None, None)]),
        ]);
        let arguments = [argument(string, 12)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));
        assert_eq!(resolution.return_type(), string);
        assert_eq!(
            resolution.substitution().get(&parameter_symbol),
            Some(&string)
        );
    }

    #[test]
    fn generic_candidate_infers_through_object_shape() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let string = table.string();
        let expected = table.object_type(vec![PropertyType::new("value", false, parameter_type)]);
        let actual = table.object_type(vec![PropertyType::new("value", false, string)]);
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![Parameter::required(expected)], parameter_type, site(1))
                .with_type_parameters(vec![type_parameter(parameter_symbol, None, None)]),
        ]);
        let arguments = [argument(actual, 12)];
        assert_eq!(
            resolve_call(&mut table, &overloads, call(&arguments)).return_type(),
            string
        );
    }

    #[test]
    fn contextual_return_participates_in_generic_inference() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![], parameter_type, site(1))
                .with_type_parameters(vec![type_parameter(parameter_symbol, None, None)]),
        ]);
        let resolution = resolve_call(
            &mut table,
            &overloads,
            call(&[]).with_contextual_return(string),
        );
        assert_eq!(resolution.return_type(), string);
    }

    #[test]
    fn explicit_type_argument_instantiates_signature() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(
                vec![Parameter::required(parameter_type)],
                parameter_type,
                site(1),
            )
            .with_type_parameters(vec![type_parameter(parameter_symbol, None, None)]),
        ]);
        let arguments = [argument(string, 12)];
        let type_arguments = [string];
        let resolution = resolve_call(
            &mut table,
            &overloads,
            call(&arguments).with_type_arguments(&type_arguments),
        );
        assert_eq!(resolution.return_type(), string);
    }

    #[test]
    fn explicit_type_argument_count_is_checked() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let number = table.number();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![], number, site(1)).with_type_parameters(vec![type_parameter(
                parameter_symbol,
                None,
                None,
            )]),
        ]);
        let resolution = resolve_call(&mut table, &overloads, call(&[]).with_type_arguments(&[]));
        assert_eq!(codes(&resolution), [TYPE_ARGUMENT_COUNT_MISMATCH.as_str()]);
    }

    #[test]
    fn explicit_type_argument_default_fills_trailing_parameter() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![], parameter_type, site(1))
                .with_type_parameters(vec![type_parameter(parameter_symbol, None, Some(string))]),
        ]);
        let resolution = resolve_call(&mut table, &overloads, call(&[]).with_type_arguments(&[]));
        assert_eq!(resolution.return_type(), string);
    }

    #[test]
    fn explicit_type_argument_constraint_is_checked() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![], parameter_type, site(1))
                .with_type_parameters(vec![type_parameter(parameter_symbol, Some(number), None)]),
        ]);
        let type_arguments = [string];
        let resolution = resolve_call(
            &mut table,
            &overloads,
            call(&[]).with_type_arguments(&type_arguments),
        );
        assert_eq!(codes(&resolution), [TYPE_ARGUMENT_COUNT_MISMATCH.as_str()]);
    }

    #[test]
    fn inferred_type_argument_constraint_failure_reports_argument_diagnostic() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(
                vec![Parameter::required(parameter_type)],
                parameter_type,
                site(1),
            )
            .with_type_parameters(vec![type_parameter(
                parameter_symbol,
                Some(number),
                None,
            )]),
        ]);
        let arguments = [argument(string, 12)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));

        assert_eq!(codes(&resolution), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
        assert_eq!(resolution.diagnostics()[0].range(), range(12, 13));
    }

    #[test]
    fn uninferred_generic_uses_unknown_fallback() {
        let mut table = TypeTable::new();
        let parameter_symbol = SymbolId::new(80);
        let parameter_type = table.named(parameter_symbol);
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![], parameter_type, site(1))
                .with_type_parameters(vec![type_parameter(parameter_symbol, None, None)]),
            Signature::new(vec![], string, site(2)),
        ]);
        let resolution = resolve_call(&mut table, &overloads, call(&[]));
        assert_eq!(resolution.signature_index(), Some(0));
        assert_eq!(resolution.return_type(), table.unknown());
        assert!(!resolution.has_errors());
    }

    #[test]
    fn multi_candidate_failure_uses_no_overload_code_and_argument_span() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let boolean = table.boolean();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![Parameter::required(number)], number, site(1)),
            Signature::new(vec![Parameter::required(string)], string, site(2)),
        ]);
        let arguments = [argument(boolean, 12)];
        let resolution = resolve_call(&mut table, &overloads, call(&arguments));
        assert_eq!(codes(&resolution), [NO_OVERLOAD_MATCHES.as_str()]);
        assert_eq!(resolution.diagnostics()[0].range(), range(12, 13));
    }

    #[test]
    fn empty_overload_set_recovers_with_no_match() {
        let mut table = TypeTable::new();
        let resolution = resolve_call(&mut table, &OverloadSet::new(vec![]), call(&[]));
        assert_eq!(codes(&resolution), [NO_OVERLOAD_MATCHES.as_str()]);
        assert_eq!(resolution.return_type(), table.error_type());
    }

    #[test]
    fn implementation_must_accept_every_overload_parameter() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::required(number)],
            number,
            site(1),
        )]);
        let implementation = Signature::new(vec![Parameter::required(string)], number, site(5));
        let diagnostics = check_implementation(&mut table, &overloads, Some(&implementation));
        assert_eq!(
            diagnostics[0].code().as_str(),
            IMPLEMENTATION_NOT_COMPATIBLE.as_str()
        );
    }

    #[test]
    fn implementation_may_accept_a_broader_parameter_and_return_union() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let union = table.union(&[number, string]);
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![Parameter::required(number)], number, site(1)),
            Signature::new(vec![Parameter::required(string)], string, site(2)),
        ]);
        let implementation = Signature::new(vec![Parameter::required(union)], union, site(5));
        assert!(check_implementation(&mut table, &overloads, Some(&implementation)).is_empty());
    }

    #[test]
    fn implementation_arity_must_cover_overload_arity() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::required(number), Parameter::optional(number)],
            number,
            site(1),
        )]);
        let implementation = Signature::new(vec![Parameter::required(number)], number, site(5));
        assert_eq!(
            check_implementation(&mut table, &overloads, Some(&implementation))[0]
                .code()
                .as_str(),
            IMPLEMENTATION_NOT_COMPATIBLE.as_str()
        );
    }

    #[test]
    fn rest_overload_requires_rest_implementation() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::rest(number)],
            number,
            site(1),
        )]);
        let implementation = Signature::new(vec![Parameter::optional(number)], number, site(5));
        assert_eq!(
            check_implementation(&mut table, &overloads, Some(&implementation))[0]
                .code()
                .as_str(),
            IMPLEMENTATION_NOT_COMPATIBLE.as_str()
        );
    }

    #[test]
    fn each_incompatible_overload_is_attributed_to_its_declaration() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let boolean = table.boolean();
        let overloads = OverloadSet::new(vec![
            Signature::new(vec![Parameter::required(number)], number, site(1)),
            Signature::new(vec![Parameter::required(string)], string, site(3)),
        ]);
        let implementation = Signature::new(vec![Parameter::required(boolean)], boolean, site(5));
        let diagnostics = check_implementation(&mut table, &overloads, Some(&implementation));
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].range(), range(1, 2));
        assert_eq!(diagnostics[1].range(), range(3, 4));
    }

    #[test]
    fn overloads_without_implementation_are_rejected() {
        let mut table = TypeTable::new();
        let number = table.number();
        let overloads = OverloadSet::new(vec![Signature::new(
            vec![Parameter::required(number)],
            number,
            site(1),
        )]);
        let diagnostics = check_implementation(&mut table, &overloads, None);
        assert_eq!(
            diagnostics[0].code().as_str(),
            OVERLOAD_MISSING_IMPLEMENTATION.as_str()
        );
    }

    #[test]
    fn generic_implementation_is_compared_after_type_parameter_erasure() {
        let mut table = TypeTable::new();
        let overload_symbol = SymbolId::new(80);
        let implementation_symbol = SymbolId::new(81);
        let overload_type = table.named(overload_symbol);
        let implementation_type = table.named(implementation_symbol);
        let overloads = OverloadSet::new(vec![
            Signature::new(
                vec![Parameter::required(overload_type)],
                overload_type,
                site(1),
            )
            .with_type_parameters(vec![type_parameter(overload_symbol, None, None)]),
        ]);
        let implementation = Signature::new(
            vec![Parameter::required(implementation_type)],
            implementation_type,
            site(5),
        )
        .with_type_parameters(vec![type_parameter(implementation_symbol, None, None)]);
        assert!(check_implementation(&mut table, &overloads, Some(&implementation)).is_empty());
    }

    #[test]
    fn incompatible_generic_constraints_reject_the_implementation() {
        let mut table = TypeTable::new();
        let overload_symbol = SymbolId::new(80);
        let implementation_symbol = SymbolId::new(81);
        let overload_type = table.named(overload_symbol);
        let implementation_type = table.named(implementation_symbol);
        let number = table.number();
        let string = table.string();
        let overloads = OverloadSet::new(vec![
            Signature::new(
                vec![Parameter::required(overload_type)],
                overload_type,
                site(1),
            )
            .with_type_parameters(vec![type_parameter(
                overload_symbol,
                Some(number),
                None,
            )]),
        ]);
        let implementation = Signature::new(
            vec![Parameter::required(implementation_type)],
            implementation_type,
            site(5),
        )
        .with_type_parameters(vec![type_parameter(
            implementation_symbol,
            Some(string),
            None,
        )]);
        assert_eq!(
            check_implementation(&mut table, &overloads, Some(&implementation))[0]
                .code()
                .as_str(),
            IMPLEMENTATION_NOT_COMPATIBLE.as_str()
        );
    }

    #[test]
    fn empty_declaration_set_needs_no_implementation() {
        let mut table = TypeTable::new();
        assert!(check_implementation(&mut table, &OverloadSet::new(vec![]), None).is_empty());
    }
}
