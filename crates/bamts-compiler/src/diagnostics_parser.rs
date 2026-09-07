//! Parse-diagnostic parity: BAMTS-P/L codes mapped onto TypeScript `TS1xxx`
//! codes with the original UTF-16 spans preserved.
//!
//! The parser and scanner keep their native `BAMTS-*` identifiers so recovery
//! and tests stay stable. Downstream oracles and the driver call
//! [`map_parse_diagnostic`] to project those records onto the TypeScript 7
//! parse-code surface without changing ranges, severity, or source identity.

use std::borrow::Cow;

use crate::diagnostic::{Diagnostic, DiagnosticCode};

/// Unterminated string literal.
const TS1002: DiagnosticCode = DiagnosticCode::new("TS1002");
/// Identifier expected.
const TS1003: DiagnosticCode = DiagnosticCode::new("TS1003");
/// Token expected.
const TS1005: DiagnosticCode = DiagnosticCode::new("TS1005");
/// Trailing comma not allowed.
const TS1009: DiagnosticCode = DiagnosticCode::new("TS1009");
/// `*/` expected.
const TS1010: DiagnosticCode = DiagnosticCode::new("TS1010");
/// Unexpected token.
const TS1012: DiagnosticCode = DiagnosticCode::new("TS1012");
/// A rest parameter must be last in a parameter list.
const TS1014: DiagnosticCode = DiagnosticCode::new("TS1014");
/// Parameter cannot have question mark and initializer.
const TS1015: DiagnosticCode = DiagnosticCode::new("TS1015");
/// A required parameter cannot follow an optional parameter.
const TS1016: DiagnosticCode = DiagnosticCode::new("TS1016");
/// An index signature must have a type annotation.
const TS1021: DiagnosticCode = DiagnosticCode::new("TS1021");
/// A modifier cannot appear on this class element.
const TS1031: DiagnosticCode = DiagnosticCode::new("TS1031");
/// A declaration that requires initialization was not initialized.
const TS1155: DiagnosticCode = DiagnosticCode::new("TS1155");
/// Decorators are not valid in this position.
const TS1206: DiagnosticCode = DiagnosticCode::new("TS1206");
/// JSX attributes require a non-empty expression.
const TS17000: DiagnosticCode = DiagnosticCode::new("TS17000");
/// Unary expressions require parentheses before exponentiation.
const TS17006: DiagnosticCode = DiagnosticCode::new("TS17006");
/// Expression expected.
const TS1109: DiagnosticCode = DiagnosticCode::new("TS1109");
/// Type expected.
const TS1110: DiagnosticCode = DiagnosticCode::new("TS1110");
/// Digit expected.
const TS1124: DiagnosticCode = DiagnosticCode::new("TS1124");
/// Hexadecimal digit expected.
const TS1125: DiagnosticCode = DiagnosticCode::new("TS1125");
/// Invalid character.
const TS1127: DiagnosticCode = DiagnosticCode::new("TS1127");
/// Declaration or statement expected.
const TS1128: DiagnosticCode = DiagnosticCode::new("TS1128");
/// Property assignment expected.
const TS1136: DiagnosticCode = DiagnosticCode::new("TS1136");
/// Unterminated template literal.
const TS1160: DiagnosticCode = DiagnosticCode::new("TS1160");
/// Unterminated regular expression literal.
const TS1161: DiagnosticCode = DiagnosticCode::new("TS1161");
const TS1163: DiagnosticCode = DiagnosticCode::new("TS1163");
const TS1308: DiagnosticCode = DiagnosticCode::new("TS1308");
/// Expected corresponding JSX closing tag.
const TS17002: DiagnosticCode = DiagnosticCode::new("TS17002");
/// JSX fragment has no corresponding closing tag.
const TS17014: DiagnosticCode = DiagnosticCode::new("TS17014");
/// Expected corresponding JSX fragment closing tag.
const TS17015: DiagnosticCode = DiagnosticCode::new("TS17015");

/// Maps a native parser/scanner code onto a TypeScript `TS1xxx` parse code.
#[must_use]
pub fn typescript_parse_code(code: DiagnosticCode, message: &str) -> Option<DiagnosticCode> {
    Some(match code.as_str() {
        "BAMTS-L001" => TS1002,
        "BAMTS-L002" => TS1010,
        "BAMTS-L003" => TS1160,
        "BAMTS-L004" => TS1161,
        "BAMTS-L005" => TS1127,
        "BAMTS-L006" | "BAMTS-L007" => TS1125,
        "BAMTS-L008" | "BAMTS-L009" | "BAMTS-L010" => TS1124,
        "BAMTS-L011" => TS1127,
        "BAMTS-P001" => map_expected_token(message),
        "BAMTS-P002" => map_expected_expression(message),
        "BAMTS-P003" => TS1003,
        "BAMTS-P004" => TS1110,
        "BAMTS-P005" => map_unexpected_token(message),
        "BAMTS-P009" => TS1136,
        "BAMTS-P012" => TS1155,
        "BAMTS-P013" => TS17002,
        "BAMTS-P014" => TS1003,
        "BAMTS-P015" => TS17015,
        "BAMTS-P016" => TS17014,
        "BAMTS-P017" => TS1163,
        "BAMTS-P018" => TS1308,
        "BAMTS-C051" if is_export_modifier_on_class_element(message) => TS1031,
        _ => return None,
    })
}

/// Canonical TypeScript message for a mapped parse code.
#[must_use]
pub fn typescript_parse_message(code: DiagnosticCode) -> Option<&'static str> {
    Some(match code.as_str() {
        "TS1002" => "Unterminated string literal.",
        "TS1003" => "Identifier expected.",
        "TS1005" => "'{0}' expected.",
        "TS1009" => "Trailing comma not allowed.",
        "TS1010" => "'*/' expected.",
        "TS1012" => "Unexpected token.",
        "TS1014" => "A rest parameter must be last in a parameter list.",
        "TS1015" => "Parameter cannot have question mark and initializer.",
        "TS1016" => "A required parameter cannot follow an optional parameter.",
        "TS1021" => "An index signature must have a type annotation.",
        "TS1031" => "'{0}' modifier cannot appear on class elements of this kind.",
        "TS1155" => "'{0}' declarations must be initialized.",
        "TS1206" => "Decorators are not valid here.",
        "TS17000" => "JSX attributes must only be assigned a non-empty 'expression'.",
        "TS17006" => {
            "An unary expression with the '{0}' operator is not allowed in the left-hand side of an exponentiation expression. Consider enclosing the expression in parentheses."
        }
        "TS1109" => "Expression expected.",
        "TS1110" => "Type expected.",
        "TS1124" => "Digit expected.",
        "TS1125" => "Hexadecimal digit expected.",
        "TS1127" => "Invalid character.",
        "TS1128" => "Declaration or statement expected.",
        "TS1136" => "Property assignment expected.",
        "TS1160" => "Unterminated template literal.",
        "TS1161" => "Unterminated regular expression literal.",
        "TS1163" => "A 'yield' expression is only allowed in a generator body.",
        "TS1308" => {
            "'await' expressions are only allowed within async functions and at the top levels of modules."
        }
        "TS17002" => "Expected corresponding JSX closing tag for '{0}'.",
        "TS17008" => "JSX element '{0}' has no corresponding closing tag.",
        "TS17014" => "JSX fragment has no corresponding closing tag.",
        "TS17015" => "Expected corresponding closing tag for JSX fragment.",
        _ => return None,
    })
}

/// Projects one native parse/scan diagnostic onto the TypeScript parse surface.
///
/// The UTF-16 span, source id, and severity are preserved. Unmapped codes are
/// returned unchanged so callers can map a mixed diagnostic list in one pass.
#[must_use]
pub fn map_parse_diagnostic(diagnostic: &Diagnostic) -> Diagnostic {
    let Some(ts_code) = typescript_parse_code(diagnostic.code(), diagnostic.message()) else {
        return diagnostic.clone();
    };
    let message: Cow<'static, str> = typescript_parse_message(ts_code)
        .map(Cow::Borrowed)
        .unwrap_or_else(|| diagnostic.message_cow());
    let mapped = Diagnostic::new(
        diagnostic.severity(),
        ts_code,
        diagnostic.source_id(),
        diagnostic.range(),
        message,
    )
    .with_note(format!(
        "{}: {}",
        diagnostic.code().as_str(),
        diagnostic.message()
    ));
    let mapped = diagnostic
        .secondary_spans()
        .iter()
        .fold(mapped, |acc, span| acc.with_secondary_span(span.clone()));
    let mapped = match diagnostic.help() {
        Some(help) => mapped.with_help(help.to_owned()),
        None => mapped,
    };
    match diagnostic.suggestion() {
        Some(suggestion) => mapped.with_suggestion(suggestion.clone()),
        None => mapped,
    }
}

/// Maps every diagnostic, preserving order after [`Diagnostic`] canonical sort.
#[must_use]
pub fn map_parse_diagnostics(diagnostics: &[Diagnostic]) -> Vec<Diagnostic> {
    let mapped: Vec<Diagnostic> = diagnostics.iter().map(map_parse_diagnostic).collect();
    crate::diagnostic::Recovered::new((), mapped).into_parts().1
}

fn is_export_modifier_on_class_element(message: &str) -> bool {
    let lower = message.to_ascii_lowercase();
    lower.contains("export modifier") && lower.contains("class element")
}

fn map_expected_token(message: &str) -> DiagnosticCode {
    let lower = message.to_ascii_lowercase();
    if lower.contains("trailing comma") {
        TS1009
    } else if lower.contains("rest parameter") {
        TS1014
    } else if lower.contains("question mark") && lower.contains("initializer") {
        TS1015
    } else if lower.contains("required parameter") && lower.contains("optional") {
        TS1016
    } else if lower.contains("index signature requires a type") {
        TS1021
    } else if lower.contains("decorators must precede a class") {
        TS1206
    } else if lower.contains("jsx closing tag does not match") {
        TS17002
    } else if lower.contains("declaration or statement") {
        TS1128
    } else {
        TS1005
    }
}

fn map_expected_expression(message: &str) -> DiagnosticCode {
    if message.to_ascii_lowercase().contains("jsx attribute value") {
        TS17000
    } else {
        TS1109
    }
}

fn map_unexpected_token(message: &str) -> DiagnosticCode {
    let lower = message.to_ascii_lowercase();
    if lower.contains("declaration or statement") {
        TS1128
    } else if lower.contains("unparenthesized unary expression") && lower.contains("left operand") {
        TS17006
    } else {
        TS1012
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::{DiagnosticSeverity, Recovered};
    use crate::source::{SourceId, TextRange, Utf16Pos};

    fn range(start: usize, end: usize) -> TextRange {
        TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered test range")
    }

    fn native(code: &'static str, start: usize, end: usize, message: &'static str) -> Diagnostic {
        Diagnostic::error(
            DiagnosticCode::new(code),
            SourceId::new(7),
            range(start, end),
            message,
        )
    }

    #[test]
    fn maps_parser_and_scanner_codes_onto_ts1xxx_preserving_spans() {
        let cases = [
            ("BAMTS-L001", 2, 8, "unterminated string literal", "TS1002"),
            ("BAMTS-P003", 4, 5, "expected an identifier", "TS1003"),
            ("BAMTS-P001", 1, 2, "expected `;`", "TS1005"),
            (
                "BAMTS-P001",
                3,
                4,
                "trailing comma is not allowed",
                "TS1009",
            ),
            ("BAMTS-L002", 0, 2, "unterminated block comment", "TS1010"),
            ("BAMTS-P005", 6, 7, "this token was skipped", "TS1012"),
            (
                "BAMTS-P001",
                8,
                9,
                "a rest parameter must be last",
                "TS1014",
            ),
            (
                "BAMTS-P001",
                8,
                9,
                "parameter cannot have a question mark and initializer",
                "TS1015",
            ),
            (
                "BAMTS-P001",
                8,
                9,
                "a required parameter cannot follow an optional parameter",
                "TS1016",
            ),
            (
                "BAMTS-L009",
                0,
                2,
                "an exponent must have at least one digit",
                "TS1124",
            ),
            ("BAMTS-L007", 1, 4, "invalid unicode escape", "TS1125"),
            ("BAMTS-L005", 0, 1, "unexpected character", "TS1127"),
            (
                "BAMTS-P005",
                0,
                1,
                "declaration or statement expected",
                "TS1128",
            ),
            (
                "BAMTS-L003",
                0,
                3,
                "unterminated template literal",
                "TS1160",
            ),
            (
                "BAMTS-L004",
                0,
                5,
                "unterminated regular expression literal",
                "TS1161",
            ),
            ("BAMTS-P002", 1, 2, "expected an expression", "TS1109"),
            ("BAMTS-P004", 1, 2, "expected a type", "TS1110"),
            ("BAMTS-P009", 2, 3, "expected a property name", "TS1136"),
            ("BAMTS-L006", 0, 2, "invalid escape sequence", "TS1125"),
            (
                "BAMTS-L008",
                0,
                3,
                "numeric separator is misplaced",
                "TS1124",
            ),
            ("BAMTS-L010", 0, 3, "invalid bigint literal", "TS1124"),
            ("BAMTS-L011", 0, 1, "invalid private identifier", "TS1127"),
            (
                "BAMTS-P001",
                0,
                1,
                "declaration or statement expected",
                "TS1128",
            ),
            (
                "BAMTS-P001",
                9,
                10,
                "an index signature requires a type",
                "TS1021",
            ),
            (
                "BAMTS-C051",
                10,
                16,
                "export modifier cannot appear on a class element",
                "TS1031",
            ),
            (
                "BAMTS-P012",
                4,
                9,
                "using declarations must be initialized",
                "TS1155",
            ),
            (
                "BAMTS-P001",
                0,
                1,
                "decorators must precede a class",
                "TS1206",
            ),
            (
                "BAMTS-P002",
                8,
                9,
                "expected a JSX attribute value",
                "TS17000",
            ),
            (
                "BAMTS-P005",
                1,
                3,
                "an unparenthesized unary expression cannot be the left operand",
                "TS17006",
            ),
        ];
        for (native_code, start, end, message, ts_code) in cases {
            let original = native(native_code, start, end, message);
            let mapped = map_parse_diagnostic(&original);
            assert_eq!(
                mapped.code().as_str(),
                ts_code,
                "{native_code} -> {ts_code}"
            );
            assert_eq!(mapped.range(), original.range());
            assert_eq!(mapped.source_id(), original.source_id());
            assert_eq!(mapped.severity(), DiagnosticSeverity::Error);
            assert_eq!(
                mapped.note().map(str::to_owned),
                Some(format!("{native_code}: {message}"))
            );
        }
    }

    #[test]
    fn unmapped_codes_keep_identity() {
        let original = native("BAMTS-P010", 0, 1, "nesting too deep");
        let mapped = map_parse_diagnostic(&original);
        assert_eq!(mapped.code().as_str(), "BAMTS-P010");
        assert_eq!(mapped.range(), original.range());
        assert_eq!(mapped.message(), original.message());
    }

    #[test]
    fn colliding_checker_code_is_not_projected_as_a_parse_diagnostic() {
        let checker = native("BAMTS-C051", 4, 8, "Expected 2 arguments, but got 1.");
        let parser = native(
            "BAMTS-C051",
            9,
            15,
            "export modifier cannot appear on a class element",
        );
        let mapped = map_parse_diagnostics(&[checker.clone(), parser]);
        let preserved = mapped
            .iter()
            .find(|diagnostic| diagnostic.code().as_str() == "BAMTS-C051")
            .expect("checker diagnostic remains native");
        assert_eq!(preserved.message(), checker.message());
        assert_eq!(preserved.range(), checker.range());
        assert!(mapped.iter().any(|diagnostic| diagnostic.code() == TS1031));
    }

    #[test]
    fn mapped_list_is_canonically_ordered() {
        let mapped = map_parse_diagnostics(&[
            native("BAMTS-P003", 4, 5, "expected an identifier"),
            native("BAMTS-L001", 1, 3, "unterminated string literal"),
        ]);
        assert_eq!(mapped[0].code().as_str(), "TS1002");
        assert_eq!(mapped[1].code().as_str(), "TS1003");
        let (_, sorted) = Recovered::new((), mapped.clone()).into_parts();
        assert_eq!(mapped, sorted);
    }
}
