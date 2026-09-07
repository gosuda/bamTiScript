use super::{
    Binder, ConstructEntry, FunctionParameter, FunctionSignature, ObjectType, PropertyType,
    SymbolId, TypeId,
};
use crate::checker::intrinsic_environment::Lib;

impl Binder<'_> {
    pub(super) fn bind_intrinsic_date(&mut self, type_symbol: SymbolId, value_symbol: SymbolId) {
        let number = self.types.number();
        let string = self.types.string();
        self.types.declare_class(type_symbol, Vec::new());
        let instance = self.types.applied_class(type_symbol, Vec::new());
        let mut properties = Vec::new();
        for name in [
            "toString",
            "toDateString",
            "toTimeString",
            "toUTCString",
            "toISOString",
        ] {
            let method = self.types.function(Vec::new(), string);
            properties.push(PropertyType::new(name, false, method).with_method(true));
        }
        for name in [
            "valueOf",
            "getTime",
            "getFullYear",
            "getUTCFullYear",
            "getMonth",
            "getUTCMonth",
            "getDate",
            "getUTCDate",
            "getDay",
            "getUTCDay",
            "getHours",
            "getUTCHours",
            "getMinutes",
            "getUTCMinutes",
            "getSeconds",
            "getUTCSeconds",
            "getMilliseconds",
            "getUTCMilliseconds",
            "getTimezoneOffset",
        ] {
            let method = self.types.function(Vec::new(), number);
            properties.push(PropertyType::new(name, false, method).with_method(true));
        }
        for (name, names) in [
            ("setTime", &["time"][..]),
            ("setMilliseconds", &["ms"]),
            ("setUTCMilliseconds", &["ms"]),
            ("setSeconds", &["sec", "ms"]),
            ("setUTCSeconds", &["sec", "ms"]),
            ("setMinutes", &["min", "sec", "ms"]),
            ("setUTCMinutes", &["min", "sec", "ms"]),
            ("setHours", &["hours", "min", "sec", "ms"]),
            ("setUTCHours", &["hours", "min", "sec", "ms"]),
            ("setDate", &["date"]),
            ("setUTCDate", &["date"]),
            ("setMonth", &["month", "date"]),
            ("setUTCMonth", &["month", "date"]),
            ("setFullYear", &["year", "month", "date"]),
            ("setUTCFullYear", &["year", "month", "date"]),
        ] {
            let parameters = names
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    FunctionParameter::new((*name).to_owned(), number, index != 0, false)
                })
                .collect();
            let method = self
                .types
                .function_with_parameters(Vec::new(), parameters, number);
            properties.push(PropertyType::new(name, false, method).with_method(true));
        }
        let json = self.types.function_with_parameters(
            Vec::new(),
            vec![FunctionParameter::new(
                "key".to_owned(),
                self.types.any(),
                true,
                false,
            )],
            string,
        );
        properties.push(PropertyType::new("toJSON", false, json).with_method(true));

        // The ES5 Intl merge supplies these overloads even without a later Intl lib.
        let string_array = self.types.array(string);
        let locales = self.types.union(&[string, string_array]);
        let mut format_properties = Vec::new();
        for (name, values) in [
            ("localeMatcher", &["best fit", "lookup"][..]),
            ("weekday", &["long", "short", "narrow"]),
            ("era", &["long", "short", "narrow"]),
            ("year", &["numeric", "2-digit"]),
            ("month", &["numeric", "2-digit", "long", "short", "narrow"]),
            ("day", &["numeric", "2-digit"]),
            ("hour", &["numeric", "2-digit"]),
            ("minute", &["numeric", "2-digit"]),
            ("second", &["numeric", "2-digit"]),
            (
                "timeZoneName",
                &[
                    "short",
                    "long",
                    "shortOffset",
                    "longOffset",
                    "shortGeneric",
                    "longGeneric",
                ],
            ),
            ("formatMatcher", &["best fit", "basic"]),
        ] {
            let mut members: Vec<_> = values
                .iter()
                .map(|value| self.types.string_literal(value))
                .collect();
            members.push(self.types.undefined_type());
            let value = self.types.union(&members);
            format_properties.push(PropertyType::new(name, true, value));
        }
        let hour12 = self
            .types
            .union(&[self.types.boolean(), self.types.undefined_type()]);
        let time_zone = self.types.union(&[string, self.types.undefined_type()]);
        format_properties.extend([
            PropertyType::new("hour12", true, hour12),
            PropertyType::new("timeZone", true, time_zone),
        ]);
        let format_options = self.types.object_type(format_properties);
        // `interface Date` in lib.es5.d.ts declares the no-argument
        // `toLocale*` trio, and the Intl-tagged `interface Date` merge in the
        // same file adds the `(locales?, options?)` overloads. Both arities
        // are pushed so `object_type_with_members` merges each name into one
        // two-signature overload group in declaration order.
        //
        // Later refinements stay unmodelled rather than substituted:
        // `lib.es2020.date.d.ts` widens `locales` to `Intl.LocalesArgument`
        // and `lib.esnext.date.d.ts` adds `toTemporalInstant():
        // Temporal.Instant`; neither `Intl.Locale`/`Intl.LocalesArgument` nor
        // `Temporal.Instant` has a registered identity in the intrinsic
        // environment, so no honest type can be named for them yet.
        for name in ["toLocaleString", "toLocaleDateString", "toLocaleTimeString"] {
            let base = self.types.function(Vec::new(), string);
            properties.push(PropertyType::new(name, false, base).with_method(true));
            let method = self.types.function_with_parameters(
                Vec::new(),
                vec![
                    FunctionParameter::new("locales".to_owned(), locales, true, false),
                    FunctionParameter::new("options".to_owned(), format_options, true, false),
                ],
                string,
            );
            properties.push(PropertyType::new(name, false, method).with_method(true));
        }
        let raw = self.types.object_type(properties);
        self.types.publish_final_class_template(type_symbol, raw);
        self.class_instance_types.insert(type_symbol, instance);
        self.class_instance_types.insert(value_symbol, instance);

        let value = if self.intrinsics.has_lib(Lib::Es2015) {
            self.types.union(&[number, string, instance])
        } else {
            self.types.union(&[number, string])
        };
        let components = [
            "year",
            "monthIndex",
            "date",
            "hours",
            "minutes",
            "seconds",
            "ms",
        ];
        let construct_signatures = vec![
            ConstructEntry {
                signature: date_signature(Vec::new(), instance),
                is_abstract: false,
            },
            ConstructEntry {
                signature: date_signature(
                    vec![FunctionParameter::new(
                        "value".to_owned(),
                        value,
                        false,
                        false,
                    )],
                    instance,
                ),
                is_abstract: false,
            },
            ConstructEntry {
                signature: date_signature(
                    components
                        .iter()
                        .enumerate()
                        .map(|(index, name)| {
                            FunctionParameter::new((*name).to_owned(), number, index >= 2, false)
                        })
                        .collect(),
                    instance,
                ),
                is_abstract: false,
            },
        ];
        let parse = self.types.function_with_parameters(
            Vec::new(),
            vec![FunctionParameter::new("s".to_owned(), string, false, false)],
            number,
        );
        let now = self.types.function(Vec::new(), number);
        let utc = self.types.function_with_parameters(
            Vec::new(),
            components
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    FunctionParameter::new((*name).to_owned(), number, index >= 2, false)
                })
                .collect(),
            number,
        );
        let constructor = self.types.object_type_with_members(ObjectType {
            properties: vec![
                PropertyType::new("prototype", false, instance).with_readonly(true),
                PropertyType::new("parse", false, parse).with_method(true),
                PropertyType::new("now", false, now).with_method(true),
                PropertyType::new("UTC", false, utc).with_method(true),
            ],
            call_signatures: vec![date_signature(Vec::new(), string)],
            call_candidate_order: Vec::new(),
            construct_signatures,
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        });

        self.symbol_types[value_symbol.get() as usize] = constructor;
    }
}

fn date_signature(parameters: Vec<FunctionParameter>, return_type: TypeId) -> FunctionSignature {
    FunctionSignature {
        type_parameters: Vec::new(),
        type_parameter_bounds: Vec::new(),
        parameters,
        return_type,
        declared_return: None,
        declaring_types: Vec::new(),
        javascript: false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::checker::ProgramCheckOptions;
    use crate::checker::intrinsic_environment::{GlobalEnvironment, LibSet};
    use crate::diagnostic::Diagnostic;
    use crate::source::{ScriptKind, SourceId, SourceText};

    use super::super::{SemanticModel, SymbolId, Type, bind_source, bind_source_with_environment};

    fn source(text: &str) -> Arc<SourceText> {
        Arc::new(SourceText::new(text).expect("test source fits the per-file budget"))
    }

    fn bound(text: &str) -> (SemanticModel, Vec<Diagnostic>) {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        bind_source(parsed.product())
    }

    fn bound_with_libs(text: &str, libs: LibSet) -> (SemanticModel, Vec<Diagnostic>) {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        bind_source_with_environment(
            parsed.product(),
            GlobalEnvironment::standard(libs),
            false,
            ProgramCheckOptions::standard(),
        )
    }

    fn value_symbol(model: &SemanticModel, name: &str) -> SymbolId {
        model
            .scopes()
            .iter()
            .find_map(|scope| scope.value(name))
            .unwrap_or_else(|| panic!("value `{name}` not bound"))
    }

    fn type_symbol(model: &SemanticModel, name: &str) -> SymbolId {
        model
            .scopes()
            .iter()
            .find_map(|scope| scope.type_binding(name))
            .unwrap_or_else(|| panic!("type `{name}` not bound"))
    }

    fn assert_date_instance(model: &SemanticModel, type_id: super::super::TypeId) {
        let date_symbol = type_symbol(model, "Date");
        match model.types().get(type_id) {
            Type::AppliedClass { symbol, arguments } => {
                assert_eq!(*symbol, date_symbol);
                assert!(arguments.is_empty());
            }
            actual => panic!("expected Date instance, got {actual:?}"),
        }
    }

    #[test]
    fn date_type_annotation_resolves_to_applied_class() {
        let (model, diagnostics) = bound("declare const d: Date;");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        let d = value_symbol(&model, "d");
        assert_date_instance(&model, model.symbol_type(d));
    }

    #[test]
    fn new_date_returns_instance_and_date_call_returns_string() {
        let (model, diagnostics) = bound("const d = new Date(); const s = Date();");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        assert_date_instance(&model, model.symbol_type(value_symbol(&model, "d")));
        assert_eq!(
            model.symbol_type(value_symbol(&model, "s")),
            model.types().string()
        );
    }

    #[test]
    fn date_statics_return_numbers_and_instance_methods_are_typed() {
        let (model, diagnostics) = bound(
            "declare const d: Date;\
             const now = Date.now();\
             const parsed = Date.parse(\"2026-01-01\");\
             const utc = Date.UTC(2026, 0);\
             const time = d.getTime();\
             const iso = d.toISOString();",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        for name in ["now", "parsed", "utc", "time"] {
            assert_eq!(
                model.symbol_type(value_symbol(&model, name)),
                model.types().number(),
                "{name} should be number",
            );
        }
        assert_eq!(
            model.symbol_type(value_symbol(&model, "iso")),
            model.types().string()
        );
    }

    #[test]
    fn date_constructor_has_callable_construct_and_static_surface() {
        let (model, diagnostics) = bound("declare const d: Date;");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        let date_type = type_symbol(&model, "Date");
        let date_value = value_symbol(&model, "Date");
        let constructor_type = model.symbol_type(date_value);
        let Type::ObjectType(constructor) = model.types().get(constructor_type) else {
            panic!("Date value must expose an object constructor type");
        };

        assert_eq!(constructor.call_signatures.len(), 1);
        assert_eq!(
            constructor.call_signatures[0].return_type(),
            model.types().string()
        );
        assert_eq!(constructor.construct_signatures.len(), 3);
        for entry in &constructor.construct_signatures {
            match model.types().get(entry.signature.return_type()) {
                Type::AppliedClass { symbol, arguments } => {
                    assert_eq!(*symbol, date_type);
                    assert!(arguments.is_empty());
                }
                actual => panic!("constructor must return Date, got {actual:?}"),
            }
        }

        for name in ["parse", "UTC", "now", "prototype"] {
            assert!(
                constructor
                    .properties()
                    .iter()
                    .any(|property| property.name() == name),
                "missing Date constructor property `{name}`",
            );
        }
        let prototype = constructor
            .properties()
            .iter()
            .find(|property| property.name() == "prototype")
            .expect("Date.prototype property");
        assert!(prototype.readonly());
    }

    #[test]
    fn date_es2015_value_constructor_widening_is_lib_gated() {
        let (es5_model, es5_diagnostics) =
            bound_with_libs("declare const d: Date;", LibSet::from_lib_names(&["es5"]));
        assert!(es5_diagnostics.is_empty(), "{es5_diagnostics:?}");
        let es5_constructor = es5_model.symbol_type(value_symbol(&es5_model, "Date"));
        let Type::ObjectType(es5_constructor) = es5_model.types().get(es5_constructor) else {
            panic!("Date value must expose an object constructor type");
        };
        let es5_value_parameter = es5_constructor.construct_signatures[1]
            .signature
            .parameters()[0]
            .type_id();
        let Type::Union(es5_members) = es5_model.types().get(es5_value_parameter) else {
            panic!("Date(value) must expose a union parameter");
        };
        assert_eq!(es5_members.len(), 2);

        let (es2015_model, es2015_diagnostics) = bound_with_libs(
            "declare const d: Date;",
            LibSet::from_lib_names(&["es2015"]),
        );
        assert!(es2015_diagnostics.is_empty(), "{es2015_diagnostics:?}");
        let es2015_constructor = es2015_model.symbol_type(value_symbol(&es2015_model, "Date"));
        let Type::ObjectType(es2015_constructor) = es2015_model.types().get(es2015_constructor)
        else {
            panic!("Date value must expose an object constructor type");
        };
        let es2015_value_parameter = es2015_constructor.construct_signatures[1]
            .signature
            .parameters()[0]
            .type_id();
        let Type::Union(es2015_members) = es2015_model.types().get(es2015_value_parameter) else {
            panic!("Date(value) must expose a union parameter");
        };
        assert_eq!(es2015_members.len(), 3);
    }

    #[test]
    fn date_to_locale_methods_merge_base_and_intl_overloads() {
        let (model, diagnostics) = bound("declare const d: Date; const text = d.toLocaleString();");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        let date_type = type_symbol(&model, "Date");
        let locale = model
            .types()
            .class_template_properties(date_type)
            .iter()
            .find(|property| property.name() == "toLocaleString")
            .expect("Date.toLocaleString property");
        let Type::ObjectType(overloads) = model.types().get(locale.type_id()) else {
            panic!("Date.toLocaleString must preserve both overloads");
        };
        assert_eq!(overloads.call_signatures.len(), 2);
        assert!(overloads.call_signatures[0].parameters().is_empty());
        assert_eq!(overloads.call_signatures[1].parameters().len(), 2);
        assert!(overloads.call_signatures[1].parameters()[0].optional());
        assert!(overloads.call_signatures[1].parameters()[1].optional());
    }
}
