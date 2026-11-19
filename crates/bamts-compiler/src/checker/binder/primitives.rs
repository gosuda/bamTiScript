//! Synthesized members for primitive wrappers and arrays.
//!
//! Member access on a primitive receiver resolves through the wrapper
//! type's members (`String.prototype`, `Array.prototype`, …). The tables
//! here model the `lib.*.d.ts` instance surface the same way
//! `bind_intrinsic_date` and `bind_collection_intrinsics` model theirs:
//! each member carries the lib that first declares it, and a member whose
//! lib is not in the active set does not resolve, so a missing member
//! reports the same diagnostic as a missing object member.

use super::{Binder, FunctionParameter, ObjectType, Type, TypeId};
use crate::checker::intrinsic_environment::Lib;
use crate::source::TextRange;

fn req(name: &str, ty: TypeId) -> FunctionParameter {
    FunctionParameter::new(name.to_owned(), ty, false, false)
}

fn opt(name: &str, ty: TypeId) -> FunctionParameter {
    FunctionParameter::new(name.to_owned(), ty, true, false)
}

fn rest(name: &str, ty: TypeId) -> FunctionParameter {
    FunctionParameter::new(name.to_owned(), ty, false, true)
}

impl Binder<'_> {
    pub(super) fn primitive_wrapper_member(
        &mut self,
        object_type: TypeId,
        name: &str,
        range: TextRange,
    ) -> Option<TypeId> {
        let found = match self.types.get(object_type).clone() {
            Type::String | Type::StringLiteral(_) => {
                if name.parse::<usize>().is_ok() {
                    return Some(self.types.string());
                }
                self.string_member(name)
            }
            Type::Number | Type::NumberLiteral(_) => self.number_member(name),
            Type::Boolean | Type::BooleanLiteral(_) => self.boolean_member(name),
            Type::BigInt | Type::BigIntLiteral(_) => self.bigint_member(name),
            Type::Symbol => self.symbol_member(name),
            _ => None,
        };
        match found {
            Some(_) => found,
            None => self.unknown_wrapper_member(range),
        }
    }

    pub(super) fn array_prototype_member(
        &mut self,
        object_type: TypeId,
        name: &str,
        range: TextRange,
    ) -> Option<TypeId> {
        let element = match self.types.get(object_type).clone() {
            Type::Array(element) => element,
            _ => return None,
        };
        match self.array_member(element, name) {
            Some(member) => Some(member),
            None => self.unknown_wrapper_member(range),
        }
    }

    fn unknown_wrapper_member(&mut self, range: TextRange) -> Option<TypeId> {
        if self.is_typescript() {
            self.emit(
                super::PROPERTY_DOES_NOT_EXIST,
                range,
                super::PROPERTY_DOES_NOT_EXIST_MESSAGE,
            );
            Some(self.types.error_type())
        } else {
            Some(self.types.any())
        }
    }

    fn has_lib(&self, lib: Lib) -> bool {
        self.intrinsics.has_lib(lib)
    }

    fn nullary(&mut self, ret: TypeId) -> TypeId {
        self.types
            .function_with_parameters(Vec::new(), Vec::new(), ret)
    }

    fn method_type(&mut self, params: Vec<FunctionParameter>, ret: TypeId) -> TypeId {
        self.types
            .function_with_parameters(Vec::new(), params, ret)
    }

    fn overloaded(&mut self, signatures: Vec<TypeId>) -> TypeId {
        let mut call_signatures = Vec::with_capacity(signatures.len());
        for signature in signatures {
            match self.types.get(signature).clone() {
                Type::Function(signature) => call_signatures.push(signature),
                _ => unreachable!("synthesized overload must be a function"),
            }
        }
        self.types.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures,
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        })
    }

    fn property_key_union(&mut self) -> TypeId {
        let string = self.types.string();
        let number = self.types.number();
        let symbol = self.types.symbol_type();
        self.types.union(&[string, number, symbol])
    }

    fn object_member_fallback(&mut self, name: &str) -> Option<TypeId> {
        let boolean = self.types.boolean();
        let string = self.types.string();
        let object = self.types.object();
        match name {
            "hasOwnProperty" => {
                let key = self.property_key_union();
                Some(self.method_type(vec![req("v", key)], boolean))
            }
            "isPrototypeOf" => Some(self.method_type(vec![req("v", object)], boolean)),
            "propertyIsEnumerable" => {
                let key = self.property_key_union();
                Some(self.method_type(vec![req("v", key)], boolean))
            }
            "toLocaleString" => Some(self.nullary(string)),
            _ => None,
        }
    }

    fn string_member(&mut self, name: &str) -> Option<TypeId> {
        let string = self.types.string();
        let number = self.types.number();
        let boolean = self.types.boolean();
        let any = self.types.any();
        let undefined = self.types.undefined_type();
        let strings = self.types.array(string);
        match name {
            "charAt" => Some(self.method_type(vec![req("pos", number)], string)),
            "charCodeAt" => Some(self.method_type(vec![opt("index", number)], number)),
            "concat" => Some(self.method_type(vec![rest("strings", strings)], string)),
            "indexOf" => Some(self.method_type(
                vec![req("searchString", string), opt("position", number)],
                number,
            )),
            "lastIndexOf" => Some(self.method_type(
                vec![req("searchString", string), opt("position", number)],
                number,
            )),
            "localeCompare" => Some(self.method_type(vec![req("that", string)], number)),
            "match" => {
                let regexp_like = self.regexp_like();
                let regexp = self.types.union(&[string, regexp_like]);
                Some(self.method_type(vec![req("regexp", regexp)], any))
            }
            "replace" => Some(self.string_replace()),
            "search" => {
                let regexp_like = self.regexp_like();
                let regexp = self.types.union(&[string, regexp_like]);
                Some(self.method_type(vec![req("regexp", regexp)], number))
            }
            "slice" => Some(self.method_type(
                vec![opt("start", number), opt("end", number)],
                string,
            )),
            "split" => {
                let regexp_like = self.regexp_like();
                let separator = self.types.union(&[string, regexp_like]);
                Some(self.method_type(
                    vec![req("separator", separator), opt("limit", number)],
                    strings,
                ))
            }
            "substring" => Some(self.method_type(
                vec![req("start", number), opt("end", number)],
                string,
            )),
            "substr" => Some(self.method_type(
                vec![req("from", number), opt("length", number)],
                string,
            )),
            "toLowerCase" | "toLocaleLowerCase" | "toUpperCase" | "toLocaleUpperCase"
            | "trim" | "toString" => Some(self.nullary(string)),
            "valueOf" => Some(self.nullary(string)),
            "normalize" => Some(self.method_type(vec![opt("form", string)], string)),
            "repeat" => Some(self.method_type(vec![req("count", number)], string)),
            "startsWith" | "endsWith" | "includes" => Some(self.method_type(
                vec![req("searchString", string), opt("position", number)],
                boolean,
            )),
            "codePointAt" => {
                let code = self.types.union(&[number, undefined]);
                Some(self.method_type(vec![req("pos", number)], code))
            }
            "padStart" | "padEnd" if self.has_lib(Lib::Es2017String) => Some(self.method_type(
                vec![req("maxLength", number), opt("fillString", string)],
                string,
            )),
            "trimStart" | "trimEnd" | "trimLeft" | "trimRight"
                if self.has_lib(Lib::Es2019String) =>
            {
                Some(self.nullary(string))
            }
            "matchAll" if self.has_lib(Lib::Es2020String) => {
                let regexp = self.regexp_like();
                let iterator = self.collection_iterator(any);
                Some(self.method_type(vec![req("regexp", regexp)], iterator))
            }
            "at" if self.has_lib(Lib::Es2022At) => {
                let found = self.types.union(&[string, undefined]);
                Some(self.method_type(vec![req("index", number)], found))
            }
            "anchor" => Some(self.method_type(vec![req("name", string)], string)),
            "big" | "blink" | "bold" | "fixed" | "italics" | "small" | "strike" | "sub"
            | "sup" => Some(self.nullary(string)),
            "fontcolor" | "link" => {
                let param = if name == "fontcolor" { "color" } else { "url" };
                Some(self.method_type(vec![req(param, string)], string))
            }
            "fontsize" => Some(self.method_type(vec![req("size", number)], string)),
            "length" => Some(number),
            _ => self.object_member_fallback(name),
        }
    }

    fn regexp_like(&mut self) -> TypeId {
        self.types.any()
    }

    fn string_replace(&mut self) -> TypeId {
        let string = self.types.string();
        let any = self.types.any();
        let regexp_like = self.regexp_like();
        let search = self.types.union(&[string, regexp_like]);
        let replacer = self.types.function_with_parameters(
            Vec::new(),
            vec![req("substring", string), rest("args", any)],
            string,
        );
        let first = self.types.function_with_parameters(
            Vec::new(),
            vec![
                req("searchValue", search),
                req("replaceValue", string),
            ],
            string,
        );
        let second = self.types.function_with_parameters(
            Vec::new(),
            vec![req("searchValue", search), req("replacer", replacer)],
            string,
        );
        self.overloaded(vec![first, second])
    }

    fn number_member(&mut self, name: &str) -> Option<TypeId> {
        let string = self.types.string();
        let number = self.types.number();
        match name {
            "toFixed" => Some(self.method_type(vec![opt("fractionDigits", number)], string)),
            "toExponential" => {
                Some(self.method_type(vec![opt("fractionDigits", number)], string))
            }
            "toPrecision" => Some(self.method_type(vec![opt("precision", number)], string)),
            "toString" => Some(self.method_type(vec![opt("radix", number)], string)),
            "valueOf" => Some(self.nullary(number)),
            "toLocaleString" => {
                let any = self.types.any();
                Some(self.method_type(vec![opt("locales", any), opt("options", any)], string))
            }
            _ => self.object_member_fallback(name),
        }
    }

    fn boolean_member(&mut self, name: &str) -> Option<TypeId> {
        let string = self.types.string();
        let boolean = self.types.boolean();
        match name {
            "toString" => Some(self.nullary(string)),
            "valueOf" => Some(self.nullary(boolean)),
            _ => self.object_member_fallback(name),
        }
    }

    fn symbol_member(&mut self, name: &str) -> Option<TypeId> {
        let string = self.types.string();
        let symbol = self.types.symbol_type();
        let undefined = self.types.undefined_type();
        match name {
            "toString" => Some(self.nullary(string)),
            "valueOf" => Some(self.nullary(symbol)),
            "description" if self.has_lib(Lib::Es2019Symbol) => {
                Some(self.types.union(&[symbol, undefined]))
            }
            _ => self.object_member_fallback(name),
        }
    }

    fn bigint_member(&mut self, name: &str) -> Option<TypeId> {
        let string = self.types.string();
        let bigint = self.types.bigint();
        let number = self.types.number();
        match name {
            "toString" => Some(self.method_type(vec![opt("radix", number)], string)),
            "toLocaleString" => {
                let any = self.types.any();
                Some(self.method_type(vec![opt("locales", any), opt("options", any)], string))
            }
            "valueOf" => Some(self.nullary(bigint)),
            _ => self.object_member_fallback(name),
        }
    }

    fn array_member(&mut self, element: TypeId, name: &str) -> Option<TypeId> {
        let number = self.types.number();
        let string = self.types.string();
        let boolean = self.types.boolean();
        let void = self.types.void();
        let any = self.types.any();
        let undefined = self.types.undefined_type();
        let element_or_undefined = self.types.union(&[element, undefined]);
        match name {
            "length" => Some(number),
            "push" => {
                let items = self.types.array(element);
                Some(self.method_type(vec![rest("items", items)], number))
            }
            "pop" | "shift" => Some(self.nullary(element_or_undefined)),
            "unshift" => {
                let items = self.types.array(element);
                Some(self.method_type(vec![rest("items", items)], number))
            }
            "slice" => {
                let result = self.types.array(element);
                Some(self.method_type(vec![opt("start", number), opt("end", number)], result))
            }
            "splice" => {
                let items = self.types.array(element);
                let result = self.types.array(element);
                Some(self.method_type(
                    vec![
                        req("start", number),
                        opt("deleteCount", number),
                        rest("items", items),
                    ],
                    result,
                ))
            }
            "indexOf" | "lastIndexOf" => Some(self.method_type(
                vec![req("searchElement", element), opt("fromIndex", number)],
                number,
            )),
            "join" => Some(self.method_type(vec![opt("separator", string)], string)),
            "reverse" => {
                let result = self.types.array(element);
                Some(self.nullary(result))
            }
            "sort" => {
                let element_array = self.types.array(element);
                let compare = self.types.function_with_parameters(
                    Vec::new(),
                    vec![req("a", element), req("b", element)],
                    number,
                );
                Some(self.method_type(vec![opt("compareFn", compare)], element_array))
            }
            "every" | "some" => Some(self.array_predicate_method(element, boolean)),
            "forEach" => Some(self.array_predicate_method(element, void)),
            "map" => {
                let u = self.types.method_type_parameter?;
                let u_named = self.types.named(u);
                let callback = self.array_callback(element, u_named);
                let result = self.types.array(u_named);
                let this_arg = opt("thisArg", any);
                Some(self.types.function_with_parameters(
                    vec![u],
                    vec![req("callbackfn", callback), this_arg],
                    result,
                ))
            }
            "filter" => {
                let callback = self.array_unknown_predicate(element);
                let this_arg = opt("thisArg", any);
                let result = self.types.array(element);
                Some(self.method_type(vec![req("callbackfn", callback), this_arg], result))
            }
            "reduce" | "reduceRight" => Some(self.array_reduce(element)?),
            "find" | "findLast" if name == "find" || self.has_lib(Lib::Es2023Array) => {
                let predicate = self.array_unknown_predicate(element);
                let this_arg = opt("thisArg", any);
                Some(self.method_type(
                    vec![req("predicate", predicate), this_arg],
                    element_or_undefined,
                ))
            }
            "findIndex" | "findLastIndex"
                if name == "findIndex" || self.has_lib(Lib::Es2023Array) =>
            {
                let predicate = self.array_unknown_predicate(element);
                let this_arg = opt("thisArg", any);
                Some(self.method_type(vec![req("predicate", predicate), this_arg], number))
            }
            "fill" => {
                let receiver = self.types.array(element);
                Some(self.method_type(
                    vec![req("value", element), opt("start", number), opt("end", number)],
                    receiver,
                ))
            }
            "copyWithin" => {
                let receiver = self.types.array(element);
                Some(self.method_type(
                    vec![req("target", number), req("start", number), opt("end", number)],
                    receiver,
                ))
            }
            "entries" => {
                let pair = self.types.tuple(vec![number, element]);
                let iterator = self.collection_iterator(pair);
                Some(self.nullary(iterator))
            }
            "keys" => {
                let iterator = self.collection_iterator(number);
                Some(self.nullary(iterator))
            }
            "values" => {
                let iterator = self.collection_iterator(element);
                Some(self.nullary(iterator))
            }
            "includes" if self.has_lib(Lib::Es2016Array) => Some(self.method_type(
                vec![req("searchElement", element), opt("fromIndex", number)],
                boolean,
            )),
            "flatMap" if self.has_lib(Lib::Es2019Array) => {
                let u = self.types.method_type_parameter?;
                let u_named = self.types.named(u);
                let u_array = self.types.array(u_named);
                let u_or_array = self.types.union(&[u_named, u_array]);
                let callback = self.array_callback(element, u_or_array);
                let result = self.types.array(u_named);
                let this_arg = opt("thisArg", any);
                Some(self.types.function_with_parameters(
                    vec![u],
                    vec![req("callback", callback), this_arg],
                    result,
                ))
            }
            "flat" if self.has_lib(Lib::Es2019Array) => {
                let result = self.types.array(any);
                Some(self.method_type(vec![opt("depth", number)], result))
            }
            "at" if self.has_lib(Lib::Es2022At) => {
                Some(self.method_type(vec![req("index", number)], element_or_undefined))
            }
            "toReversed" if self.has_lib(Lib::Es2023Array) => {
                let result = self.types.array(element);
                Some(self.nullary(result))
            }
            "toSorted" if self.has_lib(Lib::Es2023Array) => {
                let compare = self.types.function_with_parameters(
                    Vec::new(),
                    vec![req("a", element), req("b", element)],
                    number,
                );
                let result = self.types.array(element);
                Some(self.method_type(vec![opt("compareFn", compare)], result))
            }
            "toSpliced" if self.has_lib(Lib::Es2023Array) => {
                let items = self.types.array(element);
                let result = self.types.array(element);
                Some(self.method_type(
                    vec![
                        req("start", number),
                        opt("deleteCount", number),
                        rest("items", items),
                    ],
                    result,
                ))
            }
            "with" if self.has_lib(Lib::Es2023Array) => {
                let result = self.types.array(element);
                Some(self.method_type(
                    vec![req("index", number), req("value", element)],
                    result,
                ))
            }
            "toString" => Some(self.nullary(string)),
            "toLocaleString" => Some(self.nullary(string)),
            "valueOf" => {
                let object = self.types.object();
                Some(self.nullary(object))
            }
            _ => self.object_member_fallback(name),
        }
    }

    fn array_callback(&mut self, element: TypeId, ret: TypeId) -> TypeId {
        let number = self.types.number();
        let array = self.types.array(element);
        self.types.function_with_parameters(
            Vec::new(),
            vec![
                req("value", element),
                req("index", number),
                req("array", array),
            ],
            ret,
        )
    }

    fn array_unknown_predicate(&mut self, element: TypeId) -> TypeId {
        let unknown = self.types.unknown();
        self.array_callback(element, unknown)
    }

    fn array_predicate_method(&mut self, element: TypeId, ret: TypeId) -> TypeId {
        let any = self.types.any();
        let predicate = self.array_unknown_predicate(element);
        self.method_type(vec![req("predicate", predicate), opt("thisArg", any)], ret)
    }

    fn array_reduce(&mut self, element: TypeId) -> Option<TypeId> {
        let u = self.types.method_type_parameter?;
        let u_type = self.types.named(u);
        let number = self.types.number();
        let array = self.types.array(element);
        let same = self.types.function_with_parameters(
            Vec::new(),
            vec![
                req("previousValue", element),
                req("currentValue", element),
                req("currentIndex", number),
                req("array", array),
            ],
            element,
        );
        let generic = self.types.function_with_parameters(
            Vec::new(),
            vec![
                req("previousValue", u_type),
                req("currentValue", element),
                req("currentIndex", number),
                req("array", array),
            ],
            u_type,
        );
        let first = self.method_type(vec![req("callbackfn", same)], element);
        let second = self.types.function_with_parameters(
            vec![u],
            vec![req("callbackfn", generic), req("initialValue", u_type)],
            u_type,
        );
        Some(self.overloaded(vec![first, second]))
    }
}
