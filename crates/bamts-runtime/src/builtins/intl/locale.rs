//! `Intl.Locale`.

use bamts_native::Value;

use super::super::allocate_array;
use super::options::{Options, boolean_option, coerce_options_to_object, string_option};
use super::{
    Class, arg, boolean_outcome, construct, create, define_field, install_class, intl_record,
    is_object, is_type_sequence, locale_record, new_object, optional_string_outcome, range_error,
    require_new, string_array_outcome, string_outcome, string_value, type_error,
};
use crate::intl::locale_data::{self, DATA};
use crate::intl::locale_negotiation::{
    LanguageId, LanguageTag, UnicodeExtension, canonicalize_unicode_locale_id,
};
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    install_class(
        heap,
        atoms,
        builtins,
        namespace,
        &Class {
            kind: IntlKind::Locale,
            name: "Locale",
            tag: "Intl.Locale",
            length: 1,
            constructor: constructor::<H>,
            statics: &[],
            getters: &[
                ("baseName", "get baseName", base_name::<H>),
                ("calendar", "get calendar", calendar::<H>),
                ("caseFirst", "get caseFirst", case_first::<H>),
                ("collation", "get collation", collation::<H>),
                (
                    "firstDayOfWeek",
                    "get firstDayOfWeek",
                    first_day_of_week::<H>,
                ),
                ("hourCycle", "get hourCycle", hour_cycle::<H>),
                ("language", "get language", language::<H>),
                (
                    "numberingSystem",
                    "get numberingSystem",
                    numbering_system::<H>,
                ),
                ("numeric", "get numeric", numeric::<H>),
                ("region", "get region", region::<H>),
                ("script", "get script", script::<H>),
                ("variants", "get variants", variants::<H>),
            ],
            methods: &[
                ("getCalendars", 0, get_calendars::<H>),
                ("getCollations", 0, get_collations::<H>),
                ("getHourCycles", 0, get_hour_cycles::<H>),
                ("getNumberingSystems", 0, get_numbering_systems::<H>),
                ("getTextInfo", 0, get_text_info::<H>),
                ("getTimeZones", 0, get_time_zones::<H>),
                ("getWeekInfo", 0, get_week_info::<H>),
                ("maximize", 0, maximize::<H>),
                ("minimize", 0, minimize::<H>),
                ("toString", 0, to_string::<H>),
            ],
        },
    );
}

fn this_locale<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<LanguageTag, EvalFailure> {
    match intl_record(machine, this)? {
        Some(IntlObject::Locale(tag)) => Ok(tag.clone()),
        _ => Err(type_error(machine, "receiver is not an Intl.Locale")),
    }
}

/// GetOption for a keyword whose value must match the `type` production.
fn type_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<Option<String>, EvalFailure> {
    let value = string_option(machine, options, name, &[])?;
    checked_type(machine, name, value)
}

fn checked_type<H: Host>(
    machine: &mut Machine<'_, H>,
    name: &str,
    value: Option<String>,
) -> Result<Option<String>, EvalFailure> {
    match value {
        Some(value) if !is_type_sequence(&value) => Err(range_error(
            machine,
            format!("{value} is not a valid value for {name}"),
        )),
        value => Ok(value),
    }
}

/// `WeekdayToString`: a number names a day, Sunday being both 0 and 7.
fn weekday_keyword(value: &str) -> &str {
    match value {
        "0" | "7" => "sun",
        "1" => "mon",
        "2" => "tue",
        "3" => "wed",
        "4" => "thu",
        "5" => "fri",
        "6" => "sat",
        other => other,
    }
}

/// UpdateLanguageId: the language options, validated as they are read.
fn update_language_id<H: Host>(
    machine: &mut Machine<'_, H>,
    tag: &LanguageTag,
    options: Options,
) -> Result<LanguageId, EvalFailure> {
    let mut id = tag.id.clone();
    if let Some(language) = string_option(machine, options, "language", &[])? {
        if !LanguageTag::is_language_subtag(&language) {
            return Err(range_error(machine, format!("invalid language {language}")));
        }
        id.language = language;
    }
    if let Some(script) = string_option(machine, options, "script", &[])? {
        if !LanguageTag::is_script_subtag(&script) {
            return Err(range_error(machine, format!("invalid script {script}")));
        }
        id.script = Some(script);
    }
    if let Some(region) = string_option(machine, options, "region", &[])? {
        if !LanguageTag::is_region_subtag(&region) {
            return Err(range_error(machine, format!("invalid region {region}")));
        }
        id.region = Some(region);
    }
    if let Some(variants) = string_option(machine, options, "variants", &[])? {
        let lower = variants.to_ascii_lowercase();
        let subtags: Vec<String> = lower.split('-').map(str::to_owned).collect();
        let duplicate = subtags
            .iter()
            .enumerate()
            .any(|(index, subtag)| subtags[..index].contains(subtag));
        if duplicate
            || !subtags
                .iter()
                .all(|subtag| LanguageTag::is_variant_subtag(subtag))
        {
            return Err(range_error(machine, format!("invalid variants {variants}")));
        }
        id.variants = subtags;
    }
    Ok(id)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "Locale")?;
    let tag = arg(args, 0);
    if machine.string_value(tag).is_none() && !is_object(machine, tag)? {
        return Err(type_error(
            machine,
            "a locale must be a string or an object",
        ));
    }
    let text = match locale_record(machine, tag)? {
        Some(tag) => tag.to_string(),
        None => machine.coerce_string_observable(tag)?.to_utf8_lossy(),
    };
    let options = coerce_options_to_object(machine, arg(args, 1))?;
    let canonical = canonicalize_unicode_locale_id(&text, &*DATA)
        .map_err(|error| range_error(machine, error.to_string()))?;
    let mut tag = parse(machine, &canonical)?;
    tag.id = update_language_id(machine, &tag, options)?;

    let calendar = type_option(machine, options, "calendar")?;
    let collation = type_option(machine, options, "collation")?;
    let first_day = string_option(machine, options, "firstDayOfWeek", &[])?
        .map(|day| weekday_keyword(&day).to_owned());
    let first_day = checked_type(machine, "firstDayOfWeek", first_day)?;
    let hour_cycle = string_option(machine, options, "hourCycle", &["h11", "h12", "h23", "h24"])?;
    let case_first = string_option(machine, options, "caseFirst", &["upper", "lower", "false"])?;
    let numeric = boolean_option(machine, options, "numeric")?;
    let numbering_system = type_option(machine, options, "numberingSystem")?;

    let keywords = [
        ("ca", calendar),
        ("co", collation),
        ("fw", first_day),
        ("hc", hour_cycle),
        ("kf", case_first),
        ("kn", numeric.map(|value| value.to_string())),
        ("nu", numbering_system),
    ];
    if keywords.iter().any(|(_, value)| value.is_some()) {
        let extension = tag.unicode.get_or_insert_with(UnicodeExtension::default);
        for (key, value) in keywords {
            if let Some(value) = value {
                extension.keywords.insert(key.to_owned(), value);
            }
        }
    }
    let canonical = canonicalize_unicode_locale_id(&tag.to_string(), &*DATA)
        .map_err(|error| range_error(machine, error.to_string()))?;
    let tag = parse(machine, &canonical)?;
    construct(machine, IntlKind::Locale, IntlObject::Locale(tag))
}

fn parse<H: Host>(machine: &mut Machine<'_, H>, text: &str) -> Result<LanguageTag, EvalFailure> {
    LanguageTag::parse(text).map_err(|error| range_error(machine, error.to_string()))
}

fn keyword(tag: &LanguageTag, key: &str) -> Option<String> {
    tag.unicode
        .as_ref()
        .and_then(|extension| extension.keywords.get(key))
        .cloned()
}

macro_rules! keyword_getters {
    ($($name:ident: $key:literal),+ $(,)?) => {
        $(fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let tag = this_locale(machine, this)?;
            optional_string_outcome(machine, keyword(&tag, $key).as_deref())
        })+
    };
}

keyword_getters! {
    calendar: "ca",
    case_first: "kf",
    collation: "co",
    first_day_of_week: "fw",
    hour_cycle: "hc",
    numbering_system: "nu",
}

fn numeric<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    Ok(boolean_outcome(
        keyword(&tag, "kn").is_some_and(|value| value.is_empty() || value == "true"),
    ))
}

fn base_name<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    string_outcome(machine, &tag.id.render())
}

fn language<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    string_outcome(machine, &tag.id.language)
}

fn script<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    optional_string_outcome(machine, tag.id.script.as_deref())
}

fn region<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    optional_string_outcome(machine, tag.id.region.as_deref())
}

fn variants<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    if tag.id.variants.is_empty() {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    string_outcome(machine, &tag.id.variants.join("-"))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    string_outcome(machine, &tag.to_string())
}

/// A new `Intl.Locale` with `tag`'s extensions over a replaced identifier.
fn with_id<H: Host>(
    machine: &mut Machine<'_, H>,
    mut tag: LanguageTag,
    id: Option<LanguageId>,
) -> Result<BuiltinOutcome, EvalFailure> {
    if let Some(id) = id {
        tag.id = id;
    }
    create(machine, IntlObject::Locale(tag)).map(BuiltinOutcome::Value)
}

fn maximize<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    let maximal = locale_data::add_likely_subtags(&tag.id);
    with_id(machine, tag, maximal)
}

fn minimize<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    let minimal = locale_data::remove_likely_subtags(&tag.id);
    with_id(machine, tag, minimal)
}

/// The answer of a `get...` method: the keyword alone when it is present.
fn keyword_or_list<H: Host>(
    machine: &mut Machine<'_, H>,
    tag: &LanguageTag,
    key: &str,
    list: &[&str],
) -> Result<BuiltinOutcome, EvalFailure> {
    let values: Vec<String> = match keyword(tag, key) {
        Some(value) if !value.is_empty() => vec![value],
        _ => list.iter().map(|value| (*value).to_owned()).collect(),
    };
    string_array_outcome(machine, &values)
}

fn get_calendars<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    keyword_or_list(machine, &tag, "ca", locale_data::calendars_of(&tag))
}

fn get_collations<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    keyword_or_list(machine, &tag, "co", locale_data::COLLATIONS)
}

fn get_hour_cycles<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    keyword_or_list(machine, &tag, "hc", locale_data::hour_cycles(&tag))
}

fn get_numbering_systems<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    keyword_or_list(machine, &tag, "nu", locale_data::numbering_systems_of(&tag))
}

fn get_time_zones<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    match locale_data::time_zones_of(&tag) {
        Some(zones) => {
            let zones: Vec<String> = zones.iter().map(|zone| (*zone).to_owned()).collect();
            string_array_outcome(machine, &zones)
        }
        None => Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
    }
}

fn get_text_info<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    let direction = if locale_data::is_right_to_left(&tag) {
        "rtl"
    } else {
        "ltr"
    };
    let result = new_object(machine)?;
    let direction = string_value(machine, direction)?;
    define_field(machine, result, "direction", direction)?;
    Ok(BuiltinOutcome::Value(result))
}

/// The ISO weekday a `-u-fw` value names.
fn weekday_number(value: &str) -> Option<u8> {
    ["mon", "tue", "wed", "thu", "fri", "sat", "sun"]
        .iter()
        .position(|day| *day == value)
        .and_then(|index| u8::try_from(index + 1).ok())
}

fn get_week_info<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let tag = this_locale(machine, this)?;
    let (first_day, weekend) = locale_data::week_info(&tag);
    let first_day = keyword(&tag, "fw")
        .and_then(|value| weekday_number(&value))
        .unwrap_or(first_day);
    let result = new_object(machine)?;
    define_field(
        machine,
        result,
        "firstDay",
        Value::int32(u32::from(first_day)),
    )?;
    let days = weekend
        .iter()
        .map(|day| Value::int32(u32::from(*day)))
        .collect();
    let weekend = allocate_array(machine, days)?;
    define_field(machine, result, "weekend", weekend)?;
    Ok(BuiltinOutcome::Value(result))
}
