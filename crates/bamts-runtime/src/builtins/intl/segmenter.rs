//! `Intl.Segmenter`, its `Segments` objects, and their iterator.

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::options::{
    canonicalize_locale_list, get_options_object, locale_matcher_option, matcher_name,
    string_option,
};
use super::{
    Class, allocate, arg, create, define_field, install_class, instance_prototype, intl_record,
    new_object, require_new, service_failure, string_value, supported_locales_outcome, type_error,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::number_data::NoHostLocale;
use crate::intl::plural_rules::{
    SegmentRecord, SegmentedText, Segmenter, SegmenterGranularity, SegmenterOptions,
};
use crate::intl::{IntlKind, IntlObject, SegmentIteratorRecord, SegmentsRecord};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    install_class(
        heap,
        builtins,
        namespace,
        &Class {
            kind: IntlKind::Segmenter,
            name: "Segmenter",
            tag: "Intl.Segmenter",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[],
            methods: &[
                ("resolvedOptions", 0, resolved_options::<H>),
                ("segment", 1, segment::<H>),
            ],
        },
    );
    let segments = builtins.intl_prototype(IntlKind::Segments);
    let containing = super::install_function(heap, builtins, "containing", 1, containing::<H>);
    super::define_data(heap, segments, "containing", containing);
    let iterator = builtins.symbol_iterator();
    let function =
        super::install_function(heap, builtins, "[Symbol.iterator]", 0, create_iterator::<H>);
    super::define_symbol_method(heap, segments, iterator, function);

    let prototype = builtins.intl_prototype(IntlKind::SegmentIterator);
    let iterator_prototype = builtins.iterator_prototype();
    super::set_prototype(heap, prototype, iterator_prototype);
    let next = super::install_function(heap, builtins, "next", 0, next::<H>);
    super::define_data(heap, prototype, "next", next);
    let tag_symbol = builtins.symbol_to_string_tag();
    super::define_tag(heap, prototype, tag_symbol, "Segmenter String Iterator");
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "Segmenter")?;
    let prototype = instance_prototype(machine, IntlKind::Segmenter, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    let options = get_options_object(machine, arg(args, 1))?;
    let matcher = locale_matcher_option(machine, options)?;
    let granularity = string_option(
        machine,
        options,
        "granularity",
        &["grapheme", "word", "sentence"],
    )?;
    let resolved = SegmenterOptions {
        locale_matcher: Some(matcher_name(matcher).to_owned()),
        granularity,
    };
    let data: &'static IntlData = &DATA;
    let segmenter = Segmenter::try_new(&requested, &resolved, data, &NoHostLocale)
        .map_err(|error| service_failure(machine, &error))?;
    allocate(machine, IntlObject::Segmenter(segmenter), prototype).map(BuiltinOutcome::Value)
}

fn supported_locales_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    supported_locales_outcome(machine, args)
}

fn this_segmenter<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    this: Value,
) -> Result<Option<&'a Segmenter<'static>>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::Segmenter(segmenter)) => Some(segmenter),
        _ => None,
    })
}

fn not_a_segmenter<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.Segmenter")
}

fn segment<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_segmenter(machine, this)?.is_none() {
        return Err(not_a_segmenter(machine));
    }
    let text = machine.coerce_string_observable(arg(args, 0))?;
    let Some(segmenter) = this_segmenter(machine, this)? else {
        return Err(not_a_segmenter(machine));
    };
    let granularity = segmenter.resolved_options().granularity;
    let segmented = segmenter.segment_utf16(text.as_units());
    let text = segmented.map_err(|error| service_failure(machine, &error))?;
    create(
        machine,
        IntlObject::Segments(Box::new(SegmentsRecord { text, granularity })),
    )
    .map(BuiltinOutcome::Value)
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(segmenter) = this_segmenter(machine, this)? else {
        return Err(not_a_segmenter(machine));
    };
    let resolved = segmenter.resolved_options();
    let result = new_object(machine)?;
    for (name, text) in [
        ("locale", resolved.locale.as_str()),
        ("granularity", resolved.granularity.as_str()),
    ] {
        let value = string_value(machine, text)?;
        define_field(machine, result, name, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

/// CreateSegmentDataObject.
fn segment_data<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &SegmentedText,
    record: &SegmentRecord,
    granularity: SegmenterGranularity,
) -> Result<Value, EvalFailure> {
    let result = new_object(machine)?;
    let segment =
        super::super::allocate_string(machine, EcmaString::from_units(text.segment(record)))?;
    define_field(machine, result, "segment", segment)?;
    let index = crate::number_value(record.start as f64);
    define_field(machine, result, "index", index)?;
    let input = super::super::allocate_string(machine, EcmaString::from_units(text.input()))?;
    define_field(machine, result, "input", input)?;
    if granularity == SegmenterGranularity::Word {
        let word_like = Value::boolean(record.is_word_like.unwrap_or(false));
        define_field(machine, result, "isWordLike", word_like)?;
    }
    Ok(result)
}

fn this_segments<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<SegmentsRecord, EvalFailure> {
    match intl_record(machine, this)? {
        Some(IntlObject::Segments(record)) => Ok((**record).clone()),
        _ => Err(type_error(machine, "receiver is not a Segments object")),
    }
}

fn containing<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = this_segments(machine, this)?;
    let number = machine.coerce_number_observable(arg(args, 0))?;
    let number = match number.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) if number.is_nan() => 0.0,
        Some(Decoded::Number(number)) => number.trunc(),
        _ => 0.0,
    };
    if number < 0.0 || number >= record.text.input().len() as f64 {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let Some(segment) = record.text.containing(number as usize) else {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    };
    segment_data(machine, &record.text, segment, record.granularity).map(BuiltinOutcome::Value)
}

fn create_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = this_segments(machine, this)?;
    create(
        machine,
        IntlObject::SegmentIterator(Box::new(SegmentIteratorRecord {
            text: record.text,
            granularity: record.granularity,
            next_record: 0,
        })),
    )
    .map(BuiltinOutcome::Value)
}

fn next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(machine, "receiver is not a Segment Iterator"));
    };
    let HeapEntry::Intl { value, .. } = &mut machine.heap[index] else {
        return Err(type_error(machine, "receiver is not a Segment Iterator"));
    };
    let IntlObject::SegmentIterator(iterator) = &mut **value else {
        return Err(type_error(machine, "receiver is not a Segment Iterator"));
    };
    let Some(record) = iterator.text.records().get(iterator.next_record).cloned() else {
        return machine
            .iterator_result(Value::UNDEFINED, true)
            .map(BuiltinOutcome::Value);
    };
    iterator.next_record += 1;
    let text = iterator.text.clone();
    let granularity = iterator.granularity;
    let data = segment_data(machine, &text, &record, granularity)?;
    machine
        .iterator_result(data, false)
        .map(BuiltinOutcome::Value)
}
