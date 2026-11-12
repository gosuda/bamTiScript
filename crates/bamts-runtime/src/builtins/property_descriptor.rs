use bamts_native::{Decoded, Value};

use super::type_error;
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

/// The transient, partial descriptor record used by the ECMAScript descriptor
/// abstract operations. Stored properties remain the canonical [`Property`].
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct PropertyDescriptor {
    pub(crate) value: Option<Value>,
    pub(crate) writable: Option<bool>,
    pub(crate) getter: Option<Value>,
    pub(crate) setter: Option<Value>,
    pub(crate) enumerable: Option<bool>,
    pub(crate) configurable: Option<bool>,
}

impl PropertyDescriptor {
    pub(crate) fn is_accessor(self) -> bool {
        self.getter.is_some() || self.setter.is_some()
    }

    pub(crate) fn is_data(self) -> bool {
        self.value.is_some() || self.writable.is_some()
    }

    fn is_empty(self) -> bool {
        self.value.is_none()
            && self.writable.is_none()
            && self.getter.is_none()
            && self.setter.is_none()
            && self.enumerable.is_none()
            && self.configurable.is_none()
    }

    pub(crate) fn into_property(self, current: Option<Property>) -> Property {
        let enumerable = self
            .enumerable
            .unwrap_or_else(|| current.as_ref().is_some_and(Property::enumerable));
        let configurable = self
            .configurable
            .unwrap_or_else(|| current.as_ref().is_some_and(Property::configurable));

        if self.is_accessor() {
            let (current_getter, current_setter) = match current {
                Some(Property::Accessor { getter, setter, .. }) => (getter, setter),
                _ => (None, None),
            };
            return Property::Accessor {
                getter: self
                    .getter
                    .map(|value| (value != Value::UNDEFINED).then_some(value))
                    .unwrap_or(current_getter),
                setter: self
                    .setter
                    .map(|value| (value != Value::UNDEFINED).then_some(value))
                    .unwrap_or(current_setter),
                enumerable,
                configurable,
            };
        }

        if self.is_data() {
            let (current_value, current_writable) = match current {
                Some(Property::Data {
                    value, writable, ..
                }) => (value, writable),
                _ => (Value::UNDEFINED, false),
            };
            return Property::Data {
                value: self.value.unwrap_or(current_value),
                writable: self.writable.unwrap_or(current_writable),
                enumerable,
                configurable,
            };
        }

        match current {
            Some(Property::Accessor { getter, setter, .. }) => Property::Accessor {
                getter,
                setter,
                enumerable,
                configurable,
            },
            Some(Property::Data {
                value, writable, ..
            }) => Property::Data {
                value,
                writable,
                enumerable,
                configurable,
            },
            None => Property::Data {
                value: Value::UNDEFINED,
                writable: false,
                enumerable,
                configurable,
            },
        }
    }
}

fn descriptor_field<H: Host>(
    machine: &mut Machine<'_, H>,
    descriptor: Value,
    name: &str,
) -> Result<Option<Value>, EvalFailure> {
    let key = PropertyKey::Named(machine.intern_str(name));
    if !machine.internal_has_property(descriptor, &key)? {
        return Ok(None);
    }
    machine.get_property_key(descriptor, &key).map(Some)
}

/// ECMA-262 ToPropertyDescriptor. `HasProperty` and `Get` are deliberately
/// paired field-by-field so inherited accessors and abrupt completion order are
/// observable in specification order.
pub(crate) fn to_property_descriptor<H: Host>(
    machine: &mut Machine<'_, H>,
    descriptor: Value,
) -> Result<PropertyDescriptor, EvalFailure> {
    if !machine.is_object(descriptor) {
        return Err(type_error("Property description must be an object"));
    }

    let enumerable =
        descriptor_field(machine, descriptor, "enumerable")?.map(|value| machine.to_boolean(value));
    let configurable = descriptor_field(machine, descriptor, "configurable")?
        .map(|value| machine.to_boolean(value));
    let value = descriptor_field(machine, descriptor, "value")?;
    let writable =
        descriptor_field(machine, descriptor, "writable")?.map(|value| machine.to_boolean(value));

    let getter = descriptor_field(machine, descriptor, "get")?;
    if let Some(getter) = getter
        && getter != Value::UNDEFINED
        && !machine.is_callable(getter)?
    {
        return Err(type_error("Getter must be callable or undefined"));
    }

    let setter = descriptor_field(machine, descriptor, "set")?;
    if let Some(setter) = setter
        && setter != Value::UNDEFINED
        && !machine.is_callable(setter)?
    {
        return Err(type_error("Setter must be callable or undefined"));
    }

    if (getter.is_some() || setter.is_some()) && (value.is_some() || writable.is_some()) {
        return Err(type_error(
            "Property descriptor cannot be both a data and an accessor descriptor",
        ));
    }

    Ok(PropertyDescriptor {
        value,
        writable,
        getter,
        setter,
        enumerable,
        configurable,
    })
}

fn define_reified_field<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    value: Value,
) -> Result<(), EvalFailure> {
    let key = PropertyKey::Named(machine.intern_str(name));
    machine.define_descriptor(
        object,
        key,
        Property::Data {
            value,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    )
}

/// ECMA-262 FromPropertyDescriptor. The result is a fresh ordinary object and
/// only fields present in the transient record become own properties.
pub(crate) fn from_property_descriptor<H: Host>(
    machine: &mut Machine<'_, H>,
    descriptor: Option<PropertyDescriptor>,
) -> Result<Value, EvalFailure> {
    let Some(descriptor) = descriptor else {
        return Ok(Value::UNDEFINED);
    };
    let object = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;

    for (name, value) in [
        ("value", descriptor.value),
        ("writable", descriptor.writable.map(Value::boolean)),
        ("get", descriptor.getter),
        ("set", descriptor.setter),
        ("enumerable", descriptor.enumerable.map(Value::boolean)),
        ("configurable", descriptor.configurable.map(Value::boolean)),
    ] {
        if let Some(value) = value {
            define_reified_field(machine, object, name, value)?;
        }
    }
    Ok(object)
}

pub(crate) fn descriptor_from_property(property: Property) -> PropertyDescriptor {
    match property {
        Property::Data {
            value,
            writable,
            enumerable,
            configurable,
        } => PropertyDescriptor {
            value: Some(value),
            writable: Some(writable),
            getter: None,
            setter: None,
            enumerable: Some(enumerable),
            configurable: Some(configurable),
        },
        Property::Accessor {
            getter,
            setter,
            enumerable,
            configurable,
        } => PropertyDescriptor {
            value: None,
            writable: None,
            getter: Some(getter.unwrap_or(Value::UNDEFINED)),
            setter: Some(setter.unwrap_or(Value::UNDEFINED)),
            enumerable: Some(enumerable),
            configurable: Some(configurable),
        },
    }
}

/// ECMA-262 CompletePropertyDescriptor. Fills only absent fields with the
/// appropriate defaults while preserving the descriptor kind: accessor
/// descriptors receive `undefined` for a missing get/set, data and generic
/// descriptors receive `undefined`/`false` for a missing value/writable, and
/// every kind receives `false` for a missing enumerable/configurable. Present
/// fields are never altered, so an already-fully-populated descriptor is
/// returned unchanged.
pub(crate) fn complete_property_descriptor(
    mut descriptor: PropertyDescriptor,
) -> PropertyDescriptor {
    if descriptor.is_accessor() {
        if descriptor.getter.is_none() {
            descriptor.getter = Some(Value::UNDEFINED);
        }
        if descriptor.setter.is_none() {
            descriptor.setter = Some(Value::UNDEFINED);
        }
    } else {
        if descriptor.value.is_none() {
            descriptor.value = Some(Value::UNDEFINED);
        }
        if descriptor.writable.is_none() {
            descriptor.writable = Some(false);
        }
    }
    if descriptor.enumerable.is_none() {
        descriptor.enumerable = Some(false);
    }
    if descriptor.configurable.is_none() {
        descriptor.configurable = Some(false);
    }
    descriptor
}

pub(super) fn same_value<H: Host>(machine: &Machine<'_, H>, left: Value, right: Value) -> bool {
    match (left.decode(), right.decode()) {
        (Some(Decoded::Number(left)), Some(Decoded::Number(right))) => {
            (left.is_nan() && right.is_nan())
                || (left == right
                    && (left != 0.0 || left.is_sign_positive() == right.is_sign_positive()))
        }
        (Some(Decoded::Number(number)), Some(Decoded::Int32(integer)))
        | (Some(Decoded::Int32(integer)), Some(Decoded::Number(number))) => {
            number == f64::from(integer as i32) && (number != 0.0 || number.is_sign_positive())
        }
        (Some(Decoded::Int32(left)), Some(Decoded::Int32(right))) => left == right,
        _ => machine.strict_equal(left, right),
    }
}

/// ECMA-262 IsCompatiblePropertyDescriptor. This has no mutation side effects.
/// `current` is a descriptor record, typically converted from a stored property
/// via [`descriptor_from_property`].
pub(super) fn is_compatible_property_descriptor<H: Host>(
    machine: &Machine<'_, H>,
    extensible: bool,
    descriptor: PropertyDescriptor,
    current: Option<&PropertyDescriptor>,
) -> bool {
    let Some(current) = current else {
        return extensible;
    };
    if descriptor.is_empty() {
        return true;
    }
    if current.configurable.unwrap_or(false) {
        return true;
    }
    if descriptor.configurable == Some(true)
        || descriptor
            .enumerable
            .is_some_and(|enumerable| enumerable != current.enumerable.unwrap_or(false))
    {
        return false;
    }

    let current_is_accessor = current.is_accessor();
    if (descriptor.is_accessor() || descriptor.is_data())
        && descriptor.is_accessor() != current_is_accessor
    {
        return false;
    }

    if current_is_accessor {
        if let Some(candidate) = descriptor.getter
            && !same_value(
                machine,
                candidate,
                current.getter.unwrap_or(Value::UNDEFINED),
            )
        {
            return false;
        }
        if let Some(candidate) = descriptor.setter
            && !same_value(
                machine,
                candidate,
                current.setter.unwrap_or(Value::UNDEFINED),
            )
        {
            return false;
        }
    } else if current.writable != Some(true) {
        if descriptor.writable == Some(true) {
            return false;
        }
        if let Some(candidate) = descriptor.value {
            return same_value(
                machine,
                candidate,
                current.value.unwrap_or(Value::UNDEFINED),
            );
        }
    }
    true
}

/// ECMA-262 ValidateAndApplyPropertyDescriptor. Passing `None` as `target`
/// performs compatibility validation only; passing a target applies through the
/// canonical `Machine::define_descriptor` storage path. The stored `current`
/// property is converted to a [`PropertyDescriptor`] record so compatibility
/// operates on descriptor records; application still merges onto the stored
/// property.
pub(crate) fn validate_and_apply_property_descriptor<H: Host>(
    machine: &mut Machine<'_, H>,
    target: Option<(Value, PropertyKey)>,
    extensible: bool,
    descriptor: PropertyDescriptor,
    current: Option<Property>,
) -> Result<bool, EvalFailure> {
    let descriptor = if current.is_none() {
        complete_property_descriptor(descriptor)
    } else {
        descriptor
    };
    let current_record = current.clone().map(descriptor_from_property);
    if !is_compatible_property_descriptor(machine, extensible, descriptor, current_record.as_ref())
    {
        return Ok(false);
    }
    let Some((object, key)) = target else {
        return Ok(true);
    };
    if current_record.is_some() && descriptor.is_empty() {
        return Ok(true);
    }

    machine.define_descriptor(object, key, descriptor.into_property(current))?;
    Ok(true)
}

/// Reads the target's canonical extensibility bit for descriptor validation.
pub(crate) fn is_extensible<H: Host>(
    machine: &Machine<'_, H>,
    object: Value,
) -> Result<bool, EvalFailure> {
    let Some(index) = machine.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
        return Ok(false);
    };
    Ok(match &machine.heap[index] {
        HeapEntry::Object { extensible, .. }
        | HeapEntry::Array { extensible, .. }
        | HeapEntry::Function { extensible, .. }
        | HeapEntry::Script { extensible, .. }
        | HeapEntry::RegExp { extensible, .. }
        | HeapEntry::Date { extensible, .. }
        | HeapEntry::Temporal { extensible, .. }
        | HeapEntry::Intl { extensible, .. }
        | HeapEntry::Collection { extensible, .. }
        | HeapEntry::BuiltinIterator { extensible, .. }
        | HeapEntry::Generator { extensible, .. }
        | HeapEntry::AsyncGenerator { extensible, .. }
        | HeapEntry::Promise { extensible, .. }
        | HeapEntry::DisposableStack { extensible, .. }
        | HeapEntry::Timeout { extensible, .. }
        | HeapEntry::NativeFunction { extensible, .. }
        | HeapEntry::ProcessEnv { extensible, .. }
        | HeapEntry::TypedArray { extensible, .. }
        | HeapEntry::ArrayBuffer { extensible, .. }
        | HeapEntry::SharedArrayBuffer { extensible, .. }
        | HeapEntry::DataView { extensible, .. }
        | HeapEntry::WeakRef { extensible, .. }
        | HeapEntry::FinalizationRegistry { extensible, .. }
        | HeapEntry::ProxyRevoker { extensible, .. } => *extensible,
        HeapEntry::ModuleNamespace { .. } | HeapEntry::ExternalModuleNamespace { .. } => false,
        _ => false,
    })
}

/// Collects DefineProperties inputs in `[[OwnPropertyKeys]]` order and converts
/// every descriptor before any target mutation.
pub(super) fn collect_property_descriptors<H: Host>(
    machine: &mut Machine<'_, H>,
    descriptors: Value,
) -> Result<Vec<(PropertyKey, PropertyDescriptor)>, EvalFailure> {
    let mut definitions = Vec::new();
    for key in machine.internal_own_property_keys(descriptors)? {
        if !machine
            .internal_get_own_property(descriptors, &key)?
            .is_some_and(|descriptor| descriptor.enumerable == Some(true))
        {
            continue;
        }
        let descriptor = machine.get_property_key(descriptors, &key)?;
        definitions.push((key, to_property_descriptor(machine, descriptor)?));
    }
    Ok(definitions)
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, BuiltinOutcome, native_function};
    use crate::{Limits, ThrowOrigin};

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("property-descriptor");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn data(value: Value, writable: bool, configurable: bool) -> Property {
        Property::Data {
            value,
            writable,
            enumerable: false,
            configurable,
        }
    }

    fn accessor(getter: Option<Value>, setter: Option<Value>, configurable: bool) -> Property {
        Property::Accessor {
            getter,
            setter,
            enumerable: false,
            configurable,
        }
    }

    fn partial_data(value: Value) -> PropertyDescriptor {
        PropertyDescriptor {
            value: Some(value),
            ..PropertyDescriptor::default()
        }
    }

    fn partial_accessor(getter: Value) -> PropertyDescriptor {
        PropertyDescriptor {
            getter: Some(getter),
            ..PropertyDescriptor::default()
        }
    }

    #[test]
    fn compatibility_transition_matrix_covers_absent_data_accessor_and_generic_cells() {
        with_machine(|machine| {
            let getter = machine.intrinsics.global("Object").unwrap();
            let generic = PropertyDescriptor {
                enumerable: Some(false),
                ..PropertyDescriptor::default()
            };
            let data_desc = partial_data(Value::int32(1));
            let accessor_desc = partial_accessor(getter);
            let configurable_data = descriptor_from_property(data(Value::int32(0), true, true));
            let configurable_accessor =
                descriptor_from_property(accessor(Some(getter), None, true));
            let writable_data = descriptor_from_property(data(Value::int32(0), true, false));
            let readonly_data = descriptor_from_property(data(Value::int32(1), false, false));
            let fixed_accessor = descriptor_from_property(accessor(Some(getter), None, false));

            let cases = [
                ("absent/nonext/generic", false, generic, None, false),
                ("absent/nonext/data", false, data_desc, None, false),
                ("absent/nonext/accessor", false, accessor_desc, None, false),
                ("absent/ext/generic", true, generic, None, true),
                ("absent/ext/data", true, data_desc, None, true),
                ("absent/ext/accessor", true, accessor_desc, None, true),
                (
                    "config-data/generic",
                    true,
                    generic,
                    Some(&configurable_data),
                    true,
                ),
                (
                    "config-data/data",
                    true,
                    data_desc,
                    Some(&configurable_data),
                    true,
                ),
                (
                    "config-data/accessor",
                    true,
                    accessor_desc,
                    Some(&configurable_data),
                    true,
                ),
                (
                    "config-accessor/generic",
                    true,
                    generic,
                    Some(&configurable_accessor),
                    true,
                ),
                (
                    "config-accessor/data",
                    true,
                    data_desc,
                    Some(&configurable_accessor),
                    true,
                ),
                (
                    "config-accessor/accessor",
                    true,
                    accessor_desc,
                    Some(&configurable_accessor),
                    true,
                ),
                (
                    "writable-data/generic",
                    true,
                    generic,
                    Some(&writable_data),
                    true,
                ),
                (
                    "writable-data/data",
                    true,
                    data_desc,
                    Some(&writable_data),
                    true,
                ),
                (
                    "writable-data/accessor",
                    true,
                    accessor_desc,
                    Some(&writable_data),
                    false,
                ),
                (
                    "readonly-data/generic",
                    true,
                    generic,
                    Some(&readonly_data),
                    true,
                ),
                (
                    "readonly-data/data",
                    true,
                    data_desc,
                    Some(&readonly_data),
                    true,
                ),
                (
                    "readonly-data/accessor",
                    true,
                    accessor_desc,
                    Some(&readonly_data),
                    false,
                ),
                (
                    "fixed-accessor/generic",
                    true,
                    generic,
                    Some(&fixed_accessor),
                    true,
                ),
                (
                    "fixed-accessor/data",
                    true,
                    data_desc,
                    Some(&fixed_accessor),
                    false,
                ),
                (
                    "fixed-accessor/accessor",
                    true,
                    accessor_desc,
                    Some(&fixed_accessor),
                    true,
                ),
            ];
            for (name, extensible, descriptor, current, expected) in cases {
                assert_eq!(
                    is_compatible_property_descriptor(machine, extensible, descriptor, current),
                    expected,
                    "{name}",
                );
            }
        });
    }

    #[test]
    fn non_configurable_invariants_cover_every_attribute() {
        with_machine(|machine| {
            let getter = machine.intrinsics.global("Object").unwrap();
            let setter = machine.intrinsics.global("Array").unwrap();
            let fixed_data = descriptor_from_property(data(Value::int32(1), false, false));
            let fixed_accessor =
                descriptor_from_property(accessor(Some(getter), Some(setter), false));
            for descriptor in [
                PropertyDescriptor {
                    configurable: Some(true),
                    ..PropertyDescriptor::default()
                },
                PropertyDescriptor {
                    enumerable: Some(true),
                    ..PropertyDescriptor::default()
                },
                PropertyDescriptor {
                    writable: Some(true),
                    ..PropertyDescriptor::default()
                },
                partial_data(Value::int32(2)),
                partial_accessor(getter),
            ] {
                assert!(!is_compatible_property_descriptor(
                    machine,
                    true,
                    descriptor,
                    Some(&fixed_data),
                ));
            }
            for descriptor in [
                PropertyDescriptor {
                    configurable: Some(true),
                    ..PropertyDescriptor::default()
                },
                PropertyDescriptor {
                    enumerable: Some(true),
                    ..PropertyDescriptor::default()
                },
                partial_data(Value::int32(1)),
                partial_accessor(setter),
                PropertyDescriptor {
                    setter: Some(getter),
                    ..PropertyDescriptor::default()
                },
            ] {
                assert!(!is_compatible_property_descriptor(
                    machine,
                    true,
                    descriptor,
                    Some(&fixed_accessor),
                ));
            }
        });
    }

    #[test]
    fn same_value_accepts_nan_and_distinguishes_signed_zero() {
        with_machine(|machine| {
            let nan = descriptor_from_property(data(Value::number(f64::NAN), false, false));
            assert!(is_compatible_property_descriptor(
                machine,
                true,
                partial_data(Value::number(f64::NAN)),
                Some(&nan),
            ));
            let negative_zero = descriptor_from_property(data(Value::number(-0.0), false, false));
            assert!(!is_compatible_property_descriptor(
                machine,
                true,
                partial_data(Value::number(0.0)),
                Some(&negative_zero),
            ));
            assert!(!is_compatible_property_descriptor(
                machine,
                true,
                partial_data(Value::int32(0)),
                Some(&negative_zero),
            ));
            assert!(is_compatible_property_descriptor(
                machine,
                true,
                partial_data(Value::number(-0.0)),
                Some(&negative_zero),
            ));
        });
    }

    #[test]
    fn accessor_compatibility_uses_identity_and_normalizes_undefined() {
        with_machine(|machine| {
            let getter = machine.intrinsics.global("Object").unwrap();
            let other = machine.intrinsics.global("Array").unwrap();
            let fixed = descriptor_from_property(accessor(Some(getter), None, false));
            assert!(is_compatible_property_descriptor(
                machine,
                true,
                partial_accessor(getter),
                Some(&fixed),
            ));
            assert!(!is_compatible_property_descriptor(
                machine,
                true,
                partial_accessor(other),
                Some(&fixed),
            ));
            assert!(is_compatible_property_descriptor(
                machine,
                true,
                PropertyDescriptor {
                    setter: Some(Value::UNDEFINED),
                    ..PropertyDescriptor::default()
                },
                Some(&fixed),
            ));
        });
    }

    #[test]
    fn configurable_properties_transition_both_directions_with_defaults() {
        with_machine(|machine| {
            let object = ordinary_object(machine);
            let key = PropertyKey::Named(machine.intern_str("x"));
            machine
                .define_descriptor(object, key.clone(), data(Value::int32(3), true, true))
                .unwrap();
            let getter = machine.intrinsics.global("Object").unwrap();
            let current = machine.own_descriptor(object, &key).unwrap();
            assert!(
                validate_and_apply_property_descriptor(
                    machine,
                    Some((object, key.clone())),
                    true,
                    partial_accessor(getter),
                    current,
                )
                .unwrap()
            );
            assert!(matches!(
                machine.own_descriptor(object, &key).unwrap(),
                Some(Property::Accessor {
                    getter: Some(actual), setter: None, enumerable: false, configurable: true,
                }) if actual == getter
            ));
            let current = machine.own_descriptor(object, &key).unwrap();
            assert!(
                validate_and_apply_property_descriptor(
                    machine,
                    Some((object, key.clone())),
                    true,
                    partial_data(Value::int32(7)),
                    current,
                )
                .unwrap()
            );
            assert!(matches!(
                machine.own_descriptor(object, &key).unwrap(),
                Some(Property::Data {
                    value, writable: false, enumerable: false, configurable: true,
                }) if value == Value::int32(7)
            ));
        });
    }

    #[test]
    fn application_preserves_omitted_fields_and_rejects_non_extensible_creation() {
        with_machine(|machine| {
            let object = ordinary_object(machine);
            let key = PropertyKey::Named(machine.intern_str("x"));
            machine
                .define_descriptor(object, key.clone(), data(Value::int32(3), true, true))
                .unwrap();
            let current = machine.own_descriptor(object, &key).unwrap();
            assert!(
                validate_and_apply_property_descriptor(
                    machine,
                    Some((object, key.clone())),
                    true,
                    PropertyDescriptor {
                        writable: Some(false),
                        ..PropertyDescriptor::default()
                    },
                    current,
                )
                .unwrap()
            );
            assert!(matches!(
                machine.own_descriptor(object, &key).unwrap(),
                Some(Property::Data {
                    value, writable: false, enumerable: false, configurable: true,
                }) if value == Value::int32(3)
            ));

            let created_empty = PropertyKey::Named(machine.intern_str("created_empty"));
            assert!(
                validate_and_apply_property_descriptor(
                    machine,
                    Some((object, created_empty.clone())),
                    true,
                    PropertyDescriptor::default(),
                    None,
                )
                .unwrap()
            );
            assert!(matches!(
                machine.own_descriptor(object, &created_empty).unwrap(),
                Some(Property::Data {
                    value: Value::UNDEFINED,
                    writable: false,
                    enumerable: false,
                    configurable: false,
                })
            ));

            let slot = machine.runtime_slot(object).unwrap().unwrap();
            let HeapEntry::Object { extensible, .. } = &mut machine.heap[slot] else {
                unreachable!();
            };
            *extensible = false;
            let current = machine.own_descriptor(object, &key).unwrap();
            assert!(
                validate_and_apply_property_descriptor(
                    machine,
                    Some((object, key.clone())),
                    false,
                    partial_data(Value::int32(8)),
                    current,
                )
                .unwrap()
            );
            assert_eq!(
                machine.get_named_property(object, "x").unwrap(),
                Value::int32(8)
            );
            let empty = PropertyKey::Named(machine.intern_str("empty"));
            assert!(
                !validate_and_apply_property_descriptor(
                    machine,
                    Some((object, empty.clone())),
                    false,
                    PropertyDescriptor::default(),
                    None,
                )
                .unwrap()
            );
            assert!(machine.own_descriptor(object, &empty).unwrap().is_none());
            let missing = PropertyKey::Named(machine.intern_str("missing"));
            assert!(
                !validate_and_apply_property_descriptor(
                    machine,
                    Some((object, missing.clone())),
                    false,
                    partial_data(Value::int32(1)),
                    None,
                )
                .unwrap()
            );
            assert!(machine.own_descriptor(object, &missing).unwrap().is_none());
            assert!(!is_extensible(machine, object).unwrap());
        });
    }

    fn enumerable_probe<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if machine.get_named_property(this, "step")? != Value::int32(0) {
            return Err(type_error("enumerable read out of order"));
        }
        machine.set_data_property(this, "step", Value::int32(1))?;
        Ok(BuiltinOutcome::Value(Value::TRUE))
    }

    fn configurable_abrupt<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if machine.get_named_property(this, "step")? != Value::int32(1) {
            return Err(type_error("configurable read out of order"));
        }
        machine.set_data_property(this, "step", Value::int32(2))?;
        Err(type_error("configurable abrupt completion"))
    }

    fn setter_lookup_probe<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "setter_reads", Value::int32(1))?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn install_probe(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: crate::intrinsics::BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            0,
        )
    }

    #[test]
    fn to_descriptor_observes_prototypes_and_propagates_abrupt_order() {
        with_machine(|machine| {
            let prototype = ordinary_object(machine);
            machine
                .set_data_property(prototype, "value", Value::int32(9))
                .unwrap();
            let inherited = machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap();
            let descriptor = to_property_descriptor(machine, inherited).unwrap();
            assert_eq!(descriptor.value, Some(Value::int32(9)));

            let object = ordinary_object(machine);
            machine
                .set_data_property(object, "step", Value::int32(0))
                .unwrap();
            let enumerable =
                install_probe(machine, "enumerable probe", enumerable_probe::<TestHost>);
            let configurable = install_probe(
                machine,
                "configurable abrupt",
                configurable_abrupt::<TestHost>,
            );
            for (name, getter) in [("enumerable", enumerable), ("configurable", configurable)] {
                let key = PropertyKey::Named(machine.intern_str(name));
                machine
                    .define_descriptor(
                        object,
                        key,
                        Property::Accessor {
                            getter: Some(getter),
                            setter: None,
                            enumerable: true,
                            configurable: true,
                        },
                    )
                    .unwrap();
            }
            assert!(matches!(
                to_property_descriptor(machine, object),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                machine.get_named_property(object, "step").unwrap(),
                Value::int32(2)
            );
        });
    }

    #[test]
    fn getter_validation_precedes_setter_lookup_and_mixed_shape_rejection() {
        with_machine(|machine| {
            let object = ordinary_object(machine);
            machine
                .set_data_property(object, "setter_reads", Value::int32(0))
                .unwrap();
            machine
                .set_data_property(object, "get", Value::int32(1))
                .unwrap();
            let setter_probe = install_probe(
                machine,
                "setter lookup probe",
                setter_lookup_probe::<TestHost>,
            );
            let set_key = PropertyKey::Named(machine.intern_str("set"));
            machine
                .define_descriptor(
                    object,
                    set_key,
                    Property::Accessor {
                        getter: Some(setter_probe),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            assert!(matches!(
                to_property_descriptor(machine, object),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                machine.get_named_property(object, "setter_reads").unwrap(),
                Value::int32(0)
            );

            let invalid_setter = ordinary_object(machine);
            machine
                .set_data_property(invalid_setter, "get", Value::UNDEFINED)
                .unwrap();
            machine
                .set_data_property(invalid_setter, "set", Value::int32(2))
                .unwrap();
            assert!(matches!(
                to_property_descriptor(machine, invalid_setter),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            let mixed = ordinary_object(machine);
            machine
                .set_data_property(mixed, "value", Value::int32(1))
                .unwrap();
            machine
                .set_data_property(mixed, "get", Value::UNDEFINED)
                .unwrap();
            assert!(matches!(
                to_property_descriptor(machine, mixed),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn from_descriptor_reifies_only_present_fields_with_standard_attributes() {
        with_machine(|machine| {
            assert_eq!(
                from_property_descriptor(machine, None).unwrap(),
                Value::UNDEFINED
            );
            let object = from_property_descriptor(
                machine,
                Some(PropertyDescriptor {
                    value: Some(Value::int32(4)),
                    writable: Some(false),
                    enumerable: Some(true),
                    ..PropertyDescriptor::default()
                }),
            )
            .unwrap();
            assert_eq!(
                machine.get_named_property(object, "value").unwrap(),
                Value::int32(4)
            );
            assert_eq!(
                machine.get_named_property(object, "writable").unwrap(),
                Value::FALSE
            );
            assert_eq!(
                machine.get_named_property(object, "enumerable").unwrap(),
                Value::TRUE
            );
            let get_key = PropertyKey::Named(machine.intern_str("get"));
            assert!(machine.own_descriptor(object, &get_key).unwrap().is_none());
            for name in ["value", "writable", "enumerable"] {
                let name_key = PropertyKey::Named(machine.intern_str(name));
                assert!(matches!(
                    machine.own_descriptor(object, &name_key).unwrap(),
                    Some(Property::Data {
                        writable: true,
                        enumerable: true,
                        configurable: true,
                        ..
                    })
                ));
            }
            let slot = machine.runtime_slot(object).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[slot],
                HeapEntry::Object {
                    prototype: Some(prototype),
                    ..
                } if *prototype == machine.intrinsics.object_prototype
            ));

            let getter = machine.intrinsics.global("Object").unwrap();
            let accessor_object = from_property_descriptor(
                machine,
                Some(PropertyDescriptor {
                    getter: Some(getter),
                    setter: Some(Value::UNDEFINED),
                    configurable: Some(false),
                    ..PropertyDescriptor::default()
                }),
            )
            .unwrap();
            assert_eq!(
                machine.get_named_property(accessor_object, "get").unwrap(),
                getter
            );
            assert_eq!(
                machine.get_named_property(accessor_object, "set").unwrap(),
                Value::UNDEFINED
            );
            let value_key = PropertyKey::Named(machine.intern_str("value"));
            assert!(
                machine
                    .own_descriptor(accessor_object, &value_key,)
                    .unwrap()
                    .is_none()
            );
        });
    }

    #[test]
    fn descriptor_collection_uses_index_string_then_symbol_order() {
        with_machine(|machine| {
            let descriptors = ordinary_object(machine);
            let descriptor = ordinary_object(machine);
            machine
                .set_data_property(descriptor, "value", Value::int32(1))
                .unwrap();
            for name in ["b", "10", "2", "a"] {
                machine
                    .set_data_property(descriptors, name, descriptor)
                    .unwrap();
            }
            let first_symbol = machine
                .property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                .unwrap();
            let second_symbol = machine
                .property_key_from_value(machine.intrinsics.builtins.symbol_to_string_tag())
                .unwrap();
            machine
                .set_data_property_key(descriptors, first_symbol.clone(), descriptor)
                .unwrap();
            machine
                .set_data_property_key(descriptors, second_symbol.clone(), descriptor)
                .unwrap();

            let keys: Vec<_> = collect_property_descriptors(machine, descriptors)
                .unwrap()
                .into_iter()
                .map(|(key, _)| key)
                .collect();
            assert_eq!(
                keys,
                vec![
                    PropertyKey::Named(machine.intern_str("2")),
                    PropertyKey::Named(machine.intern_str("10")),
                    PropertyKey::Named(machine.intern_str("b")),
                    PropertyKey::Named(machine.intern_str("a")),
                    first_symbol,
                    second_symbol,
                ]
            );
        });
    }

    #[test]
    fn complete_fills_generic_descriptor_with_data_defaults() {
        let generic = PropertyDescriptor {
            enumerable: Some(true),
            ..PropertyDescriptor::default()
        };
        let completed = complete_property_descriptor(generic);
        // A generic descriptor is neither accessor nor data; completion treats
        // it as data per ECMA-262 CompletePropertyDescriptor.
        assert_eq!(completed.value, Some(Value::UNDEFINED));
        assert_eq!(completed.writable, Some(false));
        assert_eq!(completed.getter, None);
        assert_eq!(completed.setter, None);
        // Present enumerable is preserved; absent configurable defaults false.
        assert_eq!(completed.enumerable, Some(true));
        assert_eq!(completed.configurable, Some(false));
    }

    #[test]
    fn complete_fills_data_descriptor_preserving_present_fields() {
        let data_desc = PropertyDescriptor {
            value: Some(Value::int32(42)),
            writable: Some(true),
            enumerable: Some(true),
            ..PropertyDescriptor::default()
        };
        let completed = complete_property_descriptor(data_desc);
        assert_eq!(completed.value, Some(Value::int32(42)));
        assert_eq!(completed.writable, Some(true));
        assert_eq!(completed.enumerable, Some(true));
        assert_eq!(completed.configurable, Some(false));
        assert_eq!(completed.getter, None);
        assert_eq!(completed.setter, None);
    }

    #[test]
    fn complete_fills_accessor_descriptor_preserving_present_fields() {
        let getter = Value::int32(1); // placeholder callable-like value; semantics only need identity
        let accessor_desc = PropertyDescriptor {
            getter: Some(getter),
            enumerable: Some(false),
            ..PropertyDescriptor::default()
        };
        let completed = complete_property_descriptor(accessor_desc);
        assert_eq!(completed.getter, Some(getter));
        assert_eq!(completed.setter, Some(Value::UNDEFINED));
        assert_eq!(completed.enumerable, Some(false));
        assert_eq!(completed.configurable, Some(false));
        // Accessor completion must not synthesize data fields.
        assert_eq!(completed.value, None);
        assert_eq!(completed.writable, None);
    }

    #[test]
    fn complete_leaves_fully_populated_descriptors_unchanged() {
        let getter = Value::int32(7);
        let full_accessor = PropertyDescriptor {
            getter: Some(getter),
            setter: Some(Value::UNDEFINED),
            enumerable: Some(true),
            configurable: Some(false),
            ..PropertyDescriptor::default()
        };
        let completed = complete_property_descriptor(full_accessor);
        assert_eq!(completed.getter, Some(getter));
        assert_eq!(completed.setter, Some(Value::UNDEFINED));
        assert_eq!(completed.enumerable, Some(true));
        assert_eq!(completed.configurable, Some(false));
        assert_eq!(completed.value, None);
        assert_eq!(completed.writable, None);

        let full_data = PropertyDescriptor {
            value: Some(Value::int32(9)),
            writable: Some(false),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        };
        let completed = complete_property_descriptor(full_data);
        assert_eq!(completed.value, Some(Value::int32(9)));
        assert_eq!(completed.writable, Some(false));
        assert_eq!(completed.enumerable, Some(true));
        assert_eq!(completed.configurable, Some(true));
        assert_eq!(completed.getter, None);
        assert_eq!(completed.setter, None);
    }

    #[test]
    fn complete_empty_descriptor_becomes_default_data_descriptor() {
        let completed = complete_property_descriptor(PropertyDescriptor::default());
        assert_eq!(completed.value, Some(Value::UNDEFINED));
        assert_eq!(completed.writable, Some(false));
        assert_eq!(completed.enumerable, Some(false));
        assert_eq!(completed.configurable, Some(false));
        assert_eq!(completed.getter, None);
        assert_eq!(completed.setter, None);
    }
}
