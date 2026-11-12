//! Bytecode ISA gap closures (E1.1): append-only opcodes 52..=59.
//!
//! Existing opcodes `0..=51` keep their crate-root [`crate::Instruction`] wire
//! tags. This module owns every later tag: operand layout, canonical LEB128
//! encoding, and the reads/writes/successors each opcode contributes to the
//! crate-root dataflow and CFG passes. No version byte is added; unknown tags
//! stay [`crate::DecodeErrorKind::InvalidOpcode`].
//!
//! # Derivation
//!
//! Every opcode here closes a defect read at a live lowering callsite in
//! `crates/bamts-compiler/src/lower.rs`. Nothing is inferred from a name.
//!
//! | Tag | Opcode | Callsite defect |
//! |-----|--------|-----------------|
//! | 52 | `GetSuper` | `lower_callee` lowers `super.m()` to `GetProperty` on the receiver, so lookup starts at `this` instead of the home object's prototype |
//! | 53 | `SetSuper` | `assign_target` reaches `Expression::Super` and fails `UnsupportedConstruct::InvalidSuper`, so `super.x = v` cannot lower |
//! | 54 | `ImportAttributes` | `lower_import` never reads `ImportDeclaration::attributes` |
//! | 55 | `ImportDynamicAttributes` | `lower_import_expression` evaluates `ImportExpression::options` then discards it |
//! | 56 | `CopyDataProperties` | `rest_object` emits `ObjectSpread` + per-key `DeleteProperty`, which invokes an excluded key's getter a second time |
//! | 57 | `GetTemplateObject` | `lower_tagged_template` rebuilds the strings array per evaluation and installs `raw` with `SetProperty` (enumerable, writable) |
//! | 58 | `RequireGlobalBinding` | strict `x = v` guarded the write with `LoadGlobal`, which runs a global accessor's getter before the setter |
//! | 59 | `ThrowIntrinsicError` | `throw_error_message` loaded the mutable global `TypeError`/`ReferenceError` and constructed it, so guest code that replaced the global chose what a language error threw |
//!
//! Candidates deliberately **not** added, because no callsite proves them:
//! private brand install/check, private `in`, direct `eval`, a home-object
//! load, and a prototype getter. `super[key]` takes its home object from a
//! register the class lowering already materializes, so no ambient
//! home-object opcode is required.
//!
//! # Division of labour with the crate root
//!
//! This module reports *per-opcode* facts only. The crate root owns every
//! function-level pass: the definite-initialization fixpoint, the
//! [`crate::Certificate`] it produces, handler contribution, and the
//! reachable-fall-off check. Those passes cover these opcodes by calling
//! [`Instruction::visit_reads`], [`Instruction::visit_writes`], and
//! [`Instruction::visit_successors`], so nothing here re-implements them.

use crate::{ConstantId, DecodeError, DecodeErrorKind, IntrinsicErrorKind, Pc, Register};

/// First append-only tag. Tags `0..=51` remain the crate-root algebra.
pub const FIRST_EXTENSION_TAG: u8 = 52;
/// Exclusive end of the extension tag range (`52..=59`).
pub const EXTENSION_TAG_END: u8 = 60;

/// Append-only production opcodes closing callsite-proven ISA gaps.
///
/// Tags are stable. Field order on the wire is struct-field order, each
/// integer a canonical unsigned LEB128 `u32`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Instruction {
    /// `dst = home.[[Prototype]][key]`, invoked with `receiver` as `this`.
    ///
    /// Wire tag 52. `GetProperty` on the receiver is not a substitute: the
    /// lookup object is `[[GetPrototypeOf]](home)` while the getter still
    /// receives `receiver`, so an override on the receiver must not win.
    GetSuper {
        dst: Register,
        home: Register,
        receiver: Register,
        key: Register,
    },
    /// `home.[[Prototype]][key] = value`, invoked with `receiver` as `this`.
    ///
    /// Wire tag 53. A setter found on the prototype chain runs with
    /// `receiver`, and a successful ordinary write defines the property on
    /// `receiver`, not on `home`.
    SetSuper {
        home: Register,
        receiver: Register,
        key: Register,
        value: Register,
    },
    /// Static `import … from specifier with attributes`.
    ///
    /// Wire tag 54. `specifier` is a string constant, exactly as
    /// [`crate::Instruction::Import`] tag 33 takes it; `attributes` is the
    /// attributes object. A separate opcode, not a new field on tag 33, keeps
    /// the existing import encoding byte-identical.
    ImportAttributes {
        dst: Register,
        specifier: ConstantId,
        attributes: Register,
    },
    /// `import(specifier, attributes)` — dynamic import with an options object.
    ///
    /// Wire tag 55. Tag 43 (`ImportDynamic`) stays two-operand; this opcode
    /// carries the options register that lowering currently evaluates for its
    /// side effects and then drops.
    ImportDynamicAttributes {
        dst: Register,
        specifier: Register,
        attributes: Register,
    },
    /// Copy the own enumerable properties of `source` onto `target`, skipping
    /// every key present in the `excluded` array (object rest).
    ///
    /// Wire tag 56. `ObjectSpread` followed by `DeleteProperty` is not a
    /// substitute: spread reads the excluded keys, so an accessor among them
    /// runs a second time, and the delete is observable on a proxy target.
    /// `target` is mutated in place and must already hold an object, so it is
    /// a read here exactly as it is for [`crate::Instruction::ObjectSpread`].
    CopyDataProperties {
        target: Register,
        source: Register,
        excluded: Register,
    },
    /// Load the interned, frozen template object for one tagged-template site.
    ///
    /// Wire tag 57. `cooked` and `raw` are arrays of string parts; `dst`
    /// receives the site's unique frozen object carrying `raw` as a
    /// non-enumerable, non-writable own property. Rebuilding the arrays per
    /// evaluation is not a substitute: every evaluation of one site must
    /// observe the same object.
    GetTemplateObject {
        dst: Register,
        cooked: Register,
        raw: Register,
    },
    /// Require the global name to be bound without reading its value.
    ///
    /// Wire tag 58. Strict-mode `PutValue` on an unresolvable reference throws
    /// a `ReferenceError`, but the guard it replaces (`LoadGlobal`) also ran
    /// the getter of a global accessor before `StoreGlobal` ran the setter.
    /// This opcode performs the existence check only: the declarative global
    /// record (`let`/`const`/`class` bindings) counts as bound, and
    /// `HasProperty` on the global object answers for the object record
    /// without invoking any accessor.
    RequireGlobalBinding { name: ConstantId },
    /// Throw a new error built from the realm's intrinsic `kind` constructor
    /// whose own `message` is the string constant `message`.
    ///
    /// Wire tag 59. `kind` is [`IntrinsicErrorKind::selector`]. Loading the
    /// global constructor and calling it is not a substitute: guest code can
    /// replace or delete that binding. Every abrupt completion leaves through
    /// a handler, but the verifier still sees a fall-through successor.
    ThrowIntrinsicError {
        kind: IntrinsicErrorKind,
        message: ConstantId,
    },
}

impl Instruction {
    /// Stable wire tag in `52..=59`.
    #[must_use]
    pub const fn wire_tag(self) -> u8 {
        match self {
            Self::GetSuper { .. } => 52,
            Self::SetSuper { .. } => 53,
            Self::ImportAttributes { .. } => 54,
            Self::ImportDynamicAttributes { .. } => 55,
            Self::CopyDataProperties { .. } => 56,
            Self::GetTemplateObject { .. } => 57,
            Self::RequireGlobalBinding { .. } => 58,
            Self::ThrowIntrinsicError { .. } => 59,
        }
    }

    /// Visits every register this instruction reads before executing.
    pub fn visit_reads(self, mut visit: impl FnMut(Register)) {
        match self {
            Self::GetSuper {
                home,
                receiver,
                key,
                ..
            } => {
                visit(home);
                visit(receiver);
                visit(key);
            }
            Self::SetSuper {
                home,
                receiver,
                key,
                value,
            } => {
                visit(home);
                visit(receiver);
                visit(key);
                visit(value);
            }
            Self::ImportAttributes { attributes, .. } => visit(attributes),
            Self::ImportDynamicAttributes {
                specifier,
                attributes,
                ..
            } => {
                visit(specifier);
                visit(attributes);
            }
            Self::CopyDataProperties {
                target,
                source,
                excluded,
            } => {
                visit(target);
                visit(source);
                visit(excluded);
            }
            Self::GetTemplateObject { cooked, raw, .. } => {
                visit(cooked);
                visit(raw);
            }
            Self::RequireGlobalBinding { .. } | Self::ThrowIntrinsicError { .. } => {}
        }
    }

    /// Visits each register this instruction defines.
    pub fn visit_writes(self, mut visit: impl FnMut(Register)) {
        match self {
            Self::GetSuper { dst, .. }
            | Self::ImportAttributes { dst, .. }
            | Self::ImportDynamicAttributes { dst, .. }
            | Self::GetTemplateObject { dst, .. } => visit(dst),
            Self::SetSuper { .. }
            | Self::CopyDataProperties { .. }
            | Self::RequireGlobalBinding { .. }
            | Self::ThrowIntrinsicError { .. } => {}
        }
    }

    /// Visits each normal-control successor. None of these opcodes terminate,
    /// so each has exactly one: `pc + 1`.
    pub fn visit_successors(self, pc: u32, mut visit: impl FnMut(Pc)) {
        visit(Pc::new(pc + 1));
    }

    /// Appends the canonical encoding: tag byte, then LEB128 fields.
    pub fn encode(self, output: &mut Vec<u8>) {
        output.push(self.wire_tag());
        match self {
            Self::GetSuper {
                dst,
                home,
                receiver,
                key,
            } => {
                write_u32(dst.get(), output);
                write_u32(home.get(), output);
                write_u32(receiver.get(), output);
                write_u32(key.get(), output);
            }
            Self::SetSuper {
                home,
                receiver,
                key,
                value,
            } => {
                write_u32(home.get(), output);
                write_u32(receiver.get(), output);
                write_u32(key.get(), output);
                write_u32(value.get(), output);
            }
            Self::ImportAttributes {
                dst,
                specifier,
                attributes,
            } => {
                write_u32(dst.get(), output);
                write_u32(specifier.get(), output);
                write_u32(attributes.get(), output);
            }
            Self::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            } => {
                write_u32(dst.get(), output);
                write_u32(specifier.get(), output);
                write_u32(attributes.get(), output);
            }
            Self::CopyDataProperties {
                target,
                source,
                excluded,
            } => {
                write_u32(target.get(), output);
                write_u32(source.get(), output);
                write_u32(excluded.get(), output);
            }
            Self::GetTemplateObject { dst, cooked, raw } => {
                write_u32(dst.get(), output);
                write_u32(cooked.get(), output);
                write_u32(raw.get(), output);
            }
            Self::RequireGlobalBinding { name } => {
                write_u32(name.get(), output);
            }
            Self::ThrowIntrinsicError { kind, message } => {
                write_u32(kind.selector(), output);
                write_u32(message.get(), output);
            }
        }
    }
}

/// Decodes an already-read `tag`, reading operands from `bytes` at `offset`.
///
/// This is the seam the crate-root decoder uses: it has consumed the tag byte
/// and needs only the operands. The returned offset is the first byte after
/// the instruction.
///
/// # Errors
///
/// Returns [`DecodeErrorKind::InvalidOpcode`] for a tag outside
/// `52..=59`, [`DecodeErrorKind::InvalidIntrinsicErrorKind`] for an unknown
/// error kind, or the first unexpected EOF, overlong integer, or overflowing
/// integer among the operands.
pub fn decode_from_tag(
    tag: u8,
    bytes: &[u8],
    offset: usize,
) -> Result<(Instruction, usize), DecodeError> {
    let mut cursor = Cursor { bytes, offset };
    let tag_at = offset.saturating_sub(1);
    let instruction = match tag {
        52 => Instruction::GetSuper {
            dst: Register::new(cursor.leb128()?),
            home: Register::new(cursor.leb128()?),
            receiver: Register::new(cursor.leb128()?),
            key: Register::new(cursor.leb128()?),
        },
        53 => Instruction::SetSuper {
            home: Register::new(cursor.leb128()?),
            receiver: Register::new(cursor.leb128()?),
            key: Register::new(cursor.leb128()?),
            value: Register::new(cursor.leb128()?),
        },
        54 => Instruction::ImportAttributes {
            dst: Register::new(cursor.leb128()?),
            specifier: ConstantId::new(cursor.leb128()?),
            attributes: Register::new(cursor.leb128()?),
        },
        55 => Instruction::ImportDynamicAttributes {
            dst: Register::new(cursor.leb128()?),
            specifier: Register::new(cursor.leb128()?),
            attributes: Register::new(cursor.leb128()?),
        },
        56 => Instruction::CopyDataProperties {
            target: Register::new(cursor.leb128()?),
            source: Register::new(cursor.leb128()?),
            excluded: Register::new(cursor.leb128()?),
        },
        57 => Instruction::GetTemplateObject {
            dst: Register::new(cursor.leb128()?),
            cooked: Register::new(cursor.leb128()?),
            raw: Register::new(cursor.leb128()?),
        },
        58 => Instruction::RequireGlobalBinding {
            name: ConstantId::new(cursor.leb128()?),
        },
        59 => {
            let at = cursor.offset;
            let selector = cursor.leb128()?;
            let Some(kind) = IntrinsicErrorKind::from_selector(selector) else {
                return Err(DecodeError {
                    offset: at,
                    kind: DecodeErrorKind::InvalidIntrinsicErrorKind { selector },
                });
            };
            Instruction::ThrowIntrinsicError {
                kind,
                message: ConstantId::new(cursor.leb128()?),
            }
        }
        opcode => {
            return Err(DecodeError {
                offset: tag_at,
                kind: DecodeErrorKind::InvalidOpcode { opcode },
            });
        }
    };
    Ok((instruction, cursor.offset))
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl Cursor<'_> {
    fn byte(&mut self) -> Result<u8, DecodeError> {
        let Some(byte) = self.bytes.get(self.offset).copied() else {
            return Err(DecodeError {
                offset: self.offset,
                kind: DecodeErrorKind::UnexpectedEof,
            });
        };
        self.offset += 1;
        Ok(byte)
    }

    /// Reads one canonical unsigned LEB128 `u32`, matching the crate-root
    /// decoder byte for byte: EOF mid-integer, overlong (trailing-zero)
    /// encodings, and values exceeding 32 bits are all rejected.
    fn leb128(&mut self) -> Result<u32, DecodeError> {
        let start = self.offset;
        let mut result: u32 = 0;
        let mut shift: u32 = 0;
        loop {
            let byte = self.byte()?;
            if shift == 28 {
                if byte & 0x80 != 0 || byte > 0x0f {
                    return Err(DecodeError {
                        offset: start,
                        kind: DecodeErrorKind::IntegerOverflow,
                    });
                }
                if byte == 0 {
                    return Err(DecodeError {
                        offset: start,
                        kind: DecodeErrorKind::NonCanonicalInteger,
                    });
                }
                return Ok(result | (u32::from(byte) << 28));
            }
            result |= u32::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                if byte == 0 && self.offset - start > 1 {
                    return Err(DecodeError {
                        offset: start,
                        kind: DecodeErrorKind::NonCanonicalInteger,
                    });
                }
                return Ok(result);
            }
            shift += 7;
        }
    }
}

fn write_u32(value: u32, output: &mut Vec<u8>) {
    let mut remaining = value;
    loop {
        let byte = (remaining & 0x7f) as u8;
        remaining >>= 7;
        if remaining == 0 {
            output.push(byte);
            return;
        }
        output.push(byte | 0x80);
    }
}

#[cfg(test)]
mod tests {
    use super::{EXTENSION_TAG_END, FIRST_EXTENSION_TAG, Instruction, decode_from_tag};
    use crate::{ConstantId, DecodeErrorKind, IntrinsicErrorKind, Pc, Register};

    fn catalog() -> [Instruction; 8] {
        [
            Instruction::GetSuper {
                dst: Register::new(1),
                home: Register::new(2),
                receiver: Register::new(3),
                key: Register::new(4),
            },
            Instruction::SetSuper {
                home: Register::new(5),
                receiver: Register::new(6),
                key: Register::new(7),
                value: Register::new(8),
            },
            Instruction::ImportAttributes {
                dst: Register::new(9),
                specifier: ConstantId::new(10),
                attributes: Register::new(11),
            },
            Instruction::ImportDynamicAttributes {
                dst: Register::new(12),
                specifier: Register::new(13),
                attributes: Register::new(14),
            },
            Instruction::CopyDataProperties {
                target: Register::new(15),
                source: Register::new(16),
                excluded: Register::new(17),
            },
            Instruction::GetTemplateObject {
                dst: Register::new(18),
                cooked: Register::new(19),
                raw: Register::new(20),
            },
            Instruction::RequireGlobalBinding {
                name: ConstantId::new(21),
            },
            Instruction::ThrowIntrinsicError {
                kind: IntrinsicErrorKind::SyntaxError,
                message: ConstantId::new(22),
            },
        ]
    }

    /// Decodes a full encoding the way the crate-root decoder does: it has
    /// already consumed the tag byte, so operands start at offset 1.
    fn decode_encoding(bytes: &[u8]) -> Result<(Instruction, usize), crate::DecodeError> {
        decode_from_tag(bytes[0], bytes, 1)
    }

    #[test]
    fn extension_tags_are_append_only_and_dense() {
        assert_eq!(FIRST_EXTENSION_TAG, 52, "tags 0..=51 stay crate-root");
        assert_eq!(EXTENSION_TAG_END, 60);
        let catalog = catalog();
        assert_eq!(
            (EXTENSION_TAG_END - FIRST_EXTENSION_TAG) as usize,
            catalog.len(),
            "the tag range the root decoder dispatches on must be exactly covered"
        );
        for (index, instruction) in catalog.into_iter().enumerate() {
            let tag = FIRST_EXTENSION_TAG + index as u8;
            assert_eq!(instruction.wire_tag(), tag, "tag is its catalog index");
        }
    }

    #[test]
    fn every_extension_opcode_round_trips_on_the_wire() {
        for instruction in catalog() {
            let mut bytes = Vec::new();
            instruction.encode(&mut bytes);
            assert_eq!(bytes.first().copied(), Some(instruction.wire_tag()));
            let (decoded, end) = decode_encoding(&bytes).expect("extension opcode decodes");
            assert_eq!(decoded, instruction);
            assert_eq!(end, bytes.len(), "decode consumes exactly the encoding");
        }
    }

    #[test]
    fn encoding_is_deterministic_and_operand_ordered() {
        let instruction = Instruction::GetSuper {
            dst: Register::new(1),
            home: Register::new(2),
            receiver: Register::new(3),
            key: Register::new(4),
        };
        let mut first = Vec::new();
        let mut second = Vec::new();
        instruction.encode(&mut first);
        instruction.encode(&mut second);
        assert_eq!(first, second);
        assert_eq!(first, vec![52, 1, 2, 3, 4], "dst, home, receiver, key");
    }

    #[test]
    fn decode_rejects_pre_extension_and_unknown_tags() {
        for tag in [0_u8, 51, 60, 64, 255] {
            let error = decode_encoding(&[tag, 0, 0, 0]).expect_err("only 52..=59 decode here");
            assert_eq!(error.kind, DecodeErrorKind::InvalidOpcode { opcode: tag });
            assert_eq!(error.offset, 0, "error points at the tag byte");
        }
    }

    #[test]
    fn decode_rejects_truncated_operands() {
        assert!(decode_encoding(&[52]).is_err(), "no operands");
        assert!(
            decode_encoding(&[52, 1, 2, 3]).is_err(),
            "three of four operands"
        );
        assert!(decode_encoding(&[54, 1]).is_err());
        assert!(decode_encoding(&[57, 1, 2]).is_err());
        assert!(decode_encoding(&[59, 1]).is_err());
    }

    #[test]
    fn decode_rejects_an_unknown_intrinsic_error_kind() {
        let error = decode_encoding(&[59, 4, 0]).expect_err("selector 4 names no kind");
        assert_eq!(
            error.kind,
            DecodeErrorKind::InvalidIntrinsicErrorKind { selector: 4 }
        );
        assert_eq!(error.offset, 1, "error points at the kind operand");
    }

    #[test]
    fn decode_rejects_non_canonical_leb128() {
        let error = decode_encoding(&[54, 0x80, 0x00, 0, 0]).expect_err("overlong zero");
        assert_eq!(error.kind, DecodeErrorKind::NonCanonicalInteger);
    }

    #[test]
    fn decode_rejects_leb128_overflow() {
        let error = decode_encoding(&[54, 0x80, 0x80, 0x80, 0x80, 0x10])
            .expect_err("five-byte operand exceeds u32");
        assert_eq!(error.kind, DecodeErrorKind::IntegerOverflow);
    }

    #[test]
    fn super_ops_read_home_receiver_and_key_separately() {
        let get = Instruction::GetSuper {
            dst: Register::new(0),
            home: Register::new(1),
            receiver: Register::new(2),
            key: Register::new(3),
        };
        let mut reads = Vec::new();
        get.visit_reads(|register| reads.push(register.get()));
        assert_eq!(reads, vec![1, 2, 3], "receiver is distinct from home");
        let mut writes = Vec::new();
        get.visit_writes(|register| writes.push(register.get()));
        assert_eq!(writes, vec![0]);

        let set = Instruction::SetSuper {
            home: Register::new(1),
            receiver: Register::new(2),
            key: Register::new(3),
            value: Register::new(4),
        };
        let mut set_reads = Vec::new();
        set.visit_reads(|register| set_reads.push(register.get()));
        assert_eq!(set_reads, vec![1, 2, 3, 4]);
        let mut set_writes = 0_u32;
        set.visit_writes(|_| set_writes += 1);
        assert_eq!(set_writes, 0, "SetSuper defines no register");
    }

    #[test]
    fn copy_data_properties_reads_target_in_place_and_defines_nothing() {
        let instruction = Instruction::CopyDataProperties {
            target: Register::new(0),
            source: Register::new(1),
            excluded: Register::new(2),
        };
        let mut reads = Vec::new();
        instruction.visit_reads(|register| reads.push(register.get()));
        assert_eq!(reads, vec![0, 1, 2], "target must already hold an object");
        let mut writes = 0_u32;
        instruction.visit_writes(|_| writes += 1);
        assert_eq!(writes, 0, "matches ObjectSpread's in-place convention");
    }

    #[test]
    fn import_attributes_reads_only_the_attributes_register() {
        let instruction = Instruction::ImportAttributes {
            dst: Register::new(0),
            specifier: ConstantId::new(4),
            attributes: Register::new(1),
        };
        let mut reads = Vec::new();
        instruction.visit_reads(|register| reads.push(register.get()));
        assert_eq!(reads, vec![1], "specifier is a constant, not a register");

        let dynamic = Instruction::ImportDynamicAttributes {
            dst: Register::new(0),
            specifier: Register::new(1),
            attributes: Register::new(2),
        };
        let mut dynamic_reads = Vec::new();
        dynamic.visit_reads(|register| dynamic_reads.push(register.get()));
        assert_eq!(dynamic_reads, vec![1, 2], "dynamic specifier is a register");
    }

    #[test]
    fn every_opcode_writes_at_most_one_register() {
        for instruction in catalog() {
            let mut writes = 0_u32;
            instruction.visit_writes(|_| writes += 1);
            assert!(
                writes <= 1,
                "the root fixpoint assumes no two-write extension opcode: {instruction:?}"
            );
        }
    }

    #[test]
    fn successor_is_always_fall_through() {
        for instruction in catalog() {
            let mut successors = Vec::new();
            instruction.visit_successors(41, |pc| successors.push(pc));
            assert_eq!(
                successors,
                vec![Pc::new(42)],
                "no gap opcode terminates or branches"
            );
        }
    }
}
