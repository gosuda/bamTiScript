use super::*;

#[test]
fn format_number_truth_table() {
    let cases = [
        (0.1 + 0.2, "0.30000000000000004"),
        (1e21, "1e+21"),
        (-0.0, "0"),
        (1.0 / 3.0, "0.3333333333333333"),
        (1e-6, "0.000001"),
        (1e-7, "1e-7"),
        (9_007_199_254_740_991.0, "9007199254740991"),
        (f64::NAN, "NaN"),
        (f64::INFINITY, "Infinity"),
        (f64::NEG_INFINITY, "-Infinity"),
        (9_007_199_254_740_992.0, "9007199254740992"),
        (1e20, "100000000000000000000"),
    ];
    for (number, expected) in cases {
        assert_eq!(format_number(number), expected);
    }
}

fn flags() -> FunctionFlags {
    FunctionFlags::default()
}

fn prefix() -> Vec<u8> {
    let mut bytes = MAGIC.to_vec();
    bytes.push(FORMAT_VERSION);
    bytes
}

/// A single function exercising the dynamic-computation opcodes, all
/// references in bounds and every read dominated by a write. Register map:
///
/// * r0 = 21, r1 = 1.5, r2 = r0 + r1, r3 = -r2
/// * r4 = {}, r5 = "main" (used as a register property key)
/// * r6 = r4[r5]; r7 = [] then push/extend
/// * r9 = {}; object-spread and set-prototype from r4
/// * r10 = closure(fn0, captures=r7)
/// * r11/r12/r13 = this / arguments / new.target
/// * r14 = global g; store it back; r15 = typeof g
/// * r16 = #p private name; r17 = /ab/gi
/// * r18 = iterator(r7); (r19,r20) = next(r18)
/// * r21 = call(r10, this=r4, args=r7); r22 = construct(r10, args=r7)
/// * r23 = import "./dep"; export "x" = r23; suspend yields r22, resumes r24
/// * handler over [0,34) catches into r25
fn rich_module() -> Module<Unverified> {
    let constants = vec![
        Constant::String(EcmaString::encode("main")), // 0: function name + key string
        Constant::Int32(21),                          // 1
        Constant::Number(NumberBits::from_f64(1.5)),  // 2
        Constant::BigInt(BigIntLiteral::new("-1234567890123".to_owned()).unwrap()), // 3
        Constant::Boolean(true),                      // 4
        Constant::Null,                               // 5
        Constant::Undefined,                          // 6
        Constant::String(EcmaString::encode("./dep")), // 7: import specifier
        Constant::String(EcmaString::encode("g")),    // 8: global name
        Constant::String(EcmaString::encode("#p")),   // 9: private description
        Constant::String(EcmaString::encode("ab")),   // 10: regexp pattern
        Constant::String(EcmaString::encode("gi")),   // 11: regexp flags
        Constant::String(EcmaString::encode("x")),    // 12: export name
    ];
    let code = vec![
        Instruction::LoadConst {
            dst: Register::new(0),
            constant: ConstantId::new(1),
        },
        Instruction::LoadConst {
            dst: Register::new(1),
            constant: ConstantId::new(2),
        },
        Instruction::Binary {
            dst: Register::new(2),
            op: BinaryOp::Add,
            left: Register::new(0),
            right: Register::new(1),
        },
        Instruction::Unary {
            dst: Register::new(3),
            op: UnaryOp::Negate,
            operand: Register::new(2),
        },
        Instruction::CreateObject {
            dst: Register::new(4),
        },
        Instruction::LoadConst {
            dst: Register::new(5),
            constant: ConstantId::new(0),
        },
        Instruction::SetProperty {
            object: Register::new(4),
            key: Register::new(5),
            value: Register::new(3),
        },
        Instruction::GetProperty {
            dst: Register::new(6),
            object: Register::new(4),
            key: Register::new(5),
        },
        Instruction::CreateArray {
            dst: Register::new(7),
        },
        Instruction::ArrayPush {
            array: Register::new(7),
            value: Register::new(6),
        },
        Instruction::ArrayExtend {
            array: Register::new(7),
            iterable: Register::new(7),
        },
        Instruction::CreateObject {
            dst: Register::new(9),
        },
        Instruction::ObjectSpread {
            target: Register::new(9),
            source: Register::new(4),
        },
        Instruction::SetPrototype {
            object: Register::new(9),
            prototype: Register::new(4),
        },
        Instruction::CreateClosure {
            dst: Register::new(10),
            function: FunctionId::new(0),
            captures: Register::new(7),
        },
        Instruction::LoadThis {
            dst: Register::new(11),
        },
        Instruction::LoadArguments {
            dst: Register::new(12),
        },
        Instruction::LoadNewTarget {
            dst: Register::new(13),
        },
        Instruction::LoadGlobal {
            dst: Register::new(14),
            name: ConstantId::new(8),
        },
        Instruction::StoreGlobal {
            name: ConstantId::new(8),
            value: Register::new(14),
        },
        Instruction::TypeOfGlobal {
            dst: Register::new(15),
            name: ConstantId::new(8),
        },
        Instruction::CreatePrivateName {
            dst: Register::new(16),
            description: ConstantId::new(9),
        },
        Instruction::CreateRegExp {
            dst: Register::new(17),
            pattern: ConstantId::new(10),
            flags: ConstantId::new(11),
        },
        Instruction::GetIterator {
            dst: Register::new(18),
            src: Register::new(7),
            kind: IteratorKind::Sync,
        },
        Instruction::IteratorNext {
            done: Register::new(19),
            value: Register::new(20),
            iterator: Register::new(18),
        },
        Instruction::DefineAccessor {
            object: Register::new(9),
            key: Register::new(5),
            accessor: Register::new(10),
            kind: AccessorKind::Getter,
        },
        Instruction::Call {
            dst: Register::new(21),
            callee: Register::new(10),
            this_value: Register::new(4),
            arguments: Register::new(7),
        },
        Instruction::Construct {
            dst: Register::new(22),
            callee: Register::new(10),
            arguments: Register::new(7),
        },
        Instruction::Import {
            dst: Register::new(23),
            specifier: ConstantId::new(7),
        },
        Instruction::Export {
            name: ConstantId::new(12),
            src: Register::new(23),
        },
        Instruction::Suspend {
            dst: Register::new(24),
            src: Register::new(22),
            resume: Pc::new(31),
            mode: Register::new(25),
        },
        Instruction::JumpIfTrue {
            condition: Register::new(21),
            target: Pc::new(33),
        },
        Instruction::Return {
            value: Register::new(6),
        },
        Instruction::Return {
            value: Register::new(24),
        },
        Instruction::Return {
            value: Register::new(25),
        },
    ];
    let handlers = vec![ExceptionHandler {
        start: Pc::new(0),
        end: Pc::new(34),
        handler: Pc::new(34),
        catch_register: Register::new(25),
    }];
    Module::new(
        constants,
        vec![Function::new(
            Some(ConstantId::new(0)),
            0,
            0,
            26,
            FunctionFlags {
                is_async: true,
                is_generator: false,
                is_constructable: true,
                is_sloppy: true,
                binds_at_call: true,
            },
            code,
            handlers,
        )],
        FunctionId::new(0),
    )
}

#[test]
fn rich_module_verifies_round_trips_and_is_deterministic() {
    let verified = rich_module().verify().expect("valid production module");
    let encoded = verified.encode();
    assert_eq!(verified.encode(), encoded, "encoding is deterministic");

    let decoded = decode(&encoded, &DecodeLimits::default()).expect("canonical wire");
    assert_eq!(decoded, rich_module(), "decode is the inverse of encode");
    let reverified = decoded.verify().expect("decoded module reverifies");
    assert_eq!(reverified.encode(), encoded, "round-trip is canonical");
}

/// Every opcode variant survives an encode -> decode round-trip at the
/// instruction level, independent of CFG/reference validity. This pins the
/// wire tag and field order for all opcodes.
#[test]
fn every_opcode_round_trips_on_the_wire() {
    let instructions = [
        Instruction::LoadConst {
            dst: Register::new(1),
            constant: ConstantId::new(2),
        },
        Instruction::Move {
            dst: Register::new(3),
            src: Register::new(4),
        },
        Instruction::Unary {
            dst: Register::new(5),
            op: UnaryOp::LogicalNot,
            operand: Register::new(6),
        },
        Instruction::Binary {
            dst: Register::new(7),
            op: BinaryOp::StrictEqual,
            left: Register::new(8),
            right: Register::new(9),
        },
        Instruction::CreateObject {
            dst: Register::new(10),
        },
        Instruction::CreateArray {
            dst: Register::new(11),
        },
        Instruction::CreateClosure {
            dst: Register::new(12),
            function: FunctionId::new(13),
            captures: Register::new(14),
        },
        Instruction::GetProperty {
            dst: Register::new(15),
            object: Register::new(16),
            key: Register::new(17),
        },
        Instruction::SetProperty {
            object: Register::new(18),
            key: Register::new(19),
            value: Register::new(20),
        },
        Instruction::DeleteProperty {
            dst: Register::new(21),
            object: Register::new(22),
            key: Register::new(23),
        },
        Instruction::DefineAccessor {
            object: Register::new(24),
            key: Register::new(25),
            accessor: Register::new(26),
            kind: AccessorKind::Setter,
        },
        Instruction::Call {
            dst: Register::new(27),
            callee: Register::new(28),
            this_value: Register::new(29),
            arguments: Register::new(30),
        },
        Instruction::Construct {
            dst: Register::new(31),
            callee: Register::new(32),
            arguments: Register::new(33),
        },
        Instruction::LoadGlobal {
            dst: Register::new(34),
            name: ConstantId::new(35),
        },
        Instruction::StoreGlobal {
            name: ConstantId::new(36),
            value: Register::new(37),
        },
        Instruction::TypeOfGlobal {
            dst: Register::new(38),
            name: ConstantId::new(39),
        },
        Instruction::LoadThis {
            dst: Register::new(40),
        },
        Instruction::LoadArguments {
            dst: Register::new(41),
        },
        Instruction::LoadNewTarget {
            dst: Register::new(42),
        },
        Instruction::ArrayPush {
            array: Register::new(43),
            value: Register::new(44),
        },
        Instruction::ArrayExtend {
            array: Register::new(45),
            iterable: Register::new(46),
        },
        Instruction::ObjectSpread {
            target: Register::new(47),
            source: Register::new(48),
        },
        Instruction::SetPrototype {
            object: Register::new(49),
            prototype: Register::new(50),
        },
        Instruction::CreatePrivateName {
            dst: Register::new(51),
            description: ConstantId::new(52),
        },
        Instruction::CreateRegExp {
            dst: Register::new(53),
            pattern: ConstantId::new(54),
            flags: ConstantId::new(55),
        },
        Instruction::GetIterator {
            dst: Register::new(56),
            src: Register::new(57),
            kind: IteratorKind::Async,
        },
        Instruction::IteratorNext {
            done: Register::new(58),
            value: Register::new(59),
            iterator: Register::new(60),
        },
        Instruction::Jump {
            target: Pc::new(61),
        },
        Instruction::JumpIfTrue {
            condition: Register::new(62),
            target: Pc::new(63),
        },
        Instruction::JumpIfFalse {
            condition: Register::new(64),
            target: Pc::new(65),
        },
        Instruction::Return {
            value: Register::new(66),
        },
        Instruction::Throw {
            value: Register::new(67),
        },
        Instruction::Suspend {
            dst: Register::new(68),
            src: Register::new(69),
            resume: Pc::new(70),
            mode: Register::new(71),
        },
        Instruction::Import {
            dst: Register::new(71),
            specifier: ConstantId::new(72),
        },
        Instruction::Export {
            name: ConstantId::new(73),
            src: Register::new(74),
        },
        Instruction::Halt,
        Instruction::CreateCell {
            dst: Register::new(75),
        },
        Instruction::Await {
            dst: Register::new(76),
            src: Register::new(77),
            resume: Pc::new(78),
        },
        Instruction::IteratorStep {
            dst: Register::new(79),
            iterator: Register::new(80),
        },
        Instruction::IteratorResult {
            done: Register::new(81),
            value: Register::new(82),
            result: Register::new(83),
        },
        Instruction::IteratorClose {
            result: Register::new(84),
            called: Register::new(85),
            iterator: Register::new(86),
            mode: IteratorCloseMode::PreserveAbrupt,
        },
        Instruction::RequireCloseResult {
            result: Register::new(87),
            called: Register::new(88),
        },
        Instruction::ToObject {
            dst: Register::new(89),
            src: Register::new(90),
        },
        Instruction::ImportDynamic {
            dst: Register::new(91),
            specifier: Register::new(92),
        },
        Instruction::LoadImportMeta {
            dst: Register::new(93),
        },
        Instruction::DisposeCapture {
            method: Register::new(94),
            kind: Register::new(95),
            src: Register::new(96),
            hint: DisposeHint::Async,
        },
        Instruction::SuppressError {
            dst: Register::new(97),
            error: Register::new(98),
            suppressed: Register::new(99),
        },
        Instruction::ConstructWithNewTarget {
            dst: Register::new(100),
            callee: Register::new(101),
            new_target: Register::new(102),
            arguments: Register::new(103),
        },
        Instruction::DefineDataProperty {
            object: Register::new(104),
            key: Register::new(105),
            value: Register::new(106),
        },
        Instruction::LoadOwnDescriptorSlot {
            dst: Register::new(107),
            object: Register::new(108),
            key: Register::new(109),
            slot: DescriptorSlot::Value,
        },
        Instruction::DefineOwnDescriptorSlot {
            object: Register::new(110),
            key: Register::new(111),
            src: Register::new(112),
            slot: DescriptorSlot::Setter,
        },
        Instruction::WithHasBinding {
            dst: Register::new(113),
            object: Register::new(114),
            key: Register::new(115),
        },
    ];
    assert_eq!(instructions.len(), 52, "one case per opcode");
    let limits = DecodeLimits::default();
    for (opcode, instruction) in instructions.into_iter().enumerate() {
        let mut bytes = Vec::new();
        encode_instruction(instruction, &mut bytes);
        assert_eq!(
            bytes.first().copied(),
            Some(opcode as u8),
            "opcode tag is its table index"
        );
        let mut decoder = Decoder {
            bytes: &bytes,
            offset: 0,
            limits: &limits,
            total_instructions: 0,
        };
        let decoded = decoder.instruction().expect("opcode decodes");
        assert_eq!(decoded, instruction, "{instruction:?} round-trips");
        assert_eq!(decoder.offset, bytes.len(), "consumes exactly its bytes");
    }
}

#[test]
fn suspend_wire_round_trip_preserves_mode() {
    let instruction = Instruction::Suspend {
        dst: Register::new(1),
        src: Register::new(2),
        resume: Pc::new(3),
        mode: Register::new(4),
    };
    let mut bytes = Vec::new();
    encode_instruction(instruction, &mut bytes);
    assert_eq!(bytes, vec![32, 1, 2, 3, 4]);
    let limits = DecodeLimits::default();
    let mut decoder = Decoder {
        bytes: &bytes,
        offset: 0,
        limits: &limits,
        total_instructions: 0,
    };
    assert_eq!(decoder.instruction().expect("Suspend decodes"), instruction);
    assert_eq!(decoder.offset, bytes.len());
}

#[test]
fn minimal_module_has_exact_canonical_wire() {
    let module = Module::new(
        vec![Constant::Int32(7)],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::Return {
                    value: Register::new(0),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    let encoded = module.verify().expect("valid").encode();
    let mut expected = prefix();
    expected.extend_from_slice(&[
        1, // constant count
        1, 7, 0, 0, 0, // Int32(7)
        1, // function count
        0, // entry
        0, // name none
        0, // capture count
        0, // parameter count
        1, // register count
        0, // flags
        2, // code length
        0, 0, 0, // LoadConst dst0 const0
        30, 0, // Return value0
        0, // handler count
    ]);
    assert_eq!(encoded, expected);
}

#[test]
fn fields_beyond_127_scale_and_round_trip() {
    // 200 constants, 200 registers, 200 instructions -> multi-byte LEB128.
    let constant_count: u32 = 200;
    let mut constants = Vec::new();
    for value in 0..constant_count {
        constants.push(Constant::Int32(value as i32));
    }
    let register_count: u32 = 200;
    let mut code = Vec::new();
    for register in 0..register_count {
        code.push(Instruction::LoadConst {
            dst: Register::new(register),
            constant: ConstantId::new(register % constant_count),
        });
    }
    code.push(Instruction::Return {
        value: Register::new(register_count - 1),
    });
    let module = Module::new(
        constants,
        vec![Function::new(
            None,
            0,
            0,
            register_count,
            flags(),
            code,
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    let verified = module.clone().verify().expect("large module verifies");
    let encoded = verified.encode();
    // 200 needs two LEB128 bytes; confirm the multi-byte path is exercised.
    assert!(
        (0..encoded.len().saturating_sub(1)).any(|i| encoded[i] == 0xc8 && encoded[i + 1] == 0x01),
        "constant count 200 must use a two-byte LEB128 group"
    );
    let decoded = decode(&encoded, &DecodeLimits::default()).expect("round trip");
    assert_eq!(decoded, module);
    assert_eq!(decoded.verify().expect("reverify").encode(), encoded,);
}

/// A call whose arguments array holds far more than the old 127/fixed-window
/// ceiling: a single arguments register, no window, no arg-count field.
#[test]
fn calls_scale_past_fixed_window_via_arguments_array() {
    let mut code = vec![
        Instruction::CreateObject {
            dst: Register::new(0),
        }, // callee stand-in
        Instruction::CreateObject {
            dst: Register::new(1),
        }, // this
        Instruction::CreateArray {
            dst: Register::new(2),
        }, // arguments array
    ];
    // Push 500 elements into the arguments array: arity is unbounded by the
    // ISA shape, limited only by structural register/instruction ceilings.
    for _ in 0..500 {
        code.push(Instruction::ArrayPush {
            array: Register::new(2),
            value: Register::new(1),
        });
    }
    code.push(Instruction::Call {
        dst: Register::new(3),
        callee: Register::new(0),
        this_value: Register::new(1),
        arguments: Register::new(2),
    });
    code.push(Instruction::Return {
        value: Register::new(3),
    });
    let module = Module::new(
        vec![],
        vec![Function::new(None, 0, 0, 4, flags(), code, vec![])],
        FunctionId::new(0),
    );
    let verified = module.clone().verify().expect("variadic call verifies");
    assert_eq!(
        decode(&verified.encode(), &DecodeLimits::default())
            .expect("round trip")
            .verify()
            .expect("reverify")
            .encode(),
        verified.encode()
    );
}

fn decode_leb(bytes: &[u8]) -> Result<u32, DecodeError> {
    let limits = DecodeLimits::default();
    let mut decoder = Decoder {
        bytes,
        offset: 0,
        limits: &limits,
        total_instructions: 0,
    };
    decoder.leb128()
}

#[test]
fn leb128_accepts_only_canonical_encodings() {
    assert_eq!(decode_leb(&[0]), Ok(0));
    assert_eq!(decode_leb(&[1]), Ok(1));
    assert_eq!(decode_leb(&[127]), Ok(127));
    assert_eq!(decode_leb(&[0xc8, 0x01]), Ok(200));
    assert_eq!(decode_leb(&[0xff, 0xff, 0xff, 0xff, 0x0f]), Ok(u32::MAX));

    // Overlong single zero group.
    assert_eq!(
        decode_leb(&[0x80, 0x00]),
        Err(DecodeError {
            offset: 0,
            kind: DecodeErrorKind::NonCanonicalInteger,
        })
    );
    // Overlong nonzero value.
    assert_eq!(
        decode_leb(&[0x81, 0x00]),
        Err(DecodeError {
            offset: 0,
            kind: DecodeErrorKind::NonCanonicalInteger,
        })
    );
    // Truncated mid-integer: EOF is reported where the missing
    // continuation byte belongs (offset 1, after consuming 0x80).
    assert_eq!(
        decode_leb(&[0x80]),
        Err(DecodeError {
            offset: 1,
            kind: DecodeErrorKind::UnexpectedEof,
        })
    );
    // Overflow beyond 32 bits (sixth group / high bits on fifth group).
    assert_eq!(
        decode_leb(&[0xff, 0xff, 0xff, 0xff, 0x1f]),
        Err(DecodeError {
            offset: 0,
            kind: DecodeErrorKind::IntegerOverflow,
        })
    );
    assert_eq!(
        decode_leb(&[0x80, 0x80, 0x80, 0x80, 0x80]),
        Err(DecodeError {
            offset: 0,
            kind: DecodeErrorKind::IntegerOverflow,
        })
    );
}

#[test]
fn decode_errors_report_the_first_bad_byte() {
    let mut bytes = prefix();
    bytes[3] ^= 1;
    assert_eq!(
        decode(&bytes, &DecodeLimits::default()),
        Err(DecodeError {
            offset: 3,
            kind: DecodeErrorKind::BadMagic {
                expected: MAGIC[3],
                actual: bytes[3],
            },
        })
    );
    assert_eq!(
        decode(&MAGIC[..4], &DecodeLimits::default()),
        Err(DecodeError {
            offset: 4,
            kind: DecodeErrorKind::UnexpectedEof,
        })
    );
    let mut bad_version = MAGIC.to_vec();
    bad_version.push(3);
    assert_eq!(
        decode(&bad_version, &DecodeLimits::default()),
        Err(DecodeError {
            offset: 8,
            kind: DecodeErrorKind::UnsupportedVersion { version: 3 },
        })
    );
    let mut version_four = rich_module().verify().expect("valid module").encode();
    version_four[MAGIC.len()] = 4;
    assert_eq!(
        decode(&version_four, &DecodeLimits::default()),
        Err(DecodeError {
            offset: 8,
            kind: DecodeErrorKind::UnsupportedVersion { version: 4 },
        }),
        "v4 artifacts are rejected after the Suspend wire grows"
    );
}

#[test]
fn truncated_string_reports_payload_start() {
    let mut bytes = prefix();
    bytes.extend_from_slice(&[1, 2, 2, b'a', 0]);

    assert_eq!(
        decode(&bytes, &DecodeLimits::default()),
        Err(DecodeError {
            offset: 12,
            kind: DecodeErrorKind::UnexpectedEof,
        })
    );
}

#[test]
fn decoder_checks_limits_before_allocation() {
    let mut bytes = prefix();
    write_u32(200, &mut bytes); // constant count, two-byte LEB128 [0xc8, 0x01]
    let limits = DecodeLimits {
        max_constants: 128,
        ..DecodeLimits::default()
    };
    assert_eq!(
        decode(&bytes, &limits),
        Err(DecodeError {
            offset: prefix().len(),
            kind: DecodeErrorKind::LimitExceeded {
                field: "constant count",
                limit: 128,
                actual: 200,
            },
        })
    );
}

#[test]
fn decoder_rejects_invalid_bigint_utf8_without_recovery() {
    let mut bytes = prefix();
    write_u32(1, &mut bytes); // constant count
    bytes.push(7); // bigint tag
    write_u32(1, &mut bytes); // length
    bytes.push(0xff); // invalid UTF-8
    assert_eq!(
        decode(&bytes, &DecodeLimits::default()),
        Err(DecodeError {
            offset: prefix().len() + 3,
            kind: DecodeErrorKind::InvalidUtf8,
        })
    );
}

#[test]
fn decoder_rejects_truncated_string_units() {
    let mut bytes = prefix();
    write_u32(1, &mut bytes);
    bytes.push(2);
    write_u32(2, &mut bytes);
    bytes.extend_from_slice(&0xD800_u16.to_le_bytes());
    assert!(matches!(
        decode(&bytes, &DecodeLimits::default()),
        Err(DecodeError {
            kind: DecodeErrorKind::UnexpectedEof,
            ..
        })
    ));
}

#[test]
fn decoder_rejects_string_over_unit_limit() {
    let mut bytes = prefix();
    write_u32(1, &mut bytes);
    bytes.push(2);
    write_u32(3, &mut bytes);
    let limits = DecodeLimits {
        max_string_units: 2,
        ..DecodeLimits::default()
    };
    assert!(matches!(
        decode(&bytes, &limits),
        Err(DecodeError {
            kind: DecodeErrorKind::LimitExceeded {
                field: "string unit count",
                limit: 2,
                actual: 3,
            },
            ..
        })
    ));
}

#[test]
fn string_constants_round_trip_lone_surrogates() {
    let encoded = Module::new(
        vec![Constant::String(EcmaString::from_units(&[
            0xD800, 0xDC00, 0xDFFF,
        ]))],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt],
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("lone surrogates are valid literal constants")
    .encode();
    let module = decode(&encoded, &DecodeLimits::default())
        .expect("valid UTF-16 units")
        .verify()
        .expect("the decoded module verifies");
    assert!(matches!(
        module.constants(),
        [Constant::String(value)] if value.as_units() == [0xD800, 0xDC00, 0xDFFF]
    ));
    assert_eq!(module.encode(), encoded);
}

#[test]
fn decoder_rejects_noncanonical_nan_bits() {
    let mut bytes = prefix();
    write_u32(1, &mut bytes);
    bytes.push(0); // number tag
    bytes.extend_from_slice(&0x7ff0_0000_0000_0001_u64.to_le_bytes());
    assert_eq!(
        decode(&bytes, &DecodeLimits::default()),
        Err(DecodeError {
            offset: prefix().len() + 2,
            kind: DecodeErrorKind::NonCanonicalNumber {
                bits: 0x7ff0_0000_0000_0001,
            },
        })
    );
    assert_eq!(
        NumberBits::from_bits(0xfff0_0000_0000_0001).bits(),
        CANONICAL_NAN_BITS
    );
}

#[test]
fn decoder_rejects_invalid_bigint_text() {
    for text in ["007", "-0", "", "-", "1a", "+1", "00"] {
        let mut bytes = prefix();
        write_u32(1, &mut bytes);
        bytes.push(7); // bigint tag
        write_text(text, &mut bytes);
        assert!(
            matches!(
                decode(&bytes, &DecodeLimits::default()),
                Err(DecodeError {
                    kind: DecodeErrorKind::InvalidBigInt,
                    ..
                })
            ),
            "expected {text:?} to be rejected"
        );
    }
    // Canonical forms accepted.
    for text in ["0", "7", "-7", "1234567890123456789012345"] {
        assert!(BigIntLiteral::new(text.to_owned()).is_some(), "{text}");
    }
}

/// A module builder for the flags/opcode/operator hostile tests: one
/// function with `body` as its raw code bytes.
fn one_function_bytes(body: &[u8]) -> Vec<u8> {
    let mut bytes = prefix();
    write_u32(0, &mut bytes); // constants
    write_u32(1, &mut bytes); // functions
    write_u32(0, &mut bytes); // entry
    write_u32(0, &mut bytes); // name none
    write_u32(0, &mut bytes); // capture count
    write_u32(0, &mut bytes); // parameter count
    write_u32(1, &mut bytes); // register count
    bytes.push(0); // flags
    write_u32(1, &mut bytes); // code length
    bytes.extend_from_slice(body);
    bytes
}

#[test]
fn decoder_rejects_unknown_tags_flags_and_operators() {
    // Invalid constant tag.
    let mut bad_constant = prefix();
    write_u32(1, &mut bad_constant);
    bad_constant.push(200);
    assert!(matches!(
        decode(&bad_constant, &DecodeLimits::default()),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidConstantTag { tag: 200 },
            ..
        })
    ));

    // Invalid function flags (unknown bit).
    let mut bad_flags = prefix();
    write_u32(0, &mut bad_flags); // constants
    write_u32(1, &mut bad_flags); // functions
    write_u32(0, &mut bad_flags); // entry
    write_u32(0, &mut bad_flags); // name none
    write_u32(0, &mut bad_flags); // capture count
    write_u32(0, &mut bad_flags); // params
    write_u32(1, &mut bad_flags); // registers
    bad_flags.push(0b10_0000); // unknown flag bit
    assert!(matches!(
        decode(&bad_flags, &DecodeLimits::default()),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidFunctionFlags { bits: 0b10_0000 },
            ..
        })
    ));

    // Invalid opcode.
    assert!(matches!(
        decode(&one_function_bytes(&[250]), &DecodeLimits::default()),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidOpcode { opcode: 250 },
            ..
        })
    ));
    // Unary with a bad operator tag (opcode 2, dst 0, op 99, operand 0).
    assert!(matches!(
        decode(
            &one_function_bytes(&[2, 0, 99, 0]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidUnaryOp { tag: 99 },
            ..
        })
    ));
    // Binary with a bad operator tag (opcode 3, dst 0, op 99, l 0, r 0).
    assert!(matches!(
        decode(
            &one_function_bytes(&[3, 0, 99, 0, 0]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidBinaryOp { tag: 99 },
            ..
        })
    ));
    // GetIterator with a bad kind tag (opcode 25, dst 0, src 0, kind 9).
    assert!(matches!(
        decode(
            &one_function_bytes(&[25, 0, 0, 9]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidIteratorKind { tag: 9 },
            ..
        })
    ));
    // IteratorClose with a bad mode tag
    // (opcode 40, result 0, called 0, iterator 0, mode 9).
    assert!(matches!(
        decode(
            &one_function_bytes(&[40, 0, 0, 0, 9]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidIteratorCloseMode { tag: 9 },
            ..
        })
    ));
    // RequireCloseResult with a truncated called register is hostile input,
    // not an implicit default.
    assert!(decode(&one_function_bytes(&[41, 0]), &DecodeLimits::default()).is_err());
    // DisposeCapture rejects unknown hints and truncated operands.
    assert!(matches!(
        decode(
            &one_function_bytes(&[45, 0, 1, 2, 9]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidDisposeHint { tag: 9 },
            ..
        })
    ));
    assert!(decode(&one_function_bytes(&[45, 0, 1]), &DecodeLimits::default()).is_err());
    // SuppressError requires all three register operands.
    assert!(decode(&one_function_bytes(&[46, 0, 0]), &DecodeLimits::default()).is_err());
    assert!(
        decode(
            &one_function_bytes(&[47, 0, 0, 0]),
            &DecodeLimits::default()
        )
        .is_err()
    );
    assert!(decode(&one_function_bytes(&[48, 0, 0]), &DecodeLimits::default()).is_err());
    // DefineAccessor with a bad kind tag (opcode 10, obj 0, key 0, acc 0, kind 9).
    assert!(matches!(
        decode(
            &one_function_bytes(&[10, 0, 0, 0, 9]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidAccessorKind { tag: 9 },
            ..
        })
    ));
    // LoadOwnDescriptorSlot / DefineOwnDescriptorSlot reject unknown slot tags
    // and truncated operands.
    assert!(matches!(
        decode(
            &one_function_bytes(&[49, 0, 0, 0, 9]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidDescriptorSlot { tag: 9 },
            ..
        })
    ));
    assert!(matches!(
        decode(
            &one_function_bytes(&[50, 0, 0, 0, 9]),
            &DecodeLimits::default()
        ),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidDescriptorSlot { tag: 9 },
            ..
        })
    ));
    assert!(decode(&one_function_bytes(&[49, 0, 0]), &DecodeLimits::default()).is_err());
    assert!(decode(&one_function_bytes(&[50, 0, 0]), &DecodeLimits::default()).is_err());
    // WithHasBinding requires dst, object, and key.
    assert!(decode(&one_function_bytes(&[51, 0, 0]), &DecodeLimits::default()).is_err());
}

#[test]
fn decoder_rejects_trailing_bytes() {
    let mut trailing = rich_module().verify().expect("valid").encode();
    trailing.push(0);
    assert!(matches!(
        decode(&trailing, &DecodeLimits::default()),
        Err(DecodeError {
            kind: DecodeErrorKind::TrailingBytes { count: 1 },
            ..
        })
    ));
}

#[test]
fn decode_is_total_over_hostile_bytes() {
    // Every truncation of a valid module either decodes or errors, never
    // panics; and adversarial byte soup never panics.
    let valid = rich_module().verify().expect("valid").encode();
    for len in 0..=valid.len() {
        let _ = decode(&valid[..len], &DecodeLimits::default());
    }
    for seed in 0u16..=255 {
        let soup: Vec<u8> = (0..64).map(|i| (seed as u8).wrapping_mul(i + 1)).collect();
        let _ = decode(&soup, &DecodeLimits::default());
    }
}

#[test]
fn single_byte_mutations_change_decode_result() {
    let encoded = rich_module().verify().expect("valid").encode();
    let baseline = decode(&encoded, &DecodeLimits::default());
    let mut observed_difference = false;
    for index in 0..encoded.len() {
        let mut mutated = encoded.clone();
        mutated[index] = mutated[index].wrapping_add(1);
        if decode(&mutated, &DecodeLimits::default()) != baseline {
            observed_difference = true;
        }
    }
    assert!(
        observed_difference,
        "flipping bytes must be observable at the decode boundary"
    );
}

#[test]
fn verifier_rejects_empty_module_and_bad_entry() {
    assert_eq!(
        Module::new(vec![], vec![], FunctionId::new(0)).verify(),
        Err(module_error(VerifyErrorKind::EmptyModule))
    );
    let bad_entry = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            0,
            flags(),
            vec![Instruction::Halt],
            vec![],
        )],
        FunctionId::new(1),
    );
    assert!(matches!(
        bad_entry.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::EntryFunctionOutOfBounds { .. },
            ..
        })
    ));
}

#[test]
fn verifier_rejects_bad_function_metadata() {
    let empty_function = Module::new(
        vec![],
        vec![Function::new(None, 0, 0, 0, flags(), vec![], vec![])],
        FunctionId::new(0),
    );
    assert!(matches!(
        empty_function.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::EmptyFunction,
            ..
        })
    ));

    let too_many_params = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            2,
            1,
            flags(),
            vec![Instruction::Halt],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        too_many_params.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ParameterCountExceedsRegisters { .. },
            ..
        })
    ));

    // Captures plus parameters overflow the register file even though each
    // alone fits: 1 capture + 1 parameter = 2 > 1 register.
    let captures_and_params_overflow = Module::new(
        vec![],
        vec![Function::new(
            None,
            1,
            1,
            1,
            flags(),
            vec![Instruction::Halt],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        captures_and_params_overflow.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::EntryRegistersExceedRegisterCount { .. },
            ..
        })
    ));

    let bad_name = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            Some(ConstantId::new(0)),
            0,
            0,
            0,
            flags(),
            vec![Instruction::Halt],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        bad_name.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::FunctionNameNotString { .. },
            ..
        })
    ));
}

#[test]
fn verifier_rejects_out_of_bounds_references() {
    let bad_register = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::LoadConst {
                dst: Register::new(1),
                constant: ConstantId::new(0),
            }],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        bad_register.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::RegisterOutOfBounds { .. },
            ..
        })
    ));

    let bad_constant = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::LoadConst {
                dst: Register::new(0),
                constant: ConstantId::new(0),
            }],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        bad_constant.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ConstantOutOfBounds { .. },
            ..
        })
    ));

    let bad_function_ref = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![
                Instruction::CreateArray {
                    dst: Register::new(0),
                },
                Instruction::CreateClosure {
                    dst: Register::new(0),
                    function: FunctionId::new(5),
                    captures: Register::new(0),
                },
                Instruction::Return {
                    value: Register::new(0),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        bad_function_ref.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::FunctionReferenceOutOfBounds { .. },
            ..
        })
    ));
}

/// Global/private/regexp/export/import names must resolve to string
/// constants; a non-string constant is rejected.
#[test]
fn verifier_requires_string_constants_for_named_refs() {
    let cases: Vec<(&str, Instruction)> = vec![
        (
            "LoadGlobal",
            Instruction::LoadGlobal {
                dst: Register::new(0),
                name: ConstantId::new(0),
            },
        ),
        (
            "TypeOfGlobal",
            Instruction::TypeOfGlobal {
                dst: Register::new(0),
                name: ConstantId::new(0),
            },
        ),
        (
            "CreatePrivateName",
            Instruction::CreatePrivateName {
                dst: Register::new(0),
                description: ConstantId::new(0),
            },
        ),
        (
            "CreateRegExp",
            Instruction::CreateRegExp {
                dst: Register::new(0),
                pattern: ConstantId::new(0),
                flags: ConstantId::new(0),
            },
        ),
        (
            "Import",
            Instruction::Import {
                dst: Register::new(0),
                specifier: ConstantId::new(0),
            },
        ),
    ];
    for (label, instruction) in cases {
        let module = Module::new(
            vec![Constant::Int32(0)], // constant 0 is NOT a string
            vec![Function::new(
                None,
                0,
                0,
                1,
                flags(),
                vec![
                    instruction,
                    Instruction::Return {
                        value: Register::new(0),
                    },
                ],
                vec![],
            )],
            FunctionId::new(0),
        );
        assert!(
            matches!(
                module.verify(),
                Err(VerifyError {
                    kind: VerifyErrorKind::StringConstantExpected { .. },
                    ..
                })
            ),
            "{label} must require a string constant"
        );
    }

    // Export with a non-string name is likewise rejected.
    let export = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![
                Instruction::CreateObject {
                    dst: Register::new(0),
                },
                Instruction::Export {
                    name: ConstantId::new(0),
                    src: Register::new(0),
                },
                Instruction::Return {
                    value: Register::new(0),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        export.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::StringConstantExpected { .. },
            ..
        })
    ));
}

/// A `CreateClosure` capture-array register and a `Call`/`Construct`
/// arguments register must be definitely initialized before use.
#[test]
fn verifier_requires_capture_and_argument_registers_initialized() {
    // captures register (r0) read before any write.
    let uninit_captures = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::CreateClosure {
                    dst: Register::new(1),
                    function: FunctionId::new(0),
                    captures: Register::new(0),
                },
                Instruction::Return {
                    value: Register::new(1),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert_eq!(
        uninit_captures.verify(),
        Err(VerifyError {
            function: Some(FunctionId::new(0)),
            instruction: Some(Pc::new(0)),
            kind: VerifyErrorKind::ReadBeforeWrite {
                register: Register::new(0),
            },
        })
    );

    // arguments register (r2) read before any write in a Call.
    let uninit_args = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            4,
            flags(),
            vec![
                Instruction::CreateObject {
                    dst: Register::new(0),
                },
                Instruction::CreateObject {
                    dst: Register::new(1),
                },
                Instruction::Call {
                    dst: Register::new(3),
                    callee: Register::new(0),
                    this_value: Register::new(1),
                    arguments: Register::new(2),
                },
                Instruction::Return {
                    value: Register::new(3),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert_eq!(
        uninit_args.verify(),
        Err(VerifyError {
            function: Some(FunctionId::new(0)),
            instruction: Some(Pc::new(2)),
            kind: VerifyErrorKind::ReadBeforeWrite {
                register: Register::new(2),
            },
        })
    );
}

#[test]
fn verifier_rejects_reachable_falloff() {
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            // Last instruction is a non-terminator: falls off the end.
            vec![Instruction::CreateObject {
                dst: Register::new(0),
            }],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::JumpOutOfBounds { target: 1, .. },
            ..
        })
    ));
}

#[test]
fn verifier_rejects_bad_jump_and_conditional_targets() {
    for instruction in [
        Instruction::Jump { target: Pc::new(9) },
        Instruction::JumpIfFalse {
            condition: Register::new(0),
            target: Pc::new(9),
        },
    ] {
        let module = Module::new(
            vec![],
            vec![Function::new(
                None,
                0,
                1, // register 0 is a parameter so the condition read is valid
                1,
                flags(),
                vec![instruction],
                vec![],
            )],
            FunctionId::new(0),
        );
        assert!(matches!(
            module.verify(),
            Err(VerifyError {
                kind: VerifyErrorKind::JumpOutOfBounds { .. },
                ..
            })
        ));
    }
}

#[test]
fn verifier_rejects_read_before_write() {
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            3,
            flags(),
            vec![
                Instruction::Binary {
                    dst: Register::new(2),
                    op: BinaryOp::Add,
                    left: Register::new(0),
                    right: Register::new(1),
                },
                Instruction::Return {
                    value: Register::new(2),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert_eq!(
        module.verify(),
        Err(VerifyError {
            function: Some(FunctionId::new(0)),
            instruction: Some(Pc::new(0)),
            kind: VerifyErrorKind::ReadBeforeWrite {
                register: Register::new(0),
            },
        })
    );
}

#[test]
fn captures_and_parameters_are_initialized_on_entry() {
    // One capture (r0) and two parameters (r1, r2) read immediately with no
    // preceding write must verify; captures precede parameters.
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            1,
            2,
            4,
            flags(),
            vec![
                Instruction::Binary {
                    dst: Register::new(3),
                    op: BinaryOp::Add,
                    left: Register::new(0),  // capture
                    right: Register::new(2), // parameter
                },
                Instruction::Return {
                    value: Register::new(1), // parameter
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("captures and params initialized");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(0), Register::new(0)),
        Some(true),
        "capture is initialized on entry"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(0), Register::new(2)),
        Some(true),
        "parameter is initialized on entry"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(0), Register::new(3)),
        Some(false),
        "a non-entry register is not initialized on entry"
    );
}

/// `IteratorNext` writes both `done` and `value`; both are initialized after
/// it, letting a subsequent instruction read them without a separate write.
#[test]
fn iterator_next_initializes_both_written_registers() {
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            4,
            flags(),
            vec![
                Instruction::CreateArray {
                    dst: Register::new(0),
                },
                Instruction::GetIterator {
                    dst: Register::new(1),
                    src: Register::new(0),
                    kind: IteratorKind::Sync,
                },
                Instruction::IteratorNext {
                    done: Register::new(2),
                    value: Register::new(3),
                    iterator: Register::new(1),
                },
                // Read BOTH results: sound only because IteratorNext defines
                // two registers.
                Instruction::Binary {
                    dst: Register::new(2),
                    op: BinaryOp::StrictEqual,
                    left: Register::new(2),
                    right: Register::new(3),
                },
                Instruction::Return {
                    value: Register::new(2),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("two-write dataflow verifies");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(3), Register::new(2)),
        Some(true)
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(3), Register::new(3)),
        Some(true)
    );
}

/// `Await` shares `Suspend`'s CFG and definite-initialization shape:
/// `resume` is its only successor, `dst` is initialized on the resume
/// edge, and no other register gains initialization across the suspension.
#[test]
fn await_has_the_suspend_cfg_and_dataflow_shape() {
    let module = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            3,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::Await {
                    dst: Register::new(1),
                    src: Register::new(0),
                    resume: Pc::new(2),
                },
                Instruction::Return {
                    value: Register::new(1),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("await verifies like suspend");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(1), Register::new(1)),
        Some(false),
        "dst is not initialized before the await"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(2), Register::new(1)),
        Some(true),
        "dst is initialized on the resume edge"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(2), Register::new(2)),
        Some(false),
        "no other register gains initialization across the await"
    );
}

/// An awaited operand must itself be definitely initialized: reading an
/// unwritten register as `src` is a read-before-write error.
#[test]
fn await_rejects_an_uninitialized_operand() {
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::Await {
                    dst: Register::new(1),
                    src: Register::new(0),
                    resume: Pc::new(1),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(module.verify().is_err());
}

/// The split async-iteration pair: `IteratorStep` initializes its raw
/// result register, and `IteratorResult` initializes both `done` and
/// `value`, so the settled object can be read between the two.
#[test]
fn iterator_step_and_result_initialize_their_writes() {
    let module = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            6,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::GetIterator {
                    dst: Register::new(1),
                    src: Register::new(0),
                    kind: IteratorKind::Async,
                },
                Instruction::IteratorStep {
                    dst: Register::new(2),
                    iterator: Register::new(1),
                },
                Instruction::IteratorResult {
                    done: Register::new(3),
                    value: Register::new(4),
                    result: Register::new(2),
                },
                // Read BOTH results: sound only because IteratorResult
                // defines two registers.
                Instruction::Binary {
                    dst: Register::new(5),
                    op: BinaryOp::StrictEqual,
                    left: Register::new(3),
                    right: Register::new(4),
                },
                Instruction::Return {
                    value: Register::new(5),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("split-step dataflow verifies");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(3), Register::new(2)),
        Some(true),
        "the raw result is initialized before IteratorResult reads it"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(4), Register::new(3)),
        Some(true)
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(4), Register::new(4)),
        Some(true)
    );
}

#[test]
fn catch_register_is_observable_in_handler() {
    // The handler reads its catch register with no in-block write; this is
    // sound only because handler dispatch initializes the catch register.
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![
                Instruction::CreateObject {
                    dst: Register::new(0),
                },
                Instruction::Throw {
                    value: Register::new(0),
                },
                Instruction::Return {
                    value: Register::new(0),
                }, // handler
            ],
            vec![ExceptionHandler {
                start: Pc::new(0),
                end: Pc::new(2),
                handler: Pc::new(2),
                catch_register: Register::new(0),
            }],
        )],
        FunctionId::new(0),
    );
    let verified = module
        .verify()
        .expect("catch register initialized on dispatch");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(2), Register::new(0)),
        Some(true)
    );
}

#[test]
fn verifier_rejects_bad_handler_bounds_and_catch_register() {
    let bad_range = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt, Instruction::Halt],
            vec![ExceptionHandler {
                start: Pc::new(1),
                end: Pc::new(1), // empty range
                handler: Pc::new(0),
                catch_register: Register::new(0),
            }],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        bad_range.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::InvalidHandlerBounds { .. },
            ..
        })
    ));

    let bad_catch = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt, Instruction::Halt],
            vec![ExceptionHandler {
                start: Pc::new(0),
                end: Pc::new(2),
                handler: Pc::new(1),
                catch_register: Register::new(5), // >= register_count
            }],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        bad_catch.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::HandlerCatchRegisterOutOfBounds { .. },
            ..
        })
    ));
}

#[test]
fn verifier_rejects_partially_overlapping_handlers() {
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt, Instruction::Halt, Instruction::Halt],
            vec![
                ExceptionHandler {
                    start: Pc::new(0),
                    end: Pc::new(2),
                    handler: Pc::new(0),
                    catch_register: Register::new(0),
                },
                ExceptionHandler {
                    start: Pc::new(1),
                    end: Pc::new(3),
                    handler: Pc::new(2),
                    catch_register: Register::new(0),
                },
            ],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::HandlersPartiallyOverlap { left: 0, right: 1 },
            ..
        })
    ));
}

#[test]
fn verifier_accepts_disjoint_adjacent_and_nested_handlers() {
    // An outer range, an identical duplicate of it (degenerate nesting), a
    // nested child, and two adjacent disjoint siblings (`[1,4)`, `[4,7)`,
    // `[7,10)` touch at boundaries): all laminar, none partially overlapping.
    let handler = |start, end, target| ExceptionHandler {
        start: Pc::new(start),
        end: Pc::new(end),
        handler: Pc::new(target),
        catch_register: Register::new(0),
    };
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt; 10],
            vec![
                handler(0, 10, 0),
                handler(0, 10, 0),
                handler(1, 4, 1),
                handler(4, 7, 4),
                handler(7, 10, 7),
            ],
        )],
        FunctionId::new(0),
    );
    assert!(module.verify().is_ok());
}

#[test]
fn verifier_rejects_crossing_handlers_with_original_indices() {
    // `[0,10)` and `[5,15)` cross: neither disjoint nor nested. The reported
    // indices are the original `Function::handlers` positions.
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt; 15],
            vec![
                ExceptionHandler {
                    start: Pc::new(0),
                    end: Pc::new(10),
                    handler: Pc::new(0),
                    catch_register: Register::new(0),
                },
                ExceptionHandler {
                    start: Pc::new(5),
                    end: Pc::new(15),
                    handler: Pc::new(5),
                    catch_register: Register::new(0),
                },
            ],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::HandlersPartiallyOverlap { left: 0, right: 1 },
            ..
        })
    ));
}

#[test]
fn verifier_accepts_and_preserves_order_of_deeply_nested_handlers() {
    // Deeply nested ranges supplied innermost-first (the reverse of the
    // sweep's internal sort order): verification accepts them and leaves
    // `Function::handlers` in its original wire order.
    const DEPTH: u32 = 64;
    let mut handlers: Vec<ExceptionHandler> = (0..DEPTH)
        .map(|level| ExceptionHandler {
            start: Pc::new(level),
            end: Pc::new(DEPTH * 2 - level),
            handler: Pc::new(level),
            catch_register: Register::new(0),
        })
        .collect();
    handlers.reverse();
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags(),
            vec![Instruction::Halt; (DEPTH * 2) as usize],
            handlers.clone(),
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("laminar nesting verifies");
    assert_eq!(verified.functions()[0].handlers(), handlers.as_slice());
}

#[test]
fn verifier_rejects_facts_work_above_cap() {
    // The work-limit uses a strict `>`, so facts-work equal to the cap is
    // accepted and cap+1 is rejected. The at-cap acceptance case would force
    // the full `MAX_VERIFIER_FACTS_WORDS * 8` = 64 MiB allocation inside
    // `definite_initialization` (there is no register_count / code split
    // that hits the exact cap cheaply), so the boundary is pinned from the
    // rejection side only: one instruction over `MAX_REGISTERS` adds another
    // `MAX_REGISTERS / 64` fact words and tips the total past the cap.
    let words_per_instruction = u64::from(MAX_REGISTERS) / 64;
    let over_cap = (MAX_VERIFIER_FACTS_WORDS / words_per_instruction) as usize + 1;
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            MAX_REGISTERS,
            flags(),
            vec![Instruction::Halt; over_cap],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::VerifierWorkLimitExceeded { .. },
            ..
        })
    ));
}

#[test]
fn verifier_rejects_hostile_near_max_work_before_allocating() {
    // A single function whose facts would need 64 M words (512 MiB, 8x the
    // cap) is rejected in O(functions) time before any bitset is allocated:
    // the module carries only `MAX_REGISTERS` cheap `Halt` instructions.
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            MAX_REGISTERS,
            flags(),
            vec![Instruction::Halt; MAX_REGISTERS as usize],
            vec![],
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::VerifierWorkLimitExceeded { .. },
            ..
        })
    ));
}

#[test]
fn verifier_accepts_loop_carried_facts_and_exposes_certificate() {
    let module = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::Binary {
                    dst: Register::new(1),
                    op: BinaryOp::Add,
                    left: Register::new(0),
                    right: Register::new(0),
                },
                Instruction::Jump { target: Pc::new(1) },
            ],
            vec![],
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("loop has a sound witness");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(certificate.instruction_count(), 3);
    assert_eq!(
        certificate.initialized_before(Pc::new(1), Register::new(0)),
        Some(true)
    );
}

#[test]
fn certificate_queries_are_total_for_all_wrappers() {
    let verified = rich_module().verify().expect("valid");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    // Out-of-range register -> None.
    assert_eq!(
        certificate.initialized_before(Pc::new(0), Register::new(u32::MAX)),
        None
    );
    // Out-of-range PC -> None.
    assert_eq!(
        certificate.initialized_before(Pc::new(u32::MAX), Register::new(0)),
        None
    );
    // Missing certificate for an out-of-range function -> None.
    assert!(verified.certificate(FunctionId::new(9)).is_none());
}

#[test]
fn verification_bytes_counts_certificate_storage() {
    let instruction_count = 2usize;
    let register_count = 130u32;
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            1,
            register_count,
            flags(),
            vec![
                Instruction::Move {
                    dst: Register::new(129),
                    src: Register::new(0),
                },
                Instruction::Return {
                    value: Register::new(129),
                },
            ],
            vec![],
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("test module verifies");
    let words = RegisterSet::words_for(register_count);
    let expected = std::mem::size_of::<Certificate>()
        + instruction_count * std::mem::size_of::<RegisterSet>()
        + instruction_count * words * std::mem::size_of::<u64>();

    assert_eq!(module.verification_bytes(), expected);
}

#[test]
fn compact_scalar_layouts_are_preserved() {
    assert_eq!(std::mem::size_of::<Register>(), 4);
    assert_eq!(std::mem::size_of::<Pc>(), 4);
    assert_eq!(std::mem::size_of::<NumberBits>(), 8);
    assert_eq!(std::mem::size_of::<FunctionFlags>(), 5);
}

#[test]
fn iterator_close_initializes_both_results_for_close_validation() {
    let module = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            4,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::GetIterator {
                    dst: Register::new(1),
                    src: Register::new(0),
                    kind: IteratorKind::Sync,
                },
                Instruction::IteratorClose {
                    result: Register::new(2),
                    called: Register::new(3),
                    iterator: Register::new(1),
                    mode: IteratorCloseMode::Propagate,
                },
                Instruction::RequireCloseResult {
                    result: Register::new(2),
                    called: Register::new(3),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("close result dataflow verifies");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(3), Register::new(2)),
        Some(true),
        "IteratorClose initializes result"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(3), Register::new(3)),
        Some(true),
        "IteratorClose initializes called"
    );
}

#[test]
fn require_close_result_reads_both_operands() {
    for instruction in [
        Instruction::RequireCloseResult {
            result: Register::new(0),
            called: Register::new(1),
        },
        Instruction::RequireCloseResult {
            result: Register::new(1),
            called: Register::new(0),
        },
    ] {
        let module = Module::new(
            vec![Constant::Int32(0)],
            vec![Function::new(
                None,
                0,
                0,
                2,
                flags(),
                vec![
                    Instruction::LoadConst {
                        dst: Register::new(0),
                        constant: ConstantId::new(0),
                    },
                    instruction,
                    Instruction::Halt,
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            module.verify().is_err(),
            "both operands must be initialized"
        );
    }
}
#[test]
fn suppress_error_reads_both_operands() {
    for instruction in [
        Instruction::SuppressError {
            dst: Register::new(2),
            error: Register::new(0),
            suppressed: Register::new(1),
        },
        Instruction::SuppressError {
            dst: Register::new(2),
            error: Register::new(1),
            suppressed: Register::new(0),
        },
    ] {
        let module = Module::new(
            vec![Constant::Int32(0)],
            vec![Function::new(
                None,
                0,
                0,
                3,
                flags(),
                vec![
                    Instruction::LoadConst {
                        dst: Register::new(0),
                        constant: ConstantId::new(0),
                    },
                    instruction,
                    Instruction::Halt,
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            module.verify().is_err(),
            "both SuppressError operands must be initialized"
        );
    }
}

#[test]
fn verifier_rejects_aliased_iterator_close_outputs() {
    let register = Register::new(1);
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::IteratorClose {
                    result: register,
                    called: register,
                    iterator: Register::new(0),
                    mode: IteratorCloseMode::Propagate,
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );

    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::AliasedIteratorCloseOutputs { register: found },
            ..
        }) if found == register
    ));
}

#[test]
fn verifier_rejects_aliased_dispose_capture_outputs() {
    let register = Register::new(1);
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::DisposeCapture {
                    method: register,
                    kind: register,
                    src: Register::new(0),
                    hint: DisposeHint::Sync,
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::AliasedDisposeCaptureOutputs { register: found },
            ..
        }) if found == register
    ));
}

#[test]
fn verifier_rejects_aliased_iterator_next_outputs() {
    let register = Register::new(1);
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::IteratorNext {
                    done: register,
                    value: register,
                    iterator: Register::new(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::AliasedIteratorNextOutputs { register: found },
            ..
        }) if found == register
    ));
}

#[test]
fn verifier_rejects_aliased_iterator_result_outputs() {
    let register = Register::new(1);
    let module = Module::new(
        vec![],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::IteratorResult {
                    done: register,
                    value: register,
                    result: Register::new(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::AliasedIteratorResultOutputs { register: found },
            ..
        }) if found == register
    ));
}

#[test]
fn to_object_reads_source_before_writing_destination() {
    let valid = Module::new(
        vec![Constant::Int32(7)],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::ToObject {
                    dst: Register::new(1),
                    src: Register::new(0),
                },
                Instruction::Return {
                    value: Register::new(1),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("ToObject source and destination verify");
    assert_eq!(
        valid
            .certificate(FunctionId::new(0))
            .expect("certificate")
            .initialized_before(Pc::new(2), Register::new(1)),
        Some(true),
        "ToObject defines its destination"
    );

    let unread_source = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::ToObject {
                    dst: Register::new(1),
                    src: Register::new(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(unread_source.verify().is_err(), "ToObject reads its source");
}

#[test]
fn construct_with_new_target_rejects_out_of_bounds_registers() {
    for instruction in [
        Instruction::ConstructWithNewTarget {
            dst: Register::new(4),
            callee: Register::new(0),
            new_target: Register::new(1),
            arguments: Register::new(2),
        },
        Instruction::ConstructWithNewTarget {
            dst: Register::new(0),
            callee: Register::new(4),
            new_target: Register::new(1),
            arguments: Register::new(2),
        },
        Instruction::ConstructWithNewTarget {
            dst: Register::new(0),
            callee: Register::new(1),
            new_target: Register::new(4),
            arguments: Register::new(2),
        },
        Instruction::ConstructWithNewTarget {
            dst: Register::new(0),
            callee: Register::new(1),
            new_target: Register::new(2),
            arguments: Register::new(4),
        },
    ] {
        let module = Module::new(
            Vec::new(),
            vec![Function::new(
                None,
                0,
                3,
                3,
                flags(),
                vec![instruction, Instruction::Halt],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            matches!(
                module.verify(),
                Err(VerifyError {
                    kind: VerifyErrorKind::RegisterOutOfBounds { .. },
                    ..
                })
            ),
            "ConstructWithNewTarget must reject out-of-bounds registers"
        );
    }
}

#[test]
fn construct_with_new_target_round_trips_on_the_wire() {
    let instruction = Instruction::ConstructWithNewTarget {
        dst: Register::new(1),
        callee: Register::new(2),
        new_target: Register::new(3),
        arguments: Register::new(4),
    };
    let mut bytes = Vec::new();
    encode_instruction(instruction, &mut bytes);
    assert_eq!(bytes.first().copied(), Some(47), "wire tag is 47");
    let limits = DecodeLimits::default();
    let mut decoder = Decoder {
        bytes: &bytes,
        offset: 0,
        limits: &limits,
        total_instructions: 0,
    };
    let decoded = decoder.instruction().expect("opcode decodes");
    assert_eq!(decoded, instruction);
    assert_eq!(decoder.offset, bytes.len());
}

#[test]
fn define_data_property_rejects_out_of_bounds_registers() {
    for instruction in [
        Instruction::DefineDataProperty {
            object: Register::new(3),
            key: Register::new(0),
            value: Register::new(1),
        },
        Instruction::DefineDataProperty {
            object: Register::new(0),
            key: Register::new(3),
            value: Register::new(1),
        },
        Instruction::DefineDataProperty {
            object: Register::new(0),
            key: Register::new(1),
            value: Register::new(3),
        },
    ] {
        let module = Module::new(
            Vec::new(),
            vec![Function::new(
                None,
                0,
                3,
                3,
                flags(),
                vec![instruction, Instruction::Halt],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            matches!(
                module.verify(),
                Err(VerifyError {
                    kind: VerifyErrorKind::RegisterOutOfBounds { .. },
                    ..
                })
            ),
            "DefineDataProperty must reject out-of-bounds registers"
        );
    }
}

#[test]
fn define_data_property_round_trips_on_the_wire() {
    let instruction = Instruction::DefineDataProperty {
        object: Register::new(1),
        key: Register::new(2),
        value: Register::new(3),
    };
    let mut bytes = Vec::new();
    encode_instruction(instruction, &mut bytes);
    assert_eq!(bytes.first().copied(), Some(48), "wire tag is 48");
    let limits = DecodeLimits::default();
    let mut decoder = Decoder {
        bytes: &bytes,
        offset: 0,
        limits: &limits,
        total_instructions: 0,
    };
    let decoded = decoder.instruction().expect("opcode decodes");
    assert_eq!(decoded, instruction);
    assert_eq!(decoder.offset, bytes.len());
}

#[test]
fn own_descriptor_slot_opcodes_round_trip_exact_bytes() {
    let cases = [
        (
            Instruction::LoadOwnDescriptorSlot {
                dst: Register::new(1),
                object: Register::new(2),
                key: Register::new(3),
                slot: DescriptorSlot::Value,
            },
            vec![49, 1, 2, 3, 0],
        ),
        (
            Instruction::LoadOwnDescriptorSlot {
                dst: Register::new(4),
                object: Register::new(5),
                key: Register::new(6),
                slot: DescriptorSlot::Getter,
            },
            vec![49, 4, 5, 6, 1],
        ),
        (
            Instruction::LoadOwnDescriptorSlot {
                dst: Register::new(7),
                object: Register::new(8),
                key: Register::new(9),
                slot: DescriptorSlot::Setter,
            },
            vec![49, 7, 8, 9, 2],
        ),
        (
            Instruction::DefineOwnDescriptorSlot {
                object: Register::new(1),
                key: Register::new(2),
                src: Register::new(3),
                slot: DescriptorSlot::Value,
            },
            vec![50, 1, 2, 3, 0],
        ),
        (
            Instruction::DefineOwnDescriptorSlot {
                object: Register::new(4),
                key: Register::new(5),
                src: Register::new(6),
                slot: DescriptorSlot::Getter,
            },
            vec![50, 4, 5, 6, 1],
        ),
        (
            Instruction::DefineOwnDescriptorSlot {
                object: Register::new(7),
                key: Register::new(8),
                src: Register::new(9),
                slot: DescriptorSlot::Setter,
            },
            vec![50, 7, 8, 9, 2],
        ),
    ];
    let limits = DecodeLimits::default();
    for (instruction, expected) in cases {
        let mut bytes = Vec::new();
        encode_instruction(instruction, &mut bytes);
        assert_eq!(bytes, expected, "{instruction:?} exact wire layout");
        let mut decoder = Decoder {
            bytes: &bytes,
            offset: 0,
            limits: &limits,
            total_instructions: 0,
        };
        let decoded = decoder.instruction().expect("opcode decodes");
        assert_eq!(decoded, instruction);
        assert_eq!(decoder.offset, bytes.len());
    }
}

#[test]
fn own_descriptor_slot_opcodes_scale_past_127_registers() {
    let load = Instruction::LoadOwnDescriptorSlot {
        dst: Register::new(200),
        object: Register::new(201),
        key: Register::new(202),
        slot: DescriptorSlot::Getter,
    };
    let define = Instruction::DefineOwnDescriptorSlot {
        object: Register::new(200),
        key: Register::new(201),
        src: Register::new(202),
        slot: DescriptorSlot::Setter,
    };
    for instruction in [load, define] {
        let mut bytes = Vec::new();
        encode_instruction(instruction, &mut bytes);
        assert!(
            bytes.windows(2).any(|pair| pair == [0xc8, 0x01]),
            "register 200 must use two-byte LEB128"
        );
        let limits = DecodeLimits::default();
        let mut decoder = Decoder {
            bytes: &bytes,
            offset: 0,
            limits: &limits,
            total_instructions: 0,
        };
        assert_eq!(decoder.instruction().expect("decodes"), instruction);
    }
}

#[test]
fn load_own_descriptor_slot_defines_dst_and_requires_operands() {
    let verified = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            2,
            3,
            flags(),
            vec![
                Instruction::LoadOwnDescriptorSlot {
                    dst: Register::new(2),
                    object: Register::new(0),
                    key: Register::new(1),
                    slot: DescriptorSlot::Value,
                },
                Instruction::Return {
                    value: Register::new(2),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("LoadOwnDescriptorSlot defines dst");
    assert_eq!(
        verified
            .certificate(FunctionId::new(0))
            .and_then(|cert| { cert.initialized_before(Pc::new(1), Register::new(2)) }),
        Some(true),
        "dst is defined after LoadOwnDescriptorSlot"
    );

    let unread_object = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            1,
            3,
            flags(),
            vec![
                Instruction::LoadOwnDescriptorSlot {
                    dst: Register::new(2),
                    object: Register::new(1),
                    key: Register::new(0),
                    slot: DescriptorSlot::Getter,
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        unread_object.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ReadBeforeWrite { .. },
            ..
        })
    ));

    let unread_key = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            1,
            3,
            flags(),
            vec![
                Instruction::LoadOwnDescriptorSlot {
                    dst: Register::new(2),
                    object: Register::new(0),
                    key: Register::new(1),
                    slot: DescriptorSlot::Setter,
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        unread_key.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ReadBeforeWrite { .. },
            ..
        })
    ));
}

#[test]
fn define_own_descriptor_slot_requires_all_operands_defined() {
    let ok = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            3,
            3,
            flags(),
            vec![
                Instruction::DefineOwnDescriptorSlot {
                    object: Register::new(0),
                    key: Register::new(1),
                    src: Register::new(2),
                    slot: DescriptorSlot::Setter,
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(ok.verify().is_ok());

    for (instruction, parameter_count) in [
        (
            Instruction::DefineOwnDescriptorSlot {
                object: Register::new(2),
                key: Register::new(0),
                src: Register::new(1),
                slot: DescriptorSlot::Value,
            },
            2,
        ),
        (
            Instruction::DefineOwnDescriptorSlot {
                object: Register::new(0),
                key: Register::new(2),
                src: Register::new(1),
                slot: DescriptorSlot::Getter,
            },
            2,
        ),
        (
            Instruction::DefineOwnDescriptorSlot {
                object: Register::new(0),
                key: Register::new(1),
                src: Register::new(2),
                slot: DescriptorSlot::Value,
            },
            2,
        ),
    ] {
        let unread = Module::new(
            Vec::new(),
            vec![Function::new(
                None,
                0,
                parameter_count,
                3,
                flags(),
                vec![instruction, Instruction::Halt],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            matches!(
                unread.verify(),
                Err(VerifyError {
                    kind: VerifyErrorKind::ReadBeforeWrite { .. },
                    ..
                })
            ),
            "DefineOwnDescriptorSlot requires object, key, and src initialized"
        );
    }
}

#[test]
fn own_descriptor_slot_opcodes_reject_out_of_bounds_registers() {
    for instruction in [
        Instruction::LoadOwnDescriptorSlot {
            dst: Register::new(3),
            object: Register::new(0),
            key: Register::new(1),
            slot: DescriptorSlot::Value,
        },
        Instruction::LoadOwnDescriptorSlot {
            dst: Register::new(0),
            object: Register::new(3),
            key: Register::new(1),
            slot: DescriptorSlot::Value,
        },
        Instruction::LoadOwnDescriptorSlot {
            dst: Register::new(0),
            object: Register::new(1),
            key: Register::new(3),
            slot: DescriptorSlot::Value,
        },
        Instruction::DefineOwnDescriptorSlot {
            object: Register::new(3),
            key: Register::new(0),
            src: Register::new(1),
            slot: DescriptorSlot::Getter,
        },
        Instruction::DefineOwnDescriptorSlot {
            object: Register::new(0),
            key: Register::new(3),
            src: Register::new(1),
            slot: DescriptorSlot::Getter,
        },
        Instruction::DefineOwnDescriptorSlot {
            object: Register::new(0),
            key: Register::new(1),
            src: Register::new(3),
            slot: DescriptorSlot::Getter,
        },
    ] {
        let module = Module::new(
            Vec::new(),
            vec![Function::new(
                None,
                0,
                3,
                3,
                flags(),
                vec![instruction, Instruction::Halt],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            matches!(
                module.verify(),
                Err(VerifyError {
                    kind: VerifyErrorKind::RegisterOutOfBounds { .. },
                    ..
                })
            ),
            "own-descriptor slot opcodes must reject out-of-bounds registers"
        );
    }
}

#[test]
fn with_has_binding_round_trips_on_the_wire() {
    let instruction = Instruction::WithHasBinding {
        dst: Register::new(1),
        object: Register::new(2),
        key: Register::new(3),
    };
    let mut bytes = Vec::new();
    encode_instruction(instruction, &mut bytes);
    assert_eq!(
        bytes,
        vec![51, 1, 2, 3],
        "wire tag is 51 with dst/object/key"
    );
    let limits = DecodeLimits::default();
    let mut decoder = Decoder {
        bytes: &bytes,
        offset: 0,
        limits: &limits,
        total_instructions: 0,
    };
    let decoded = decoder.instruction().expect("opcode decodes");
    assert_eq!(decoded, instruction);
    assert_eq!(decoder.offset, bytes.len());
}

#[test]
fn with_has_binding_rejects_truncated_decoding() {
    assert!(decode(&one_function_bytes(&[51]), &DecodeLimits::default()).is_err());
    assert!(decode(&one_function_bytes(&[51, 0]), &DecodeLimits::default()).is_err());
    assert!(decode(&one_function_bytes(&[51, 0, 0]), &DecodeLimits::default()).is_err());
}

#[test]
fn with_has_binding_rejects_out_of_bounds_registers() {
    for instruction in [
        Instruction::WithHasBinding {
            dst: Register::new(3),
            object: Register::new(0),
            key: Register::new(1),
        },
        Instruction::WithHasBinding {
            dst: Register::new(0),
            object: Register::new(3),
            key: Register::new(1),
        },
        Instruction::WithHasBinding {
            dst: Register::new(0),
            object: Register::new(1),
            key: Register::new(3),
        },
    ] {
        let module = Module::new(
            Vec::new(),
            vec![Function::new(
                None,
                0,
                3,
                3,
                flags(),
                vec![instruction, Instruction::Halt],
                Vec::new(),
            )],
            FunctionId::new(0),
        );
        assert!(
            matches!(
                module.verify(),
                Err(VerifyError {
                    kind: VerifyErrorKind::RegisterOutOfBounds { .. },
                    ..
                })
            ),
            "WithHasBinding must reject out-of-bounds registers"
        );
    }
}

#[test]
fn with_has_binding_defines_dst_and_requires_operands() {
    let verified = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            2,
            3,
            flags(),
            vec![
                Instruction::WithHasBinding {
                    dst: Register::new(2),
                    object: Register::new(0),
                    key: Register::new(1),
                },
                Instruction::Return {
                    value: Register::new(2),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("WithHasBinding defines dst");
    assert_eq!(
        verified
            .certificate(FunctionId::new(0))
            .and_then(|cert| { cert.initialized_before(Pc::new(1), Register::new(2)) }),
        Some(true),
        "dst is defined after WithHasBinding"
    );

    let unread_object = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            1,
            3,
            flags(),
            vec![
                Instruction::WithHasBinding {
                    dst: Register::new(2),
                    object: Register::new(1),
                    key: Register::new(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        unread_object.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ReadBeforeWrite { .. },
            ..
        })
    ));

    let unread_key = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            1,
            3,
            flags(),
            vec![
                Instruction::WithHasBinding {
                    dst: Register::new(2),
                    object: Register::new(0),
                    key: Register::new(1),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        unread_key.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ReadBeforeWrite { .. },
            ..
        })
    ));
}

#[test]
fn suspend_initializes_value_and_mode_on_resume() {
    let module = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            3,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::Suspend {
                    dst: Register::new(1),
                    src: Register::new(0),
                    resume: Pc::new(2),
                    mode: Register::new(2),
                },
                Instruction::Return {
                    value: Register::new(2),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    let verified = module.verify().expect("Suspend mode is engine-defined");
    let certificate = verified.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        certificate.initialized_before(Pc::new(2), Register::new(1)),
        Some(true),
        "resumed value is initialized on the resume edge"
    );
    assert_eq!(
        certificate.initialized_before(Pc::new(2), Register::new(2)),
        Some(true),
        "resume mode is initialized on the resume edge"
    );
}

#[test]
fn verifier_rejects_out_of_bounds_suspend_mode() {
    let module = Module::new(
        vec![Constant::Int32(0)],
        vec![Function::new(
            None,
            0,
            0,
            2,
            flags(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(0),
                },
                Instruction::Suspend {
                    dst: Register::new(1),
                    src: Register::new(0),
                    resume: Pc::new(2),
                    mode: Register::new(2),
                },
                Instruction::Return {
                    value: Register::new(1),
                },
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        module.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::RegisterOutOfBounds { register, .. },
            ..
        }) if register == Register::new(2)
    ));
}
#[test]
fn extension_opcodes_round_trip_through_root_codec_and_verify() {
    let instructions = [
        Instruction::GetSuper {
            dst: Register::new(0),
            home: Register::new(1),
            receiver: Register::new(2),
            key: Register::new(3),
        },
        Instruction::SetSuper {
            home: Register::new(0),
            receiver: Register::new(1),
            key: Register::new(2),
            value: Register::new(3),
        },
        Instruction::ImportAttributes {
            dst: Register::new(0),
            specifier: ConstantId::new(0),
            attributes: Register::new(1),
        },
        Instruction::ImportDynamicAttributes {
            dst: Register::new(0),
            specifier: Register::new(1),
            attributes: Register::new(2),
        },
        Instruction::CopyDataProperties {
            target: Register::new(0),
            source: Register::new(1),
            excluded: Register::new(2),
        },
        Instruction::GetTemplateObject {
            dst: Register::new(0),
            cooked: Register::new(1),
            raw: Register::new(2),
        },
        Instruction::RequireGlobalBinding {
            name: ConstantId::new(0),
        },
        Instruction::ThrowIntrinsicError {
            kind: IntrinsicErrorKind::ReferenceError,
            message: ConstantId::new(0),
        },
    ];
    let limits = DecodeLimits::default();
    for instruction in instructions {
        let mut bytes = Vec::new();
        encode_instruction(instruction, &mut bytes);
        let mut decoder = Decoder {
            bytes: &bytes,
            offset: 0,
            limits: &limits,
            total_instructions: 0,
        };
        assert_eq!(
            decoder.instruction().expect("extension decodes"),
            instruction
        );
        assert_eq!(decoder.offset, bytes.len());

        Module::new(
            vec![Constant::String(EcmaString::from("dep"))],
            vec![Function::new(
                None,
                0,
                4,
                4,
                flags(),
                vec![instruction, Instruction::Halt],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("extension verifies through the root contract");
    }
}

#[test]
fn root_decoder_rejects_truncated_and_unknown_extension_bytes() {
    let limits = DecodeLimits::default();
    for bytes in [
        &[52_u8][..],
        &[54, 0, 0][..],
        &[57, 0, 0][..],
        &[58][..],
        &[59, 0][..],
    ] {
        let mut decoder = Decoder {
            bytes,
            offset: 0,
            limits: &limits,
            total_instructions: 0,
        };
        assert!(matches!(
            decoder.instruction(),
            Err(DecodeError {
                kind: DecodeErrorKind::UnexpectedEof,
                ..
            })
        ));
    }

    let mut decoder = Decoder {
        bytes: &[60],
        offset: 0,
        limits: &limits,
        total_instructions: 0,
    };
    assert!(matches!(
        decoder.instruction(),
        Err(DecodeError {
            kind: DecodeErrorKind::InvalidOpcode { opcode: 60 },
            ..
        })
    ));
}

#[test]
fn extension_verifier_rejects_alias_type_bounds_and_uninitialized_reads() {
    let alias = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            3,
            3,
            flags(),
            vec![
                Instruction::CopyDataProperties {
                    target: Register::new(0),
                    source: Register::new(0),
                    excluded: Register::new(2),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        alias.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::AliasedCopyDataProperties { register },
            ..
        }) if register == Register::new(0)
    ));

    let wrong_constant_type = Module::new(
        vec![Constant::Int32(1)],
        vec![Function::new(
            None,
            0,
            1,
            2,
            flags(),
            vec![
                Instruction::ImportAttributes {
                    dst: Register::new(1),
                    specifier: ConstantId::new(0),
                    attributes: Register::new(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        wrong_constant_type.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::StringConstantExpected { .. },
            ..
        })
    ));

    let out_of_bounds = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            1,
            1,
            flags(),
            vec![
                Instruction::GetTemplateObject {
                    dst: Register::new(0),
                    cooked: Register::new(0),
                    raw: Register::new(1),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        out_of_bounds.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::RegisterOutOfBounds { register, .. },
            ..
        }) if register == Register::new(1)
    ));

    let uninitialized = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            0,
            4,
            flags(),
            vec![
                Instruction::GetSuper {
                    dst: Register::new(0),
                    home: Register::new(1),
                    receiver: Register::new(2),
                    key: Register::new(3),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        FunctionId::new(0),
    );
    assert!(matches!(
        uninitialized.verify(),
        Err(VerifyError {
            kind: VerifyErrorKind::ReadBeforeWrite { .. },
            ..
        })
    ));
}
