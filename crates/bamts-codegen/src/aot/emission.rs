use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use bamts_bytecode::{ModuleId, Program, Verified};
use bamts_cancel::CancellationToken;
use cranelift_codegen::ir::Endianness;
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable, Flags};
use sha2::{Digest, Sha256};

use super::{AotError, AotObject, compile_aot_with_cancel};
use crate::{LowerError, ProgramLowerError};

/// The target cells for which BamTS publishes AOT evidence.
pub const SUPPORTED_TARGET_TRIPLES: [&str; 7] = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "s390x-unknown-linux-gnu",
    "riscv64gc-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-apple-darwin",
    "x86_64-pc-windows-msvc",
];

/// Canonical code-generation properties for one registered target cell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TargetDescriptor {
    triple: String,
    pointer_width: u8,
    endianness: Endianness,
    call_convention: String,
}

impl TargetDescriptor {
    /// Resolves one registered target through the pinned Cranelift ISA registry.
    pub fn lookup(target: &str) -> Result<Self, EmissionError> {
        if !SUPPORTED_TARGET_TRIPLES.contains(&target) {
            return Err(EmissionError::Target(AotError::TargetLookup(format!(
                "`{target}` is not a registered BamTS target"
            ))));
        }

        let mut flag_builder = settings::builder();
        flag_builder
            .set("is_pic", "true")
            .map_err(|error| EmissionError::Target(AotError::TargetBuild(error.to_string())))?;
        let flags = Flags::new(flag_builder);
        let isa_builder = isa::lookup_by_name(target)
            .map_err(|error| EmissionError::Target(AotError::TargetLookup(error.to_string())))?;
        let isa = isa_builder
            .finish(flags)
            .map_err(|error| EmissionError::Target(AotError::TargetBuild(error.to_string())))?;
        let triple = isa.triple().to_string();
        let pointer_width = isa.frontend_config().pointer_bits();
        require_64_bit_pointer_width(pointer_width)?;
        isa.triple()
            .endianness()
            .map_err(|()| EmissionError::Target(AotError::TargetEndianness(triple.clone())))?;

        Ok(Self {
            triple,
            pointer_width,
            endianness: isa.endianness(),
            call_convention: format!("{:?}", isa.frontend_config().default_call_conv),
        })
    }

    #[must_use]
    pub fn triple(&self) -> &str {
        &self.triple
    }

    #[must_use]
    pub const fn pointer_width(&self) -> u8 {
        self.pointer_width
    }

    #[must_use]
    pub const fn endianness(&self) -> Endianness {
        self.endianness
    }

    #[must_use]
    pub fn call_convention(&self) -> &str {
        &self.call_convention
    }

    /// Content-addressed identity of every target property that affects output.
    #[must_use]
    pub fn fingerprint(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"bamts-target/v1\0");
        hasher.update(self.triple.as_bytes());
        hasher.update(b"\0");
        hasher.update(self.pointer_width.to_string().as_bytes());
        hasher.update(b"\0");
        hasher.update(format!("{:?}", self.endianness).as_bytes());
        hasher.update(b"\0");
        hasher.update(self.call_convention.as_bytes());
        hasher.finalize().into()
    }

    #[must_use]
    pub fn fingerprint_hex(&self) -> String {
        hex_digest(self.fingerprint())
    }
}

/// One raw AOT object paired with its resolved target and byte digest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedObject {
    object: AotObject,
    descriptor: TargetDescriptor,
    digest: [u8; 32],
}

impl EmittedObject {
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.object.bytes
    }

    #[must_use]
    pub const fn object(&self) -> &AotObject {
        &self.object
    }

    #[must_use]
    pub const fn target(&self) -> &TargetDescriptor {
        &self.descriptor
    }

    #[must_use]
    pub const fn content_digest(&self) -> [u8; 32] {
        self.digest
    }

    #[must_use]
    pub fn content_digest_hex(&self) -> String {
        hex_digest(self.digest)
    }
}

/// A failure while resolving or emitting one target object.
#[derive(Debug)]
pub enum EmissionError {
    Target(AotError),
    Compile(AotError),
    TargetMismatch { requested: String, emitted: String },
    DuplicateTarget(String),
}

impl fmt::Display for EmissionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Target(error) => write!(formatter, "target resolution failed: {error}"),
            Self::Compile(error) => write!(formatter, "target emission failed: {error}"),
            Self::TargetMismatch { requested, emitted } => write!(
                formatter,
                "emitted object target `{emitted}` does not match requested target `{requested}`"
            ),
            Self::DuplicateTarget(target) => {
                write!(formatter, "target `{target}` was requested more than once")
            }
        }
    }
}

impl From<EmissionError> for AotError {
    fn from(error: EmissionError) -> Self {
        match error {
            EmissionError::Target(error) | EmissionError::Compile(error) => error,
            error @ (EmissionError::TargetMismatch { .. } | EmissionError::DuplicateTarget(_)) => {
                Self::TargetBuild(error.to_string())
            }
        }
    }
}

impl Error for EmissionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Target(error) | Self::Compile(error) => Some(error),
            Self::TargetMismatch { .. } | Self::DuplicateTarget(_) => None,
        }
    }
}

fn require_64_bit_pointer_width(bits: u8) -> Result<(), EmissionError> {
    if bits == 64 {
        return Ok(());
    }
    Err(EmissionError::Target(AotError::Lower(ProgramLowerError {
        module: ModuleId::new(0),
        kind: LowerError::UnsupportedPointerWidth { bits },
    })))
}

#[must_use]
pub fn content_digest(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

/// Confirms that an emitted object's normalized target matches its descriptor.
pub fn require_matching_target(
    emitted: &EmittedObject,
    expected: &TargetDescriptor,
) -> Result<(), EmissionError> {
    if emitted.object.target == expected.triple {
        return Ok(());
    }
    Err(EmissionError::TargetMismatch {
        requested: expected.triple.clone(),
        emitted: emitted.object.target.clone(),
    })
}

/// Emits one object using a fresh cancellation token.
pub fn emit_for_target(
    program: &Program<Verified>,
    target: &TargetDescriptor,
) -> Result<EmittedObject, EmissionError> {
    emit_for_target_with_cancel(program, target, &CancellationToken::new())
}

/// Emits one object through the sole raw AOT implementation.
pub fn emit_for_target_with_cancel(
    program: &Program<Verified>,
    target: &TargetDescriptor,
    cancel: &CancellationToken,
) -> Result<EmittedObject, EmissionError> {
    let object = compile_aot_with_cancel(program, target.triple(), cancel)
        .map_err(EmissionError::Compile)?;
    let emitted = EmittedObject {
        digest: content_digest(&object.bytes),
        descriptor: target.clone(),
        object,
    };
    require_matching_target(&emitted, target)?;
    Ok(emitted)
}

/// Emits each requested target exactly once, in caller order.
pub fn emit_for_targets<'a>(
    program: &Program<Verified>,
    targets: impl IntoIterator<Item = &'a TargetDescriptor>,
) -> Result<Vec<EmittedObject>, EmissionError> {
    let mut seen = BTreeSet::new();
    let mut emitted = Vec::new();
    for target in targets {
        if !seen.insert(target.triple()) {
            return Err(EmissionError::DuplicateTarget(target.triple().to_owned()));
        }
        emitted.push(emit_for_target(program, target)?);
    }
    Ok(emitted)
}

fn hex_digest(digest: [u8; 32]) -> String {
    use std::fmt::Write as _;

    let mut output = String::with_capacity(64);
    for byte in digest {
        write!(output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::{
        Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
        ModuleId, ProgramModule, Register,
    };

    use super::*;

    fn program(value: i32) -> Program<Verified> {
        let function = Function::new(
            None,
            0,
            0,
            1,
            FunctionFlags::default(),
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(1),
                },
                Instruction::Return {
                    value: Register::new(0),
                },
            ],
            Vec::new(),
        );
        let module = Module::new(
            vec![
                Constant::String(EcmaString::encode("emission-test")),
                Constant::Int32(value),
            ],
            vec![function],
            FunctionId::new(0),
        )
        .verify()
        .expect("test module verifies");
        Program::link(
            vec![ProgramModule {
                name: ConstantId::new(0),
                code: module,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("test program links")
    }

    fn host_descriptor() -> TargetDescriptor {
        TargetDescriptor::lookup("x86_64-unknown-linux-gnu").expect("registered target resolves")
    }

    #[test]
    fn registered_descriptors_resolve_through_cranelift() {
        for triple in SUPPORTED_TARGET_TRIPLES {
            let descriptor = TargetDescriptor::lookup(triple).expect("registered target resolves");
            assert_eq!(descriptor.triple(), triple);
            assert_eq!(descriptor.pointer_width(), 64);
            assert_eq!(descriptor.fingerprint_hex().len(), 64);
        }
        assert_eq!(
            TargetDescriptor::lookup("x86_64-unknown-linux-gnu")
                .unwrap()
                .endianness(),
            Endianness::Little
        );
        assert_eq!(
            TargetDescriptor::lookup("s390x-unknown-linux-gnu")
                .unwrap()
                .endianness(),
            Endianness::Big
        );
    }

    #[test]
    fn each_registered_target_emits_its_own_object_format() {
        for (triple, magic) in [
            ("x86_64-unknown-linux-gnu", &[0x7f, b'E', b'L', b'F'][..]),
            ("aarch64-apple-darwin", &[0xcf, 0xfa, 0xed, 0xfe][..]),
            ("x86_64-apple-darwin", &[0xcf, 0xfa, 0xed, 0xfe][..]),
            ("x86_64-pc-windows-msvc", &[0x64, 0x86][..]),
        ] {
            let descriptor = TargetDescriptor::lookup(triple).expect("registered target resolves");
            let emitted = emit_for_target(&program(42), &descriptor).expect("object emits");
            assert!(emitted.bytes().starts_with(magic), "{triple}");
        }
    }

    #[test]
    fn unsupported_target_and_pointer_width_are_typed() {
        assert!(matches!(
            TargetDescriptor::lookup("i686-unknown-linux-gnu"),
            Err(EmissionError::Target(AotError::TargetLookup(_)))
        ));
        assert!(matches!(
            require_64_bit_pointer_width(32),
            Err(EmissionError::Target(AotError::Lower(ProgramLowerError {
                kind: LowerError::UnsupportedPointerWidth { bits: 32 },
                ..
            })))
        ));
    }

    #[test]
    fn duplicate_emission_preserves_object_and_digest_identity() {
        let descriptor = host_descriptor();
        let first = emit_for_target(&program(42), &descriptor).expect("first emission succeeds");
        let second = emit_for_target(&program(42), &descriptor).expect("second emission succeeds");
        assert_eq!(first.bytes(), second.bytes());
        assert_eq!(first.object(), second.object());
        assert_eq!(first.content_digest(), content_digest(first.bytes()));
        assert_eq!(first.content_digest(), second.content_digest());
    }

    #[test]
    fn target_mismatch_and_duplicate_target_are_rejected() {
        let descriptor = host_descriptor();
        let emitted = emit_for_target(&program(42), &descriptor).expect("emission succeeds");
        let mut other = descriptor.clone();
        other.triple = "aarch64-unknown-linux-gnu".to_owned();
        assert!(matches!(
            require_matching_target(&emitted, &other),
            Err(EmissionError::TargetMismatch { .. })
        ));
        assert!(matches!(
            emit_for_targets(&program(42), [&descriptor, &descriptor]),
            Err(EmissionError::DuplicateTarget(_))
        ));
    }

    #[test]
    fn content_and_target_digests_change_with_identity() {
        assert_ne!(content_digest(b"first"), content_digest(b"second"));
        let x86 = TargetDescriptor::lookup("x86_64-unknown-linux-gnu").unwrap();
        let arm = TargetDescriptor::lookup("aarch64-unknown-linux-gnu").unwrap();
        assert_ne!(x86.fingerprint(), arm.fingerprint());
    }
}
