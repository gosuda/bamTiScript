//! ISA-to-runtime-helper lowering demands.
//!
//! Every [`Instruction`] either lowers entirely to native code or calls exactly
//! one [`Helper`]. [`helper_demand`] is total over the instruction algebra, so a
//! newly appended opcode fails to compile here instead of silently reaching a
//! fallback, and [`verify_helper_coverage`] proves the classification reaches
//! every one of the [`HELPER_COUNT`] runtime helpers exactly through the
//! opcodes that need it plus the declared [`STRUCTURAL_HELPERS`].

use bamts_bytecode::{
    AccessorKind, BinaryOp, ConstantId, DescriptorSlot, DisposeHint, FunctionId, Instruction,
    IntrinsicErrorKind, IteratorCloseMode, IteratorKind, Pc, Register, UnaryOp,
};
use bamts_native::HELPER_COUNT;
use cranelift_codegen::ir::types;

use crate::Helper;

/// The helper count this classification was proven against. A runtime that
/// grows a helper must extend [`helper_demand`] or [`STRUCTURAL_HELPERS`] and
/// raise this bound; [`verify_helper_coverage`] refuses to certify coverage
/// against an unexamined helper set.
pub const EXPECTED_HELPER_COUNT: u32 = 55;

/// Helpers that no opcode requests.
///
/// [`Helper::ConsumeFuel`] is emitted by the per-block fuel prologue, and
/// [`Helper::ResumeMode`] is emitted by the `Suspend` resume prologue after
/// [`Helper::ResumeValue`] succeeds. Opcode classification alone cannot reach
/// either of them.
pub const STRUCTURAL_HELPERS: &[Helper] = &[Helper::ConsumeFuel, Helper::ResumeMode];

/// How one opcode reaches the runtime.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HelperDemand {
    /// Lowered entirely in native code, with no runtime call.
    Inline,
    /// Lowered as a call to exactly one runtime helper.
    Call(Helper),
    /// Needs a runtime helper that does not yet exist in the helper table.
    ///
    /// Carries the intended C symbol name and the contract it must implement.
    /// [`verify_helper_coverage`] turns this into a concrete error that blocks
    /// E2.1 until the helper is added.
    Missing {
        /// The missing helper's C symbol name.
        name: &'static str,
        /// One-sentence semantic contract.
        contract: &'static str,
    },
}

/// The runtime helper an opcode lowers to, or [`HelperDemand::Inline`] when the
/// opcode needs no runtime call.
///
/// The match is exhaustive by construction: it names every variant of the
/// instruction algebra and has no wildcard arm.
#[must_use]
pub const fn helper_demand(instruction: Instruction) -> HelperDemand {
    match instruction {
        // Register moves, unconditional control flow, and the three frame
        // terminators are pure native lowerings.
        Instruction::Move { .. }
        | Instruction::Jump { .. }
        | Instruction::Return { .. }
        | Instruction::Throw { .. }
        | Instruction::Halt => HelperDemand::Inline,

        Instruction::LoadConst { .. } => HelperDemand::Call(Helper::LoadConstant),
        Instruction::Unary { .. } => HelperDemand::Call(Helper::Unary),
        Instruction::Binary { .. } => HelperDemand::Call(Helper::Binary),
        Instruction::CreateObject { .. } => HelperDemand::Call(Helper::CreateObject),
        Instruction::ToObject { .. } => HelperDemand::Call(Helper::ToObject),
        Instruction::LoadImportMeta { .. } => HelperDemand::Call(Helper::LoadImportMeta),
        Instruction::CreateArray { .. } => HelperDemand::Call(Helper::CreateArray),
        Instruction::CreateCell { .. } => HelperDemand::Call(Helper::CreateCell),
        Instruction::CreateClosure { .. } => HelperDemand::Call(Helper::CreateClosure),
        Instruction::GetProperty { .. } => HelperDemand::Call(Helper::GetProperty),
        Instruction::SetProperty { .. } => HelperDemand::Call(Helper::SetProperty),
        Instruction::DeleteProperty { .. } => HelperDemand::Call(Helper::DeleteProperty),
        Instruction::DefineAccessor { .. } => HelperDemand::Call(Helper::DefineAccessor),
        Instruction::DefineDataProperty { .. } => HelperDemand::Call(Helper::DefineDataProperty),
        Instruction::LoadOwnDescriptorSlot { .. } => {
            HelperDemand::Call(Helper::LoadOwnDescriptorSlot)
        }
        Instruction::DefineOwnDescriptorSlot { .. } => {
            HelperDemand::Call(Helper::DefineOwnDescriptorSlot)
        }
        Instruction::WithHasBinding { .. } => HelperDemand::Call(Helper::WithHasBinding),
        Instruction::Call { .. } => HelperDemand::Call(Helper::Call),
        Instruction::Construct { .. } => HelperDemand::Call(Helper::Construct),
        Instruction::ConstructWithNewTarget { .. } => {
            HelperDemand::Call(Helper::ConstructWithNewTarget)
        }
        Instruction::LoadGlobal { .. } => HelperDemand::Call(Helper::LoadGlobal),
        Instruction::StoreGlobal { .. } => HelperDemand::Call(Helper::StoreGlobal),
        Instruction::TypeOfGlobal { .. } => HelperDemand::Call(Helper::TypeOfGlobal),
        Instruction::LoadThis { .. } => HelperDemand::Call(Helper::LoadThis),
        Instruction::LoadArguments { .. } => HelperDemand::Call(Helper::LoadArguments),
        Instruction::LoadNewTarget { .. } => HelperDemand::Call(Helper::LoadNewTarget),
        Instruction::ArrayPush { .. } => HelperDemand::Call(Helper::ArrayPush),
        Instruction::ArrayExtend { .. } => HelperDemand::Call(Helper::ArrayExtend),
        Instruction::ObjectSpread { .. } => HelperDemand::Call(Helper::ObjectSpread),
        Instruction::SetPrototype { .. } => HelperDemand::Call(Helper::SetPrototype),
        Instruction::CreatePrivateName { .. } => HelperDemand::Call(Helper::CreatePrivateName),
        Instruction::CreateRegExp { .. } => HelperDemand::Call(Helper::CreateRegExp),
        Instruction::GetIterator { .. } => HelperDemand::Call(Helper::GetIterator),
        Instruction::IteratorNext { .. } => HelperDemand::Call(Helper::IteratorNext),
        Instruction::IteratorStep { .. } => HelperDemand::Call(Helper::IteratorStep),
        Instruction::IteratorResult { .. } => HelperDemand::Call(Helper::IteratorResult),
        Instruction::IteratorClose { .. } => HelperDemand::Call(Helper::IteratorClose),
        Instruction::RequireCloseResult { .. } => HelperDemand::Call(Helper::RequireCloseResult),
        Instruction::DisposeCapture { .. } => HelperDemand::Call(Helper::DisposeCapture),
        Instruction::SuppressError { .. } => HelperDemand::Call(Helper::SuppressError),
        Instruction::Import { .. } => HelperDemand::Call(Helper::Import),
        Instruction::ImportDynamic { .. } => HelperDemand::Call(Helper::ImportDynamic),
        Instruction::Export { .. } => HelperDemand::Call(Helper::Export),
        Instruction::GetSuper { .. } => HelperDemand::Call(Helper::GetSuper),
        Instruction::SetSuper { .. } => HelperDemand::Call(Helper::SetSuper),
        Instruction::ImportAttributes { .. } => HelperDemand::Call(Helper::ImportAttributes),
        Instruction::ImportDynamicAttributes { .. } => {
            HelperDemand::Call(Helper::ImportDynamicAttributes)
        }
        Instruction::CopyDataProperties { .. } => HelperDemand::Call(Helper::CopyDataProperties),
        Instruction::GetTemplateObject { .. } => HelperDemand::Call(Helper::GetTemplateObject),
        Instruction::RequireGlobalBinding { .. } => {
            HelperDemand::Call(Helper::RequireGlobalBinding)
        }
        Instruction::ThrowIntrinsicError { .. } => HelperDemand::Call(Helper::ThrowIntrinsicError),

        // Both conditional branches test the same runtime truthiness predicate,
        // differing only in the native branch polarity.
        Instruction::JumpIfTrue { .. } | Instruction::JumpIfFalse { .. } => {
            HelperDemand::Call(Helper::Truthy)
        }

        // Both suspension forms re-enter through the same resume-value read.
        Instruction::Suspend { .. } | Instruction::Await { .. } => {
            HelperDemand::Call(Helper::ResumeValue)
        }
    }
}

/// One instruction per opcode, in wire-tag order.
///
/// Payloads are arbitrary but structurally distinct, since coverage depends
/// only on which variant each entry selects. Keeping one entry per opcode makes
/// [`verify_helper_coverage`] a statement about the whole algebra rather than
/// about a sampled subset.
pub const ISA_REPRESENTATIVES: [Instruction; 60] = [
    Instruction::LoadConst {
        dst: Register::new(0),
        constant: ConstantId::new(0),
    },
    Instruction::Move {
        dst: Register::new(1),
        src: Register::new(2),
    },
    Instruction::Unary {
        dst: Register::new(3),
        op: UnaryOp::LogicalNot,
        operand: Register::new(4),
    },
    Instruction::Binary {
        dst: Register::new(5),
        op: BinaryOp::Add,
        left: Register::new(6),
        right: Register::new(7),
    },
    Instruction::CreateObject {
        dst: Register::new(8),
    },
    Instruction::ToObject {
        dst: Register::new(9),
        src: Register::new(10),
    },
    Instruction::LoadImportMeta {
        dst: Register::new(11),
    },
    Instruction::CreateArray {
        dst: Register::new(12),
    },
    Instruction::CreateCell {
        dst: Register::new(13),
    },
    Instruction::CreateClosure {
        dst: Register::new(14),
        function: FunctionId::new(0),
        captures: Register::new(15),
    },
    Instruction::GetProperty {
        dst: Register::new(16),
        object: Register::new(17),
        key: Register::new(18),
    },
    Instruction::SetProperty {
        object: Register::new(19),
        key: Register::new(20),
        value: Register::new(21),
    },
    Instruction::DeleteProperty {
        dst: Register::new(22),
        object: Register::new(23),
        key: Register::new(24),
    },
    Instruction::DefineAccessor {
        object: Register::new(25),
        key: Register::new(26),
        accessor: Register::new(27),
        kind: AccessorKind::Getter,
    },
    Instruction::DefineDataProperty {
        object: Register::new(28),
        key: Register::new(29),
        value: Register::new(30),
    },
    Instruction::LoadOwnDescriptorSlot {
        dst: Register::new(31),
        object: Register::new(32),
        key: Register::new(33),
        slot: DescriptorSlot::Value,
    },
    Instruction::DefineOwnDescriptorSlot {
        object: Register::new(34),
        key: Register::new(35),
        src: Register::new(36),
        slot: DescriptorSlot::Getter,
    },
    Instruction::WithHasBinding {
        dst: Register::new(37),
        object: Register::new(38),
        key: Register::new(39),
    },
    Instruction::Call {
        dst: Register::new(40),
        callee: Register::new(41),
        this_value: Register::new(42),
        arguments: Register::new(43),
    },
    Instruction::Construct {
        dst: Register::new(44),
        callee: Register::new(45),
        arguments: Register::new(46),
    },
    Instruction::ConstructWithNewTarget {
        dst: Register::new(47),
        callee: Register::new(48),
        new_target: Register::new(49),
        arguments: Register::new(50),
    },
    Instruction::LoadGlobal {
        dst: Register::new(51),
        name: ConstantId::new(1),
    },
    Instruction::StoreGlobal {
        name: ConstantId::new(2),
        value: Register::new(52),
    },
    Instruction::TypeOfGlobal {
        dst: Register::new(53),
        name: ConstantId::new(3),
    },
    Instruction::LoadThis {
        dst: Register::new(54),
    },
    Instruction::LoadArguments {
        dst: Register::new(55),
    },
    Instruction::LoadNewTarget {
        dst: Register::new(56),
    },
    Instruction::ArrayPush {
        array: Register::new(57),
        value: Register::new(58),
    },
    Instruction::ArrayExtend {
        array: Register::new(59),
        iterable: Register::new(60),
    },
    Instruction::ObjectSpread {
        target: Register::new(61),
        source: Register::new(62),
    },
    Instruction::SetPrototype {
        object: Register::new(63),
        prototype: Register::new(64),
    },
    Instruction::CreatePrivateName {
        dst: Register::new(65),
        description: ConstantId::new(4),
    },
    Instruction::CreateRegExp {
        dst: Register::new(66),
        pattern: ConstantId::new(5),
        flags: ConstantId::new(6),
    },
    Instruction::GetIterator {
        dst: Register::new(67),
        src: Register::new(68),
        kind: IteratorKind::Sync,
    },
    Instruction::IteratorNext {
        done: Register::new(69),
        value: Register::new(70),
        iterator: Register::new(71),
    },
    Instruction::IteratorStep {
        dst: Register::new(72),
        iterator: Register::new(73),
    },
    Instruction::IteratorResult {
        done: Register::new(74),
        value: Register::new(75),
        result: Register::new(76),
    },
    Instruction::IteratorClose {
        result: Register::new(77),
        called: Register::new(78),
        iterator: Register::new(79),
        mode: IteratorCloseMode::Propagate,
    },
    Instruction::RequireCloseResult {
        result: Register::new(80),
        called: Register::new(81),
    },
    Instruction::DisposeCapture {
        method: Register::new(82),
        kind: Register::new(83),
        src: Register::new(84),
        hint: DisposeHint::Sync,
    },
    Instruction::SuppressError {
        dst: Register::new(85),
        error: Register::new(86),
        suppressed: Register::new(87),
    },
    Instruction::Jump { target: Pc::new(0) },
    Instruction::JumpIfTrue {
        condition: Register::new(88),
        target: Pc::new(1),
    },
    Instruction::JumpIfFalse {
        condition: Register::new(89),
        target: Pc::new(2),
    },
    Instruction::Return {
        value: Register::new(90),
    },
    Instruction::Throw {
        value: Register::new(91),
    },
    Instruction::Suspend {
        dst: Register::new(92),
        src: Register::new(93),
        resume: Pc::new(3),
        mode: Register::new(94),
    },
    Instruction::Await {
        dst: Register::new(94),
        src: Register::new(95),
        resume: Pc::new(4),
    },
    Instruction::Import {
        dst: Register::new(96),
        specifier: ConstantId::new(7),
    },
    Instruction::ImportDynamic {
        dst: Register::new(97),
        specifier: Register::new(98),
    },
    Instruction::Export {
        name: ConstantId::new(8),
        src: Register::new(99),
    },
    Instruction::GetSuper {
        dst: Register::new(100),
        home: Register::new(101),
        receiver: Register::new(102),
        key: Register::new(103),
    },
    Instruction::SetSuper {
        home: Register::new(104),
        receiver: Register::new(105),
        key: Register::new(106),
        value: Register::new(107),
    },
    Instruction::ImportAttributes {
        dst: Register::new(108),
        specifier: ConstantId::new(9),
        attributes: Register::new(109),
    },
    Instruction::ImportDynamicAttributes {
        dst: Register::new(110),
        specifier: Register::new(111),
        attributes: Register::new(112),
    },
    Instruction::CopyDataProperties {
        target: Register::new(113),
        source: Register::new(114),
        excluded: Register::new(115),
    },
    Instruction::GetTemplateObject {
        dst: Register::new(116),
        cooked: Register::new(117),
        raw: Register::new(118),
    },
    Instruction::RequireGlobalBinding {
        name: ConstantId::new(10),
    },
    Instruction::ThrowIntrinsicError {
        kind: IntrinsicErrorKind::TypeError,
        message: ConstantId::new(11),
    },
    Instruction::Halt,
];

/// Why helper coverage could not be certified.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HelperCoverageError {
    /// The runtime declares a different number of helpers than this
    /// classification was proven against.
    HelperCountMismatch {
        /// The count the runtime reports.
        declared: u32,
        /// The count this module has classified.
        expected: u32,
    },
    /// An external index below the declared count maps to no helper, so the
    /// helper namespace has a hole.
    UnmappedIndex {
        /// The index that inverted to no helper.
        index: u32,
    },
    /// A helper's external index does not survive a round trip, so the
    /// namespace is not a bijection.
    IndexRoundTrip {
        /// The index used to recover the helper.
        index: u32,
        /// The index that helper reports for itself.
        reported: u32,
    },
    /// No opcode and no structural emitter reaches this helper, so lowering
    /// could never call it.
    UncoveredHelper {
        /// The unreachable helper.
        helper: Helper,
    },

    /// An opcode needs a runtime helper that has not been wired into the
    /// helper table, so lowering cannot be certified for E2.1.
    MissingHelper {
        /// The opcode that needs the helper.
        instruction: Instruction,
        /// The intended C symbol name.
        name: &'static str,
        /// The semantic contract the helper must satisfy.
        contract: &'static str,
    },
    /// Two representative entries select the same opcode, so the array does not
    /// cover the algebra it claims to.
    DuplicateRepresentative {
        /// The earlier entry's position.
        first: usize,
        /// The duplicate entry's position.
        second: usize,
    },
    /// A helper's signature does not begin with the shadow-frame pointer and
    /// end with the completion out-pointer.
    AbiShape {
        /// The offending helper.
        helper: Helper,
        /// Its declared parameter count.
        parameters: usize,
    },
}

impl core::fmt::Display for HelperCoverageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HelperCoverageError::HelperCountMismatch { declared, expected } => write!(
                f,
                "runtime declares {declared} helpers but {expected} are classified"
            ),
            HelperCoverageError::UnmappedIndex { index } => {
                write!(f, "helper external index {index} maps to no helper")
            }
            HelperCoverageError::IndexRoundTrip { index, reported } => {
                write!(f, "helper external index {index} round-trips to {reported}")
            }
            HelperCoverageError::UncoveredHelper { helper } => {
                write!(f, "no opcode or structural emitter reaches {helper:?}")
            }
            HelperCoverageError::MissingHelper {
                instruction,
                name,
                contract,
            } => {
                write!(f, "{instruction:?} needs missing helper {name}: {contract}")
            }
            HelperCoverageError::DuplicateRepresentative { first, second } => write!(
                f,
                "representative {second} repeats the opcode of representative {first}"
            ),
            HelperCoverageError::AbiShape { helper, parameters } => {
                write!(
                    f,
                    "{helper:?} has an unexpected ABI shape with {parameters} parameters"
                )
            }
        }
    }
}

impl std::error::Error for HelperCoverageError {}

/// Proves that lowering can reach every runtime helper, that the opcode
/// representatives cover the algebra without repetition, that the helper
/// external-name namespace is a bijection, and that every helper carries the
/// shadow-frame and completion pointers its ABI promises.
///
/// This is the E2.1 contract vector: it takes no input and depends on no
/// environment, so it certifies the same fact on every host.
pub fn verify_helper_coverage() -> Result<(), HelperCoverageError> {
    if HELPER_COUNT != EXPECTED_HELPER_COUNT {
        return Err(HelperCoverageError::HelperCountMismatch {
            declared: HELPER_COUNT,
            expected: EXPECTED_HELPER_COUNT,
        });
    }

    for (second, instruction) in ISA_REPRESENTATIVES.iter().enumerate() {
        let discriminant = core::mem::discriminant(instruction);
        for (first, earlier) in ISA_REPRESENTATIVES[..second].iter().enumerate() {
            if core::mem::discriminant(earlier) == discriminant {
                return Err(HelperCoverageError::DuplicateRepresentative { first, second });
            }
        }
    }

    // A 53-helper namespace fits two words; the count check above pins that.
    let mut reached: u64 = 0;
    for helper in STRUCTURAL_HELPERS {
        reached |= 1u64 << helper.external_index();
    }
    for instruction in &ISA_REPRESENTATIVES {
        match helper_demand(*instruction) {
            HelperDemand::Inline => {}
            HelperDemand::Call(helper) => {
                reached |= 1u64 << helper.external_index();
            }
            HelperDemand::Missing { name, contract } => {
                return Err(HelperCoverageError::MissingHelper {
                    instruction: *instruction,
                    name,
                    contract,
                });
            }
        }
    }

    for index in 0..HELPER_COUNT {
        let Some(helper) = Helper::from_external_index(index) else {
            return Err(HelperCoverageError::UnmappedIndex { index });
        };
        let reported = helper.external_index();
        if reported != index {
            return Err(HelperCoverageError::IndexRoundTrip { index, reported });
        }
        if reached & (1u64 << index) == 0 {
            return Err(HelperCoverageError::UncoveredHelper { helper });
        }

        let params = helper.param_types();
        // `Truthy` answers with a native `0`/`1` instead of writing a
        // completion, so it is the one helper without an out-pointer.
        let expected_shape = if matches!(helper, Helper::Truthy) {
            params.len() == 2
        } else {
            params.len() >= 2 && params[params.len() - 1] == types::I64
        };
        if !expected_shape || params[0] != types::I64 {
            return Err(HelperCoverageError::AbiShape {
                helper,
                parameters: params.len(),
            });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Rebuilds the reachable-helper set the way [`verify_helper_coverage`]
    /// does, but over a caller-supplied classification, so a test can withdraw
    /// one opcode's demand and observe the coverage failure.
    fn reachable_with(classify: impl Fn(Instruction) -> HelperDemand) -> Vec<Helper> {
        let mut helpers: Vec<Helper> = STRUCTURAL_HELPERS.to_vec();
        for instruction in &ISA_REPRESENTATIVES {
            if let HelperDemand::Call(helper) = classify(*instruction) {
                helpers.push(helper);
            }
        }
        helpers.sort_unstable();
        helpers.dedup();
        helpers
    }

    #[test]
    fn coverage_holds_for_the_shipped_classification() {
        assert_eq!(verify_helper_coverage(), Ok(()));
    }

    #[test]
    fn representatives_cover_every_opcode_exactly_once() {
        let mut discriminants: Vec<_> = ISA_REPRESENTATIVES
            .iter()
            .map(core::mem::discriminant)
            .collect();
        let total = discriminants.len();
        discriminants.dedup();
        assert_eq!(total, 60, "the algebra has 60 opcodes");
        assert_eq!(
            discriminants.len(),
            total,
            "representatives must not repeat an opcode"
        );
    }

    #[test]
    fn only_moves_control_flow_and_terminators_lower_inline() {
        let inline: Vec<Instruction> = ISA_REPRESENTATIVES
            .iter()
            .copied()
            .filter(|instruction| helper_demand(*instruction) == HelperDemand::Inline)
            .collect();
        assert_eq!(inline.len(), 5, "inline set changed: {inline:?}");
        for instruction in inline {
            assert!(
                matches!(
                    instruction,
                    Instruction::Move { .. }
                        | Instruction::Jump { .. }
                        | Instruction::Return { .. }
                        | Instruction::Throw { .. }
                        | Instruction::Halt
                ),
                "unexpected inline opcode {instruction:?}"
            );
        }
    }

    #[test]
    fn every_helper_calling_opcode_names_exactly_one_helper() {
        for instruction in &ISA_REPRESENTATIVES {
            match helper_demand(*instruction) {
                HelperDemand::Inline => {}
                HelperDemand::Call(helper) => {
                    assert!(
                        helper.external_index() < HELPER_COUNT,
                        "{instruction:?} names out-of-range helper {helper:?}"
                    );
                }
                HelperDemand::Missing { .. } => {}
            }
        }
    }

    #[test]
    fn no_current_opcode_has_a_missing_helper_demand() {
        for instruction in ISA_REPRESENTATIVES {
            assert!(
                !matches!(helper_demand(instruction), HelperDemand::Missing { .. }),
                "{instruction:?} still has a missing helper demand"
            );
        }
    }

    #[test]
    fn both_branch_polarities_share_the_truthiness_helper() {
        let truthy: Vec<Instruction> = ISA_REPRESENTATIVES
            .iter()
            .copied()
            .filter(|instruction| helper_demand(*instruction) == HelperDemand::Call(Helper::Truthy))
            .collect();
        assert_eq!(truthy.len(), 2, "expected two branch opcodes: {truthy:?}");
    }

    #[test]
    fn both_suspension_forms_share_the_resume_helper() {
        let resume: Vec<Instruction> = ISA_REPRESENTATIVES
            .iter()
            .copied()
            .filter(|instruction| {
                helper_demand(*instruction) == HelperDemand::Call(Helper::ResumeValue)
            })
            .collect();
        assert_eq!(
            resume.len(),
            2,
            "expected suspend and await to share a helper: {resume:?}"
        );
    }

    #[test]
    fn consume_fuel_and_resume_mode_are_the_helpers_no_opcode_requests() {
        let from_opcodes = reachable_with(helper_demand);
        let mut without_structural = from_opcodes.clone();
        without_structural.retain(|helper| !STRUCTURAL_HELPERS.contains(helper));
        assert_eq!(
            without_structural.len(),
            HELPER_COUNT as usize - STRUCTURAL_HELPERS.len(),
            "opcode-reachable helper count changed"
        );
        assert!(
            !without_structural.contains(&Helper::ConsumeFuel),
            "no opcode may request the fuel prologue helper"
        );
        assert!(
            !without_structural.contains(&Helper::ResumeMode),
            "no opcode may request the suspend resume-mode helper"
        );
        assert_eq!(from_opcodes.len(), HELPER_COUNT as usize);
    }

    #[test]
    fn withdrawing_a_helper_demand_loses_coverage() {
        // The adversary: a lowering that forgets the truthiness call and
        // pretends both branches are pure native code.
        let broken = reachable_with(|instruction| match instruction {
            Instruction::JumpIfTrue { .. } | Instruction::JumpIfFalse { .. } => {
                HelperDemand::Inline
            }
            other => helper_demand(other),
        });
        assert!(
            !broken.contains(&Helper::Truthy),
            "the mutation must drop the truthiness helper"
        );
        assert_eq!(broken.len(), HELPER_COUNT as usize - 1);
    }

    #[test]
    fn helper_external_indices_form_a_bijection() {
        for index in 0..HELPER_COUNT {
            let helper = Helper::from_external_index(index)
                .unwrap_or_else(|| panic!("index {index} maps to no helper"));
            assert_eq!(helper.external_index(), index);
        }
        assert_eq!(Helper::from_external_index(HELPER_COUNT), None);
    }

    #[test]
    fn helper_signatures_carry_frame_and_completion_pointers() {
        for index in 0..HELPER_COUNT {
            let helper = Helper::from_external_index(index).expect("helper index");
            let params = helper.param_types();
            assert!(params.len() >= 2, "{helper:?} takes too few parameters");
            assert_eq!(params[0], types::I64, "{helper:?} lacks a frame pointer");
            if matches!(helper, Helper::Truthy) {
                assert_eq!(params.len(), 2, "Truthy takes only frame and value");
            } else {
                assert_eq!(
                    params[params.len() - 1],
                    types::I64,
                    "{helper:?} lacks an out-pointer"
                );
            }
        }
    }
}
