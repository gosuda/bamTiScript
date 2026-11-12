//! Bytecode verifier co-extension (E1.2) for ISA tags 52..=58.
//!
//! Every opcode [`crate::isa`] adds is checked here for constant type,
//! register/constant/PC bounds, operand aliasing, and control-flow
//! successors. An extension instruction that fails any check keeps its
//! module `Unverified`, so invalid bytecode cannot reach execution.
//!
//! # Integration
//!
//! The crate root is the sole consumer: `verify_instruction` converts each
//! pasted `Instruction` arm (same field names as [`crate::isa::Instruction`])
//! and calls [`verify_extension`], then maps [`Error`] onto
//! `crate::VerifyError`. Every [`Kind`] has an identical-field
//! `VerifyErrorKind` counterpart. Definite initialization, stack depth, and
//! CFG completion are function-wide properties the crate-root passes own via
//! the forwarded `visit_reads` / `visit_writes` / `visit_successors`, so no
//! whole-function verifier lives here.

use crate::isa::Instruction;
use crate::{Constant, ConstantId, FunctionId, Pc, Register};

/// A structural failure of one extension opcode, located at a function and PC.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Error {
    pub function: Option<FunctionId>,
    pub instruction: Option<Pc>,
    pub kind: Kind,
}

/// Checks owned by this co-extension. Every variant has a crate-root
/// `VerifyErrorKind` counterpart with identical fields.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kind {
    RegisterOutOfBounds {
        register: Register,
        register_count: u32,
    },
    JumpOutOfBounds {
        target: u32,
        instruction_count: usize,
    },
    ConstantOutOfBounds {
        constant: ConstantId,
        constant_count: usize,
    },
    StringConstantExpected {
        constant: ConstantId,
    },
    /// `CopyDataProperties` `target` aliases `source` or `excluded`, so the
    /// copy would read and mutate one object through two operands.
    AliasedCopyDataProperties {
        register: Register,
    },
}

/// Per-instruction bounds, constant-type, alias, and CFG checks for one
/// extension opcode. Definite initialization is a function-wide property the
/// crate-root witness adds on top.
///
/// # Errors
///
/// Returns the first structural violation on this opcode.
pub fn verify_extension(
    function_index: usize,
    pc: usize,
    instruction: Instruction,
    register_count: u32,
    constants: &[Constant],
    instruction_count: usize,
) -> Result<(), Error> {
    let check_register = |register: Register| -> Result<(), Error> {
        if register.get() >= register_count {
            Err(instruction_error(
                function_index,
                pc,
                Kind::RegisterOutOfBounds {
                    register,
                    register_count,
                },
            ))
        } else {
            Ok(())
        }
    };
    let check_string_constant = |constant: ConstantId| -> Result<(), Error> {
        if constant.get() as usize >= constants.len() {
            return Err(instruction_error(
                function_index,
                pc,
                Kind::ConstantOutOfBounds {
                    constant,
                    constant_count: constants.len(),
                },
            ));
        }
        if matches!(constants[constant.get() as usize], Constant::String(_)) {
            Ok(())
        } else {
            Err(instruction_error(
                function_index,
                pc,
                Kind::StringConstantExpected { constant },
            ))
        }
    };

    match instruction {
        Instruction::GetSuper {
            dst,
            home,
            receiver,
            key,
        } => {
            check_register(dst)?;
            check_register(home)?;
            check_register(receiver)?;
            check_register(key)?;
        }
        Instruction::SetSuper {
            home,
            receiver,
            key,
            value,
        } => {
            check_register(home)?;
            check_register(receiver)?;
            check_register(key)?;
            check_register(value)?;
        }
        Instruction::ImportAttributes {
            dst,
            specifier,
            attributes,
        } => {
            check_register(dst)?;
            check_string_constant(specifier)?;
            check_register(attributes)?;
        }
        Instruction::ImportDynamicAttributes {
            dst,
            specifier,
            attributes,
        } => {
            check_register(dst)?;
            check_register(specifier)?;
            check_register(attributes)?;
        }
        Instruction::CopyDataProperties {
            target,
            source,
            excluded,
        } => {
            check_register(target)?;
            check_register(source)?;
            check_register(excluded)?;
            if target == source || target == excluded {
                return Err(instruction_error(
                    function_index,
                    pc,
                    Kind::AliasedCopyDataProperties { register: target },
                ));
            }
        }
        Instruction::GetTemplateObject { dst, cooked, raw } => {
            check_register(dst)?;
            check_register(cooked)?;
            check_register(raw)?;
        }
        Instruction::RequireGlobalBinding { name } => check_string_constant(name)?,
    }

    let mut successor_error = None;
    instruction.visit_successors(pc as u32, |successor| {
        if successor_error.is_none() && successor.get() as usize >= instruction_count {
            successor_error = Some(instruction_error(
                function_index,
                pc,
                Kind::JumpOutOfBounds {
                    target: successor.get(),
                    instruction_count,
                },
            ));
        }
    });
    if let Some(error) = successor_error {
        return Err(error);
    }
    Ok(())
}

fn instruction_error(function: usize, pc: usize, kind: Kind) -> Error {
    Error {
        function: Some(FunctionId::new(function as u32)),
        instruction: Some(Pc::new(pc as u32)),
        kind,
    }
}

#[cfg(test)]
mod tests {
    use super::{Kind, verify_extension};
    use crate::isa::Instruction;
    use crate::{Constant, ConstantId, EcmaString, Register};

    fn strings(names: &[&str]) -> Vec<Constant> {
        names
            .iter()
            .map(|name| Constant::String(EcmaString::encode(name)))
            .collect()
    }

    #[test]
    fn every_extension_opcode_rejects_an_out_of_bounds_register_operand() {
        let constants = strings(&["./data.json"]);
        let out = Register::new(99);
        let ok = Register::new(0);
        let cases = [
            Instruction::GetSuper {
                dst: out,
                home: ok,
                receiver: ok,
                key: ok,
            },
            Instruction::GetSuper {
                dst: ok,
                home: out,
                receiver: ok,
                key: ok,
            },
            Instruction::GetSuper {
                dst: ok,
                home: ok,
                receiver: out,
                key: ok,
            },
            Instruction::GetSuper {
                dst: ok,
                home: ok,
                receiver: ok,
                key: out,
            },
            Instruction::SetSuper {
                home: out,
                receiver: ok,
                key: ok,
                value: ok,
            },
            Instruction::SetSuper {
                home: ok,
                receiver: out,
                key: ok,
                value: ok,
            },
            Instruction::SetSuper {
                home: ok,
                receiver: ok,
                key: out,
                value: ok,
            },
            Instruction::SetSuper {
                home: ok,
                receiver: ok,
                key: ok,
                value: out,
            },
            Instruction::ImportAttributes {
                dst: out,
                specifier: ConstantId::new(0),
                attributes: ok,
            },
            Instruction::ImportAttributes {
                dst: ok,
                specifier: ConstantId::new(0),
                attributes: out,
            },
            Instruction::ImportDynamicAttributes {
                dst: out,
                specifier: ok,
                attributes: ok,
            },
            Instruction::ImportDynamicAttributes {
                dst: ok,
                specifier: out,
                attributes: ok,
            },
            Instruction::ImportDynamicAttributes {
                dst: ok,
                specifier: ok,
                attributes: out,
            },
            Instruction::CopyDataProperties {
                target: out,
                source: Register::new(1),
                excluded: Register::new(2),
            },
            Instruction::CopyDataProperties {
                target: ok,
                source: out,
                excluded: Register::new(2),
            },
            Instruction::CopyDataProperties {
                target: ok,
                source: Register::new(1),
                excluded: out,
            },
            Instruction::GetTemplateObject {
                dst: out,
                cooked: ok,
                raw: ok,
            },
            Instruction::GetTemplateObject {
                dst: ok,
                cooked: out,
                raw: ok,
            },
            Instruction::GetTemplateObject {
                dst: ok,
                cooked: ok,
                raw: out,
            },
        ];
        for instruction in cases {
            let error = verify_extension(0, 0, instruction, 4, &constants, 2)
                .expect_err("register 99 is outside a 4-register file");
            assert!(
                matches!(
                    error.kind,
                    Kind::RegisterOutOfBounds { register, register_count: 4 }
                        if register.get() == 99
                ),
                "every operand slot must be bounds-checked: {instruction:?}"
            );
        }
    }

    #[test]
    fn import_attributes_requires_an_in_bounds_string_specifier() {
        let constants = vec![Constant::Int32(1)];
        let not_a_string = verify_extension(
            0,
            0,
            Instruction::ImportAttributes {
                dst: Register::new(0),
                specifier: ConstantId::new(0),
                attributes: Register::new(1),
            },
            2,
            &constants,
            2,
        )
        .expect_err("Int32 is not a module specifier");
        assert!(matches!(
            not_a_string.kind,
            Kind::StringConstantExpected { constant } if constant.get() == 0
        ));

        let out_of_bounds = verify_extension(
            0,
            0,
            Instruction::ImportAttributes {
                dst: Register::new(0),
                specifier: ConstantId::new(3),
                attributes: Register::new(1),
            },
            2,
            &constants,
            2,
        )
        .expect_err("constant 3 of 1");
        assert!(matches!(
            out_of_bounds.kind,
            Kind::ConstantOutOfBounds {
                constant,
                constant_count: 1
            } if constant.get() == 3
        ));

        let valid = strings(&["./data.json"]);
        verify_extension(
            0,
            0,
            Instruction::ImportAttributes {
                dst: Register::new(0),
                specifier: ConstantId::new(0),
                attributes: Register::new(1),
            },
            2,
            &valid,
            2,
        )
        .expect("a string specifier verifies");
    }

    #[test]
    fn require_global_binding_requires_an_in_bounds_string_name() {
        let check = |constants: &[Constant], name: u32| {
            verify_extension(
                0,
                0,
                Instruction::RequireGlobalBinding {
                    name: ConstantId::new(name),
                },
                1,
                constants,
                2,
            )
        };
        assert!(matches!(
            check(&[Constant::Int32(1)], 0).expect_err("Int32 is not a name").kind,
            Kind::StringConstantExpected { constant } if constant.get() == 0
        ));
        assert!(matches!(
            check(&strings(&["x"]), 2).expect_err("constant 2 of 1").kind,
            Kind::ConstantOutOfBounds { constant, constant_count: 1 } if constant.get() == 2
        ));
        check(&strings(&["x"]), 0).expect("a string name verifies");
    }

    #[test]
    fn copy_data_properties_rejects_target_aliasing_source_or_excluded() {
        let constants = strings(&[]);
        let aliases_source = verify_extension(
            0,
            0,
            Instruction::CopyDataProperties {
                target: Register::new(1),
                source: Register::new(1),
                excluded: Register::new(2),
            },
            3,
            &constants,
            2,
        )
        .expect_err("target == source");
        assert!(matches!(
            aliases_source.kind,
            Kind::AliasedCopyDataProperties { register } if register.get() == 1
        ));

        let aliases_excluded = verify_extension(
            0,
            0,
            Instruction::CopyDataProperties {
                target: Register::new(2),
                source: Register::new(1),
                excluded: Register::new(2),
            },
            3,
            &constants,
            2,
        )
        .expect_err("target == excluded");
        assert!(matches!(
            aliases_excluded.kind,
            Kind::AliasedCopyDataProperties { register } if register.get() == 2
        ));

        verify_extension(
            0,
            0,
            Instruction::CopyDataProperties {
                target: Register::new(0),
                source: Register::new(1),
                excluded: Register::new(2),
            },
            3,
            &constants,
            2,
        )
        .expect("three distinct registers verify");
    }

    #[test]
    fn mutating_a_distinct_copy_into_an_alias_fails_the_contract_gate() {
        let constants = strings(&[]);
        let baseline = Instruction::CopyDataProperties {
            target: Register::new(0),
            source: Register::new(1),
            excluded: Register::new(2),
        };
        verify_extension(0, 0, baseline, 3, &constants, 2).expect("baseline verifies");
        let mutated = Instruction::CopyDataProperties {
            target: Register::new(1),
            source: Register::new(1),
            excluded: Register::new(2),
        };
        assert!(
            verify_extension(0, 0, mutated, 3, &constants, 2).is_err(),
            "collapsing target onto source must fail, or the alias check is inert"
        );
    }
}
