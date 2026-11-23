use super::*;

// Keep a global fixed-point solver as an independent scheduling oracle.
fn reference_definite_initialization(function: &Function) -> Result<Certificate, VerifyError> {
    let register_count = function.register_count;
    let mut facts = vec![RegisterSet::full(register_count); function.code.len()];
    facts[0] = RegisterSet::empty(register_count);
    facts[0].insert_prefix(function.entry_initialized());
    loop {
        let mut changed = false;
        for (pc, instruction) in function.code.iter().copied().enumerate() {
            let mut after = facts[pc].clone();
            instruction.visit_writes(|write| after.insert(write));
            instruction.visit_successors(pc as u32, |successor| {
                changed |= facts[successor.get() as usize].intersect(&after);
            });
        }
        for handler in &function.handlers {
            let mut contribution = RegisterSet::full(register_count);
            for fact in &facts[handler.start.get() as usize..handler.end.get() as usize] {
                contribution.intersect(fact);
            }
            contribution.insert(handler.catch_register);
            changed |= facts[handler.handler.get() as usize].intersect(&contribution);
        }
        if !changed {
            break;
        }
    }
    for (pc, instruction) in function.code.iter().copied().enumerate() {
        let mut missing = None;
        instruction.visit_reads(|register| {
            if missing.is_none() && !facts[pc].contains(register) {
                missing = Some(register);
            }
        });
        if let Some(register) = missing {
            return Err(instruction_error(
                0,
                pc,
                VerifyErrorKind::ReadBeforeWrite { register },
            ));
        }
    }
    Ok(Certificate {
        register_count,
        facts,
    })
}

fn handler_cases(instruction_count: u32) -> Vec<Vec<ExceptionHandler>> {
    let mut cases = vec![Vec::new()];
    for start in 0..instruction_count {
        for end in start + 1..=instruction_count {
            for target in 0..instruction_count {
                for catch in 0..2 {
                    cases.push(vec![ExceptionHandler {
                        start: Pc::new(start),
                        end: Pc::new(end),
                        handler: Pc::new(target),
                        catch_register: Register::new(catch),
                    }]);
                }
            }
        }
    }
    if instruction_count > 1 {
        let outer = ExceptionHandler {
            start: Pc::new(0),
            end: Pc::new(instruction_count),
            handler: Pc::new(0),
            catch_register: Register::new(0),
        };
        let inner = ExceptionHandler {
            start: Pc::new(1),
            handler: Pc::new(1),
            catch_register: Register::new(1),
            ..outer
        };
        cases.push(vec![outer, inner]);
        cases.push(vec![inner, outer]);
        cases.push(vec![outer, outer]);
    }
    cases
}

fn instructions_at(pc: u32, count: u32) -> Vec<Instruction> {
    let mut instructions = vec![
        Instruction::Halt,
        Instruction::Return {
            value: Register::new(0),
        },
        Instruction::Return {
            value: Register::new(1),
        },
    ];
    for target in 0..count {
        instructions.push(Instruction::Jump {
            target: Pc::new(target),
        });
        instructions.push(Instruction::Await {
            dst: Register::new(1),
            src: Register::new(0),
            resume: Pc::new(target),
        });
        if pc + 1 < count {
            instructions.push(Instruction::JumpIfTrue {
                condition: Register::new(0),
                target: Pc::new(target),
            });
        }
    }
    if pc + 1 < count {
        for register in 0..2 {
            instructions.push(Instruction::LoadConst {
                dst: Register::new(register),
                constant: ConstantId::new(0),
            });
            instructions.push(Instruction::Move {
                dst: Register::new(register),
                src: Register::new(1 - register),
            });
        }
    }
    instructions
}

fn compare_graphs(
    code: &mut Vec<Instruction>,
    instruction_count: u32,
    handlers: &[Vec<ExceptionHandler>],
) -> usize {
    if code.len() < instruction_count as usize {
        return instructions_at(code.len() as u32, instruction_count)
            .into_iter()
            .map(|instruction| {
                code.push(instruction);
                let compared = compare_graphs(code, instruction_count, handlers);
                code.pop();
                compared
            })
            .sum();
    }
    let mut compared = 0;
    for initialized in 0..=2 {
        for handlers in handlers {
            let function = Function::new(
                None,
                0,
                initialized,
                2,
                FunctionFlags::default(),
                code.clone(),
                handlers.clone(),
            );
            assert_eq!(
                definite_initialization(0, &function),
                reference_definite_initialization(&function),
                "{function:?}"
            );
            compared += 1;
        }
    }
    compared
}

#[test]
fn solver_matches_fixed_point_on_small_control_flow_graphs() {
    let mut compared = 0;
    for instruction_count in 1..=3 {
        compared += compare_graphs(
            &mut Vec::new(),
            instruction_count,
            &handler_cases(instruction_count),
        );
    }
    assert!(compared > 250_000);
}

#[test]
fn solver_preserves_unreachable_facts_and_word_boundaries() {
    for register_count in [0, 1, 63, 64, 65, 127, 128, 129] {
        for initialized in [0, register_count] {
            let mut code = vec![Instruction::Halt];
            code.extend((1..16).map(|pc| Instruction::Jump {
                target: Pc::new(if pc == 15 { 1 } else { pc + 1 }),
            }));
            let function = Function::new(
                None,
                0,
                initialized,
                register_count,
                FunctionFlags::default(),
                code,
                Vec::new(),
            );
            let certificate = definite_initialization(0, &function).unwrap();
            assert_eq!(
                certificate,
                reference_definite_initialization(&function).unwrap()
            );
            for register in 0..register_count {
                assert_eq!(
                    certificate.initialized_before(Pc::new(1), Register::new(register)),
                    Some(true)
                );
            }
        }
    }
}

#[test]
fn solver_propagates_a_long_backward_chain() {
    let mut code = vec![Instruction::Jump {
        target: Pc::new(1023),
    }];
    code.push(Instruction::Return {
        value: Register::new(0),
    });
    code.extend((2..1024).map(|pc| Instruction::Jump {
        target: Pc::new(pc - 1),
    }));
    let module = Module::new(
        Vec::new(),
        vec![Function::new(
            None,
            0,
            1,
            65,
            FunctionFlags::default(),
            code,
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .unwrap();
    let certificate = module.certificate(FunctionId::new(0)).unwrap();
    for pc in 0..1024 {
        assert_eq!(
            certificate.initialized_before(Pc::new(pc), Register::new(0)),
            Some(true)
        );
        assert_eq!(
            certificate.initialized_before(Pc::new(pc), Register::new(64)),
            Some(false)
        );
    }
}
