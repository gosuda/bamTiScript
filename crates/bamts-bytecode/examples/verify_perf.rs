use std::hint::black_box;
use std::time::{Duration, Instant};

use bamts_bytecode::{
    Constant, ConstantId, ExceptionHandler, Function, FunctionFlags, FunctionId, Instruction,
    Module, Pc, Register,
};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(
        args.len(),
        5,
        "usage: verify_perf <straight|reverse|branches|handlers> <instructions> <registers> <iterations>"
    );
    let instructions: u32 = args[2].parse().expect("instruction count is a u32");
    let registers: u32 = args[3].parse().expect("register count is a u32");
    let iterations: u32 = args[4].parse().expect("iteration count is a u32");
    assert!(instructions >= 4 && registers >= 4 && iterations != 0);
    let input = workload(&args[1], instructions, registers);
    let expected = input.clone().verify().expect("warmup verifies");
    let expected_bytes = expected.encode();
    let expected_certificate = expected.certificate(FunctionId::new(0)).unwrap();
    assert_eq!(
        expected_certificate.instruction_count(),
        instructions as usize
    );
    let mut fact_digest = 0xcbf29ce484222325u64;
    for pc in 0..instructions {
        assert_eq!(
            expected_certificate.initialized_before(Pc::new(pc), Register::new(0)),
            Some(true)
        );
        assert_eq!(
            expected_certificate.initialized_before(Pc::new(pc), Register::new(registers - 1)),
            Some(false)
        );
        for register in 0..registers {
            let initialized = expected_certificate
                .initialized_before(Pc::new(pc), Register::new(register))
                .expect("queried certificate coordinate is in bounds");
            fact_digest = (fact_digest ^ u64::from(initialized)).wrapping_mul(0x100000001b3);
        }
    }

    let mut elapsed = Duration::ZERO;
    for _ in 0..iterations {
        let module = input.clone();
        let started = Instant::now();
        let verified = black_box(module).verify().expect("measured input verifies");
        elapsed += started.elapsed();
        assert_eq!(verified.encode(), expected_bytes);
        assert_eq!(
            verified.certificate(FunctionId::new(0)).unwrap(),
            expected_certificate
        );
        black_box(verified);
    }
    let digest = expected_bytes
        .iter()
        .fold(0xcbf29ce484222325u64, |hash, byte| {
            (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
        });
    println!(
        "case={} instructions={instructions} registers={registers} iterations={iterations} failures=0 total_ns={} ns_per_verify={} wire_digest={digest:016x} fact_digest={fact_digest:016x}",
        args[1],
        elapsed.as_nanos(),
        elapsed.as_nanos() / u128::from(iterations),
    );
}

fn workload(name: &str, instructions: u32, registers: u32) -> Module {
    let mut handlers = Vec::new();
    let mut code = Vec::with_capacity(instructions as usize);
    match name {
        "straight" => {
            code.resize(
                instructions as usize - 1,
                Instruction::LoadConst {
                    dst: Register::new(1),
                    constant: ConstantId::new(0),
                },
            );
            code.push(Instruction::Return {
                value: Register::new(0),
            });
        }
        "reverse" | "handlers" => {
            code.push(Instruction::Jump {
                target: Pc::new(instructions - 1),
            });
            code.push(Instruction::Return {
                value: Register::new(0),
            });
            for pc in 2..instructions {
                code.push(Instruction::Jump {
                    target: Pc::new(pc - 1),
                });
            }
            if name == "handlers" {
                for depth in 0..32.min(instructions / 2) {
                    handlers.push(ExceptionHandler {
                        start: Pc::new(depth),
                        end: Pc::new(instructions - depth),
                        handler: Pc::new(1),
                        catch_register: Register::new(1),
                    });
                }
            }
        }
        "branches" => {
            for pc in 0..instructions - 1 {
                code.push(if pc % 3 == 0 && pc + 2 < instructions {
                    Instruction::JumpIfTrue {
                        condition: Register::new(0),
                        target: Pc::new(pc + 2),
                    }
                } else {
                    Instruction::LoadConst {
                        dst: Register::new(1),
                        constant: ConstantId::new(0),
                    }
                });
            }
            code.push(Instruction::Return {
                value: Register::new(0),
            });
        }
        _ => panic!("unknown workload {name}"),
    }
    Module::new(
        vec![Constant::Int32(42)],
        vec![Function::new(
            None,
            0,
            1,
            registers,
            FunctionFlags::default(),
            code,
            handlers,
        )],
        FunctionId::new(0),
    )
}
