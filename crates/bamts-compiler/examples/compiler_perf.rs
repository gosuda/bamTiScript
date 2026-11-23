use std::env;
use std::fmt::Write as _;
use std::hint::black_box;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use bamts_compiler::checker::{PropertyType, TypeTable};
use bamts_compiler::pipeline::{FrontendMode, compile_program_frontend};
use bamts_compiler::program::ProgramLoader;
use bamts_compiler::project::{ProjectConfig, ProjectRoot};
use bamts_compiler::source::{ScriptKind, SourceId, SourceText};
use bamts_compiler::telemetry::{Phase, Telemetry, TelemetryCollector};
use bamts_compiler::{parser, scanner};

fn main() {
    let arguments: Vec<_> = env::args().skip(1).collect();
    let [workload, input, repetitions] = arguments.as_slice() else {
        panic!(
            "usage: compiler_perf <lookup|parse|program> <width|declarations|entrypoint> <repetitions>"
        );
    };
    let repetitions = positive(repetitions);
    match workload.as_str() {
        "lookup" => lookup(positive(input), repetitions),
        "parse" => parse(positive(input), repetitions),
        "program" => program(Path::new(input), repetitions),
        _ => panic!("unknown workload {workload:?}"),
    }
}

fn positive(value: &str) -> usize {
    let value = value.parse().expect("count must be an integer");
    assert!(value > 0, "count must be positive");
    value
}

fn lookup(width: usize, repetitions: usize) {
    let mut table = TypeTable::new();
    let names: Vec<_> = (0..width).map(|index| format!("p{index:06}")).collect();
    let types: Vec<_> = (0..width)
        .map(|index| table.number_literal(&index.to_string()))
        .collect();
    let object = table.object_type(
        names
            .iter()
            .zip(&types)
            .rev()
            .map(|(name, type_id)| PropertyType::new(name.as_str(), false, *type_id))
            .collect(),
    );
    // The rolling digest can cancel, so validate every member before timing.
    for (name, expected_type) in names.iter().zip(&types) {
        assert_eq!(
            table.property_type(object, name.as_str()),
            Some(*expected_type),
            "property type for {name}"
        );
        assert_eq!(
            table.read_property_type(object, name.as_str()),
            Some(*expected_type),
            "read property type for {name}"
        );
    }
    let started = Instant::now();
    let mut checksum = 0u64;
    for index in 0..repetitions {
        let name = black_box(names[index % width].as_str());
        let raw = black_box(&mut table)
            .property_type(black_box(object), name)
            .expect("property exists");
        let read = black_box(&mut table)
            .read_property_type(black_box(object), name)
            .expect("property exists");
        checksum = checksum.rotate_left(5) ^ u64::from(raw.get());
        checksum = checksum.rotate_left(5) ^ u64::from(read.get());
    }
    let elapsed = started.elapsed();
    let expected = (0..repetitions).fold(0u64, |digest, index| {
        let type_id = u64::from(types[index % width].get());
        let digest = digest.rotate_left(5) ^ type_id;
        digest.rotate_left(5) ^ type_id
    });
    assert_eq!(checksum, expected);
    println!(
        "{{\"workload\":\"lookup\",\"width\":{width},\"operations\":{},\"elapsed_ns\":{},\"checksum\":{checksum}}}",
        2 * repetitions,
        elapsed.as_nanos(),
    );
}

fn parse(declarations: usize, repetitions: usize) {
    let mut text = String::new();
    for index in 0..declarations {
        writeln!(text, "const item{index}: number = {index};").expect("write to string");
    }
    let bytes = text.len();
    let source = Arc::new(SourceText::new(text).expect("source fits the compiler budget"));
    let collector = TelemetryCollector::start();
    let started = Instant::now();
    let mut checksum = 0usize;
    let mut tokens = 0usize;
    for _ in 0..repetitions {
        let scanned = Telemetry::measure(Phase::Scan, || {
            scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::clone(&source),
            )
        });
        tokens += scanned.product().tokens().len();
        let parsed = Telemetry::measure(Phase::Parse, || parser::parse(scanned));
        assert!(
            parsed.diagnostics().is_empty(),
            "{:?}",
            parsed.diagnostics()
        );
        assert_eq!(parsed.product().statements().len(), declarations);
        checksum += black_box(parsed.product().statements().len());
        black_box(parsed);
    }
    let elapsed = started.elapsed();
    let phases = collector.snapshot();
    assert_eq!(checksum, declarations * repetitions);
    println!(
        "{{\"workload\":\"parse\",\"bytes\":{bytes},\"operations\":{repetitions},\"tokens\":{tokens},\"elapsed_ns\":{},\"scan_ns\":{},\"parse_ns\":{},\"checksum\":{checksum}}}",
        elapsed.as_nanos(),
        phases.scan.as_nanos(),
        phases.parse.as_nanos(),
    );
}

fn program(entrypoint: &Path, repetitions: usize) {
    let entrypoint = entrypoint.canonicalize().expect("entrypoint exists");
    let root = ProjectRoot::new(entrypoint.parent().expect("entrypoint has a parent"))
        .expect("entrypoint has an absolute parent");
    let config = ProjectConfig::parse(&root, root.path().join("tsconfig.json"), "{}")
        .expect("empty project configuration is valid");
    let program = ProgramLoader::new(&root, config.options())
        .expect("project root exists")
        .load(&entrypoint)
        .expect("program loads");
    let collector = TelemetryCollector::start();
    let started = Instant::now();
    let mut checksum = 0usize;
    for _ in 0..repetitions {
        let output = compile_program_frontend(black_box(&program), FrontendMode::Check);
        assert_eq!(output.modules().len(), program.modules().len());
        for module in output.modules() {
            assert!(!module.has_errors(), "{:?}", module.diagnostics());
            checksum += black_box(module.semantic_model().symbols().len());
        }
        black_box(output);
    }
    let elapsed = started.elapsed();
    let phases = collector.snapshot();
    println!(
        "{{\"workload\":\"program\",\"modules\":{},\"operations\":{repetitions},\"elapsed_ns\":{},\"scan_ns\":{},\"parse_ns\":{},\"check_ns\":{},\"total_ns\":{},\"checksum\":{checksum}}}",
        program.modules().len(),
        elapsed.as_nanos(),
        phases.scan.as_nanos(),
        phases.parse.as_nanos(),
        phases.check.as_nanos(),
        phases.total.as_nanos(),
    );
}
