use std::error::Error;
use std::io::{self, Write};
use std::path::Path;
use std::time::Instant;

use bamts::compiler::telemetry::TelemetryCollector;

fn main() -> Result<(), Box<dyn Error>> {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let (profile, path) = match arguments.as_slice() {
        [path] => (false, path),
        [flag, path] if flag == "--profile" => (true, path),
        _ => return Err("usage: run_perf [--profile] <source.ts>".into()),
    };
    let collector = profile.then(TelemetryCollector::start);
    let started = Instant::now();
    let executable = bamts::compile_source_file(Path::new(path))?;
    let compiled = started.elapsed();
    let mut host = bamts::node::NodeHost::new();
    let started = Instant::now();
    let outcome = bamts::runtime::run(
        executable.wire(),
        &mut host,
        &bamts::runtime::Limits::program(),
    )?;
    let executed = started.elapsed();
    if outcome.exit_code != 0 || host.completion_exit_code(outcome.exit_code) != 0 {
        return Err("program returned a nonzero exit status".into());
    }
    io::stdout().lock().write_all(host.stdout())?;
    if let Some(collector) = collector {
        let phases = collector.snapshot();
        eprintln!(
            "compile_ns={} scan_ns={} parse_ns={} check_ns={} frontend_ns={} run_ns={} modules={}",
            compiled.as_nanos(),
            phases.scan.as_nanos(),
            phases.parse.as_nanos(),
            phases.check.as_nanos(),
            phases.total.as_nanos(),
            executed.as_nanos(),
            executable.wire().modules().len(),
        );
    }
    Ok(())
}
