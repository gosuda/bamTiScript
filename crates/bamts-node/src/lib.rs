//! Node-compatible host capabilities for BamTS.

#![deny(unsafe_code)]

mod timers;

use std::collections::BTreeMap;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

#[cfg(feature = "script-compiler")]
use std::sync::Arc;

#[cfg(feature = "script-compiler")]
use bamts_bytecode::{EcmaString, Program, Verified};
use bamts_runtime::Host;

/// Parent-to-AOT-child transport for the logical source entrypoint.
///
/// `initialize_aot_process_context` consumes this before publishing
/// `process.env`, so it is not observable to JavaScript. It supplies the
/// logical `argv[1]` slot only when the launch proof matches.
pub const AOT_ENTRYPOINT_ENV: &str = "BAMTS_AOT_ENTRYPOINT";
/// Parent-to-AOT-child launch proof paired with the private process argument.
///
/// `initialize_aot_process_context` compares the token against
/// `process_args[1]`; the executable path otherwise fills the logical
/// `argv[1]` slot.
pub const AOT_LAUNCH_TOKEN_ENV: &str = "BAMTS_AOT_LAUNCH_TOKEN";

/// Classic-script compiler capability for Node hosts.
#[cfg(feature = "script-compiler")]
#[derive(Default)]
pub struct ScriptCompiler;

#[cfg(feature = "script-compiler")]
impl bamts_runtime::CompileProvider for ScriptCompiler {
    fn compile_script(
        &mut self,
        source: bamts_runtime::ScriptSource<'_>,
    ) -> std::result::Result<Arc<Program<Verified>>, bamts_runtime::ScriptCompileError> {
        // Strict conversion preserves the exact name the caller supplied.
        // Lossy conversion would replace unpaired surrogates with U+FFFD,
        // causing diagnostics and module resolution to disagree with the
        // caller's intent.
        let resource_name = EcmaString::from_units(source.name)
            .to_utf8_strict()
            .map_err(|error| bamts_runtime::ScriptCompileError::IllFormedSource {
                unit_offset: error.unit_offset,
            })?;
        bamts_compiler::compile_classic_script(source.source, &resource_name)
            .map(Arc::new)
            .map_err(map_script_compile_error)
    }
}

#[cfg(feature = "script-compiler")]
fn map_script_compile_error(
    error: bamts_compiler::ScriptCompileError,
) -> bamts_runtime::ScriptCompileError {
    match error {
        bamts_compiler::ScriptCompileError::IllFormedSource { unit_offset } => {
            bamts_runtime::ScriptCompileError::IllFormedSource { unit_offset }
        }
        bamts_compiler::ScriptCompileError::Syntax {
            message,
            line,
            column,
        } => bamts_runtime::ScriptCompileError::Syntax {
            message,
            line,
            column,
        },
        bamts_compiler::ScriptCompileError::Unsupported {
            message,
            line,
            column,
        } => bamts_runtime::ScriptCompileError::Unsupported {
            message,
            line,
            column,
        },
        bamts_compiler::ScriptCompileError::Capacity { message } => {
            bamts_runtime::ScriptCompileError::Capacity { message }
        }
    }
}

/// Concrete Node-compatible capability state.
///
/// Environment and arguments are explicit rather than inherited from the
/// embedding process, keeping executions independent of the invoking machine.
pub struct NodeHost {
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    exit_code: Option<i32>,
    argv: Vec<String>,
    env: BTreeMap<String, String>,
    started: Instant,
    random_state: u64,
    compiler: Option<Box<dyn bamts_runtime::CompileProvider>>,
    timers: timers::NodeTimers,
}

impl Default for NodeHost {
    fn default() -> Self {
        Self::new()
    }
}

impl NodeHost {
    #[must_use]
    pub fn new() -> Self {
        Self {
            stdout: Vec::new(),
            stderr: Vec::new(),
            exit_code: None,
            argv: Vec::new(),
            env: BTreeMap::new(),
            started: Instant::now(),
            random_state: 0x6a09_e667_f3bc_c909,
            compiler: None,
            timers: timers::NodeTimers::new(),
        }
    }

    #[must_use]
    pub fn stdout(&self) -> &[u8] {
        &self.stdout
    }

    #[must_use]
    pub fn stderr(&self) -> &[u8] {
        &self.stderr
    }

    #[must_use]
    pub const fn exit_code(&self) -> Option<i32> {
        self.exit_code
    }

    #[must_use]
    pub const fn completion_exit_code(&self, runtime_exit_code: i32) -> i32 {
        match self.exit_code {
            Some(exit_code) => exit_code,
            None => runtime_exit_code,
        }
    }

    pub fn set_argv(&mut self, argv: impl IntoIterator<Item = String>) {
        self.argv = argv.into_iter().collect();
    }

    #[must_use]
    pub fn argv(&self) -> &[String] {
        &self.argv
    }

    #[must_use]
    pub fn env(&self, name: &str) -> Option<&str> {
        self.env.get(name).map(String::as_str)
    }

    pub fn set_env(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.env.insert(name.into(), value.into());
    }

    pub fn delete_env(&mut self, name: &str) -> bool {
        self.env.remove(name).is_some()
    }

    pub fn set_script_compiler(&mut self, compiler: Box<dyn bamts_runtime::CompileProvider>) {
        self.compiler = Some(compiler);
    }
}

impl Host for NodeHost {
    fn write_stdout(&mut self, bytes: &[u8]) {
        self.stdout.extend_from_slice(bytes);
    }

    fn write_stderr(&mut self, bytes: &[u8]) {
        self.stderr.extend_from_slice(bytes);
    }

    fn exit_code(&self) -> Option<i32> {
        self.exit_code
    }

    fn set_exit_code(&mut self, exit_code: i32) {
        self.exit_code = Some(exit_code);
    }

    fn argv(&self) -> &[String] {
        &self.argv
    }

    fn env(&self, name: &str) -> Option<&str> {
        self.env.get(name).map(String::as_str)
    }

    fn set_env(&mut self, name: &str, value: &str) {
        self.env.insert(name.to_owned(), value.to_owned());
    }

    fn delete_env(&mut self, name: &str) -> bool {
        self.env.remove(name).is_some()
    }

    fn now_ms(&mut self) -> u64 {
        let elapsed = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default();
        u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
    }

    fn monotonic_ns(&mut self) -> u64 {
        u64::try_from(self.started.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }

    fn random(&mut self) -> f64 {
        // xorshift64*: deterministic, non-cryptographic entropy for Math.random.
        let mut state = self.random_state;
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        self.random_state = state;
        let bits = state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 11;
        (bits as f64) * (1.0 / ((1_u64 << 53) as f64))
    }

    fn script_compiler(&mut self) -> Option<&mut (dyn bamts_runtime::CompileProvider + 'static)> {
        self.compiler.as_deref_mut()
    }

    fn timers(&mut self) -> Option<&mut (dyn bamts_runtime::TimerProvider + 'static)> {
        Some(&mut self.timers)
    }

    fn hash(&mut self, algorithm: &str, data: &[u8]) -> Option<Vec<u8>> {
        match algorithm.to_ascii_lowercase().replace('-', "").as_str() {
            "sha256" => Some(sha256(data).to_vec()),
            "sha512" => Some(sha512(data).to_vec()),
            _ => None,
        }
    }
}

fn sha256(data: &[u8]) -> [u8; 32] {
    const INITIAL: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = data.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    let mut state = INITIAL;
    for block in padded.chunks_exact(64) {
        let mut words = [0_u32; 64];
        for (word, bytes) in words[..16].iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes(bytes.try_into().expect("four bytes"));
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ (!e & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(choice)
                .wrapping_add(K[index])
                .wrapping_add(words[index]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }
    let mut digest = [0_u8; 32];
    for (chunk, value) in digest.chunks_exact_mut(4).zip(state) {
        chunk.copy_from_slice(&value.to_be_bytes());
    }
    digest
}

fn sha512(data: &[u8]) -> [u8; 64] {
    const INITIAL: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];
    const K: [u64; 80] = [
        0x428a2f98d728ae22,
        0x7137449123ef65cd,
        0xb5c0fbcfec4d3b2f,
        0xe9b5dba58189dbbc,
        0x3956c25bf348b538,
        0x59f111f1b605d019,
        0x923f82a4af194f9b,
        0xab1c5ed5da6d8118,
        0xd807aa98a3030242,
        0x12835b0145706fbe,
        0x243185be4ee4b28c,
        0x550c7dc3d5ffb4e2,
        0x72be5d74f27b896f,
        0x80deb1fe3b1696b1,
        0x9bdc06a725c71235,
        0xc19bf174cf692694,
        0xe49b69c19ef14ad2,
        0xefbe4786384f25e3,
        0x0fc19dc68b8cd5b5,
        0x240ca1cc77ac9c65,
        0x2de92c6f592b0275,
        0x4a7484aa6ea6e483,
        0x5cb0a9dcbd41fbd4,
        0x76f988da831153b5,
        0x983e5152ee66dfab,
        0xa831c66d2db43210,
        0xb00327c898fb213f,
        0xbf597fc7beef0ee4,
        0xc6e00bf33da88fc2,
        0xd5a79147930aa725,
        0x06ca6351e003826f,
        0x142929670a0e6e70,
        0x27b70a8546d22ffc,
        0x2e1b21385c26c926,
        0x4d2c6dfc5ac42aed,
        0x53380d139d95b3df,
        0x650a73548baf63de,
        0x766a0abb3c77b2a8,
        0x81c2c92e47edaee6,
        0x92722c851482353b,
        0xa2bfe8a14cf10364,
        0xa81a664bbc423001,
        0xc24b8b70d0f89791,
        0xc76c51a30654be30,
        0xd192e819d6ef5218,
        0xd69906245565a910,
        0xf40e35855771202a,
        0x106aa07032bbd1b8,
        0x19a4c116b8d2d0c8,
        0x1e376c085141ab53,
        0x2748774cdf8eeb99,
        0x34b0bcb5e19b48a8,
        0x391c0cb3c5c95a63,
        0x4ed8aa4ae3418acb,
        0x5b9cca4f7763e373,
        0x682e6ff3d6b2b8a3,
        0x748f82ee5defb2fc,
        0x78a5636f43172f60,
        0x84c87814a1f0ab72,
        0x8cc702081a6439ec,
        0x90befffa23631e28,
        0xa4506cebde82bde9,
        0xbef9a3f7b2c67915,
        0xc67178f2e372532b,
        0xca273eceea26619c,
        0xd186b8c721c0c207,
        0xeada7dd6cde0eb1e,
        0xf57d4f7fee6ed178,
        0x06f067aa72176fba,
        0x0a637dc5a2c898a6,
        0x113f9804bef90dae,
        0x1b710b35131c471b,
        0x28db77f523047d84,
        0x32caab7b40c72493,
        0x3c9ebe0a15c9bebc,
        0x431d67c49c100d4c,
        0x4cc5d4becb3e42b6,
        0x597f299cfc657e2a,
        0x5fcb6fab3ad6faec,
        0x6c44198c4a475817,
    ];
    let bit_len = (data.len() as u128).wrapping_mul(8);
    let mut padded = data.to_vec();
    padded.push(0x80);
    while padded.len() % 128 != 112 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    let mut state = INITIAL;
    for block in padded.chunks_exact(128) {
        let mut words = [0_u64; 80];
        for (word, bytes) in words[..16].iter_mut().zip(block.chunks_exact(8)) {
            *word = u64::from_be_bytes(bytes.try_into().expect("eight bytes"));
        }
        for index in 16..80 {
            let s0 = words[index - 15].rotate_right(1)
                ^ words[index - 15].rotate_right(8)
                ^ (words[index - 15] >> 7);
            let s1 = words[index - 2].rotate_right(19)
                ^ words[index - 2].rotate_right(61)
                ^ (words[index - 2] >> 6);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..80 {
            let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
            let choice = (e & f) ^ (!e & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(choice)
                .wrapping_add(K[index])
                .wrapping_add(words[index]);
            let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }
    let mut digest = [0_u8; 64];
    for (chunk, value) in digest.chunks_exact_mut(8).zip(state) {
        chunk.copy_from_slice(&value.to_be_bytes());
    }
    digest
}

#[cfg(feature = "aot-main")]
fn decode_aot_program(
    bytes: &[u8],
) -> Result<bamts_bytecode::Program<bamts_bytecode::Verified>, bamts_bytecode::ProgramLoadError> {
    bamts_bytecode::decode_verified_program(bytes, &bamts_bytecode::ProgramDecodeLimits::default())
}

#[cfg(all(feature = "aot-main", not(test)))]
fn run_aot_main() -> i32 {
    use bamts_native::linked_program;
    use bamts_runtime::{Limits, run_linked_program};

    let mut host = NodeHost::new();
    #[cfg(feature = "script-compiler")]
    host.set_script_compiler(Box::new(ScriptCompiler));
    let linked = match linked_program() {
        Ok(linked) => linked,
        Err(error) => {
            return finish_aot_process(
                &host,
                AotCompletion::Failure(AotMainFailure::Link(error.to_string())),
            );
        }
    };
    let program = match decode_aot_program(linked.bytecode()) {
        Ok(program) => program,
        Err(error) => {
            return finish_aot_process(
                &host,
                AotCompletion::Failure(AotMainFailure::Decode(error.to_string())),
            );
        }
    };
    if let Err(error) =
        initialize_aot_process_context(&mut host, std::env::args_os(), std::env::vars_os())
    {
        return finish_aot_process(
            &host,
            AotCompletion::Failure(AotMainFailure::Context(error)),
        );
    }
    let outcome = match run_linked_program(&program, &linked, &mut host, &Limits::program()) {
        Ok(outcome) => outcome,
        Err(error) => {
            return finish_aot_process(
                &host,
                AotCompletion::Failure(AotMainFailure::Runtime(error.to_string())),
            );
        }
    };
    finish_aot_process(&host, AotCompletion::Success(&outcome))
}

#[cfg(any(feature = "aot-main", test))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum AotMainFailure {
    Link(String),
    Decode(String),
    Context(AotProcessContextError),
    Runtime(String),
}

#[cfg(any(feature = "aot-main", test))]
impl std::fmt::Display for AotMainFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Link(detail) => write!(formatter, "aot link: {detail}"),
            Self::Decode(detail) => write!(formatter, "aot decode: {detail}"),
            Self::Context(AotProcessContextError::Argument) => {
                formatter.write_str("aot context argument")
            }
            Self::Context(AotProcessContextError::EnvironmentName) => {
                formatter.write_str("aot context environment name")
            }
            Self::Context(AotProcessContextError::EnvironmentValue) => {
                formatter.write_str("aot context environment value")
            }
            Self::Runtime(detail) => write!(formatter, "aot runtime: {detail}"),
        }
    }
}

#[cfg(any(feature = "aot-main", test))]
enum AotCompletion<'a> {
    Success(&'a bamts_runtime::ExecutionOutcome),
    Failure(AotMainFailure),
}

/// Emits buffered host output for every completion and flushes both streams.
#[cfg(any(feature = "aot-main", test))]
fn write_aot_completion(
    host: &NodeHost,
    completion: AotCompletion<'_>,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<i32> {
    stdout.write_all(host.stdout())?;
    let (exit_code, failure) = match completion {
        AotCompletion::Success(outcome) => {
            stdout.write_all(&outcome.stdout)?;
            (host.completion_exit_code(outcome.exit_code), None)
        }
        AotCompletion::Failure(error) => (1, Some(error)),
    };
    stdout.flush()?;
    stderr.write_all(host.stderr())?;
    if let Some(error) = failure {
        writeln!(stderr, "bamts: {error}")?;
    }
    stderr.flush()?;
    Ok(exit_code)
}

#[cfg(all(feature = "aot-main", not(test)))]
fn finish_aot_process(host: &NodeHost, completion: AotCompletion<'_>) -> i32 {
    let mut stdout = std::io::stdout().lock();
    let mut stderr = std::io::stderr().lock();
    write_aot_completion(host, completion, &mut stdout, &mut stderr).unwrap_or(1)
}

/// C process entry for a linked BamTS AOT image.
#[cfg(all(feature = "aot-main", not(test)))]
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    run_aot_main()
}

#[cfg(any(feature = "aot-main", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AotProcessContextError {
    Argument,
    EnvironmentName,
    EnvironmentValue,
}

/// Populate an AOT host from an explicit process snapshot.
///
/// The leading `bamts` mirrors the JIT driver's argv convention, so the
/// executable always maps to logical `argv[1]`. A matching launch token
/// (compared against the private `process_args[1]`) authenticates a
/// parent-launched child: the token slot is skipped and `AOT_ENTRYPOINT_ENV`
/// fills that `argv[1]` position, falling back to the executable path when no
/// entrypoint was transported. Without a match, direct execution keeps the
/// executable at `argv[1]` and drops any inherited transport variables.
/// Conversion is all-or-nothing so an invalid OS string cannot leave a
/// partially populated host.
#[cfg(any(feature = "aot-main", test))]
fn initialize_aot_process_context(
    host: &mut NodeHost,
    args: impl IntoIterator<Item = std::ffi::OsString>,
    environment: impl IntoIterator<Item = (std::ffi::OsString, std::ffi::OsString)>,
) -> Result<(), AotProcessContextError> {
    let mut process_args = Vec::new();
    for argument in args {
        process_args.push(
            argument
                .into_string()
                .map_err(|_| AotProcessContextError::Argument)?,
        );
    }

    let mut env = BTreeMap::new();
    for (name, value) in environment {
        let name = name
            .into_string()
            .map_err(|_| AotProcessContextError::EnvironmentName)?;
        let value = value
            .into_string()
            .map_err(|_| AotProcessContextError::EnvironmentValue)?;
        env.insert(name, value);
    }

    let entrypoint_env = env.remove(AOT_ENTRYPOINT_ENV);
    let launch_token_env = env.remove(AOT_LAUNCH_TOKEN_ENV);

    // A matching launch token authenticates a parent-launched AOT child: the
    // token is supplied both as `AOT_LAUNCH_TOKEN_ENV` and as the private
    // `process_args[1]`. On a match the token slot is consumed so it never
    // reaches JavaScript, regardless of whether an entrypoint was transported.
    let launch_authenticated = match (launch_token_env.as_ref(), process_args.get(1)) {
        (Some(token), Some(argument)) => argument == token,
        _ => false,
    };

    let (entrypoint, first_program_argument) = if launch_authenticated {
        let entrypoint = entrypoint_env.or_else(|| process_args.first().cloned());
        (entrypoint, 2)
    } else {
        (process_args.first().cloned(), 1)
    };
    let mut argv = vec!["bamts".to_owned()];
    if let Some(entrypoint) = entrypoint {
        argv.push(entrypoint);
    }
    argv.extend(process_args.into_iter().skip(first_program_argument));

    host.argv = argv;
    host.env = env;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    struct FlushProbe {
        bytes: Vec<u8>,
        flushes: usize,
        flush_error: Option<std::io::ErrorKind>,
    }

    impl std::io::Write for FlushProbe {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.flushes += 1;
            match self.flush_error {
                Some(kind) => Err(std::io::Error::from(kind)),
                None => Ok(()),
            }
        }
    }

    #[cfg(feature = "aot-main")]
    #[test]
    fn linked_descriptor_decodes_whole_program_and_tuple_entry() {
        use bamts_bytecode::{
            Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction,
            Module, ModuleId, Program, ProgramModule,
        };

        let module = |name: &str| ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![Constant::String(EcmaString::encode(name))],
                vec![Function::new(
                    None,
                    0,
                    0,
                    0,
                    FunctionFlags::default(),
                    vec![Instruction::Halt],
                    Vec::new(),
                )],
                FunctionId::new(0),
            )
            .verify()
            .expect("descriptor test module verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        };
        let program = Program::link(
            vec![module("dependency"), module("entry")],
            ModuleId::new(1),
        )
        .expect("descriptor test program links");

        let decoded = decode_aot_program(&program.encode()).expect("descriptor program decodes");

        assert_eq!(decoded.entry(), ModuleId::new(1));
        assert_eq!(decoded.modules().len(), 2);
        assert!(
            decoded
                .modules()
                .iter()
                .all(|module| module.code().entry() == FunctionId::new(0))
        );
    }

    fn hex(bytes: &[u8]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut text = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            text.push(char::from(DIGITS[usize::from(byte >> 4)]));
            text.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
        }
        text
    }

    #[test]
    fn capabilities_capture_bytes_and_mutate_process_state() {
        let mut host = NodeHost::new();
        Host::write_stdout(&mut host, b"out");
        Host::write_stderr(&mut host, b"err");
        Host::set_exit_code(&mut host, 23);
        host.set_argv(["bamts".to_owned(), "file.ts".to_owned()]);
        Host::set_env(&mut host, "NODE_ENV", "test");
        assert_eq!(host.stdout(), b"out");
        assert_eq!(host.stderr(), b"err");
        assert_eq!(host.exit_code(), Some(23));
        assert_eq!(host.argv(), ["bamts", "file.ts"]);
        assert_eq!(host.env("NODE_ENV"), Some("test"));
        assert!(Host::delete_env(&mut host, "NODE_ENV"));
        assert_eq!(host.env("NODE_ENV"), None);
    }

    #[test]
    fn sha2_matches_standard_vectors() {
        let mut host = NodeHost::new();
        assert_eq!(
            hex(&Host::hash(&mut host, "sha-256", b"abc").unwrap()),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(&Host::hash(&mut host, "SHA512", b"abc").unwrap()),
            "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
        );
        assert_eq!(Host::hash(&mut host, "md5", b"abc"), None);
    }

    #[test]
    fn aot_process_context_uses_jit_argv_normalization() {
        let mut host = NodeHost::new();
        initialize_aot_process_context(
            &mut host,
            [
                std::ffi::OsString::from("/tmp/program"),
                std::ffi::OsString::from("--flag"),
            ],
            [
                (
                    std::ffi::OsString::from("ZED"),
                    std::ffi::OsString::from("last"),
                ),
                (
                    std::ffi::OsString::from("ALPHA"),
                    std::ffi::OsString::from("first"),
                ),
            ],
        )
        .unwrap();

        assert_eq!(host.argv(), ["bamts", "/tmp/program", "--flag"]);
        assert_eq!(host.env("ALPHA"), Some("first"));
        assert_eq!(host.env("ZED"), Some("last"));
    }

    #[test]
    fn aot_process_context_replaces_the_executable_with_a_private_entrypoint() {
        let mut host = NodeHost::new();
        initialize_aot_process_context(
            &mut host,
            [
                std::ffi::OsString::from("/tmp/cache/aot-image"),
                std::ffi::OsString::from("launch-7"),
                std::ffi::OsString::from("--flag"),
            ],
            [
                (
                    std::ffi::OsString::from(AOT_ENTRYPOINT_ENV),
                    std::ffi::OsString::from("src/main.ts"),
                ),
                (
                    std::ffi::OsString::from(AOT_LAUNCH_TOKEN_ENV),
                    std::ffi::OsString::from("launch-7"),
                ),
                (
                    std::ffi::OsString::from("VISIBLE"),
                    std::ffi::OsString::from("value"),
                ),
            ],
        )
        .unwrap();

        assert_eq!(host.argv(), ["bamts", "src/main.ts", "--flag"]);
        assert_eq!(host.env("BAMTS_AOT_ENTRYPOINT"), None);
        assert_eq!(host.env("VISIBLE"), Some("value"));
    }

    #[test]
    fn aot_process_context_ignores_inherited_transport_without_launch_proof() {
        let mut host = NodeHost::new();
        initialize_aot_process_context(
            &mut host,
            [
                std::ffi::OsString::from("/tmp/direct-aot-image"),
                std::ffi::OsString::from("--flag"),
            ],
            [
                (
                    std::ffi::OsString::from(AOT_ENTRYPOINT_ENV),
                    std::ffi::OsString::from("stale.ts"),
                ),
                (
                    std::ffi::OsString::from(AOT_LAUNCH_TOKEN_ENV),
                    std::ffi::OsString::from("stale-token"),
                ),
            ],
        )
        .unwrap();

        assert_eq!(host.argv(), ["bamts", "/tmp/direct-aot-image", "--flag"]);
        assert_eq!(host.env(AOT_ENTRYPOINT_ENV), None);
        assert_eq!(host.env(AOT_LAUNCH_TOKEN_ENV), None);
    }

    #[test]
    fn aot_process_context_consumes_authenticated_token_without_entrypoint() {
        let mut host = NodeHost::new();
        initialize_aot_process_context(
            &mut host,
            [
                std::ffi::OsString::from("/tmp/cache/aot-image"),
                std::ffi::OsString::from("launch-7"),
                std::ffi::OsString::from("--flag"),
                std::ffi::OsString::from("extra.ts"),
            ],
            [
                (
                    std::ffi::OsString::from(AOT_LAUNCH_TOKEN_ENV),
                    std::ffi::OsString::from("launch-7"),
                ),
                (
                    std::ffi::OsString::from("VISIBLE"),
                    std::ffi::OsString::from("value"),
                ),
            ],
        )
        .unwrap();

        // A matching token still consumes the token slot (argv[1] stays the
        // executable and the token never appears) even with no transported
        // entrypoint; transport env keys remain hidden.
        assert_eq!(
            host.argv(),
            ["bamts", "/tmp/cache/aot-image", "--flag", "extra.ts"]
        );
        assert_eq!(host.env(AOT_LAUNCH_TOKEN_ENV), None);
        assert_eq!(host.env(AOT_ENTRYPOINT_ENV), None);
        assert_eq!(host.env("VISIBLE"), Some("value"));
    }

    #[test]
    fn aot_runtime_failure_emits_host_stderr_and_stable_error() {
        let mut host = NodeHost::new();
        Host::write_stdout(&mut host, b"before failure");
        Host::write_stderr(&mut host, b"host diagnostic\n");
        let mut stdout = FlushProbe {
            bytes: Vec::new(),
            flushes: 0,
            flush_error: None,
        };
        let mut stderr = Vec::new();

        let exit_code = write_aot_completion(
            &host,
            AotCompletion::Failure(AotMainFailure::Runtime(
                "uncaught TypeError: boom".to_owned(),
            )),
            &mut stdout,
            &mut stderr,
        )
        .expect("completion writes");

        assert_eq!(exit_code, 1);
        assert_eq!(stdout.bytes, b"before failure");
        assert_eq!(stdout.flushes, 1);
        assert_eq!(
            stderr,
            b"host diagnostic\nbamts: aot runtime: uncaught TypeError: boom\n"
        );
    }

    #[test]
    fn aot_failure_labels_are_stable() {
        assert_eq!(
            AotMainFailure::Link("link failed".to_owned()).to_string(),
            "aot link: link failed"
        );
        assert_eq!(
            AotMainFailure::Decode("bad image".to_owned()).to_string(),
            "aot decode: bad image"
        );
        assert_eq!(
            AotMainFailure::Context(AotProcessContextError::Argument).to_string(),
            "aot context argument"
        );
    }

    #[test]
    fn aot_exit_code_prefers_host_zero() {
        let mut host = NodeHost::new();
        Host::set_exit_code(&mut host, 0);
        let outcome = bamts_runtime::ExecutionOutcome {
            stdout: Vec::new(),
            exit_code: 7,
        };
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let exit_code = write_aot_completion(
            &host,
            AotCompletion::Success(&outcome),
            &mut stdout,
            &mut stderr,
        )
        .expect("completion writes");

        assert_eq!(exit_code, 0);
    }

    #[test]
    fn aot_success_writes_host_and_runtime_output() {
        let mut host = NodeHost::new();
        Host::write_stdout(&mut host, b"host stdout");
        Host::write_stderr(&mut host, b"host stderr");
        let outcome = bamts_runtime::ExecutionOutcome {
            stdout: b"runtime stdout".to_vec(),
            exit_code: 7,
        };
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let exit_code = write_aot_completion(
            &host,
            AotCompletion::Success(&outcome),
            &mut stdout,
            &mut stderr,
        )
        .expect("completion writes");

        assert_eq!(exit_code, 7);
        assert_eq!(stdout, b"host stdoutruntime stdout");
        assert_eq!(stderr, b"host stderr");

        Host::set_exit_code(&mut host, 11);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let exit_code = write_aot_completion(
            &host,
            AotCompletion::Success(&outcome),
            &mut stdout,
            &mut stderr,
        )
        .expect("completion writes");

        assert_eq!(exit_code, 11);
        assert_eq!(stdout, b"host stdoutruntime stdout");
        assert_eq!(stderr, b"host stderr");
    }

    #[test]
    fn aot_completion_flushes_trailing_stdout_without_a_newline() {
        let mut host = NodeHost::new();
        Host::write_stdout(&mut host, b"trailing host output");
        let outcome = bamts_runtime::ExecutionOutcome {
            stdout: b" and runtime output".to_vec(),
            exit_code: 0,
        };
        let mut stdout = FlushProbe {
            bytes: Vec::new(),
            flushes: 0,
            flush_error: None,
        };
        let mut stderr = Vec::new();

        let exit_code = write_aot_completion(
            &host,
            AotCompletion::Success(&outcome),
            &mut stdout,
            &mut stderr,
        )
        .expect("completion writes");

        assert_eq!(exit_code, 0);
        assert_eq!(stdout.bytes, b"trailing host output and runtime output");
        assert_eq!(stdout.flushes, 1);
    }

    #[test]
    fn aot_completion_propagates_stdout_flush_failure() {
        let host = NodeHost::new();
        let outcome = bamts_runtime::ExecutionOutcome {
            stdout: Vec::new(),
            exit_code: 0,
        };
        let mut stdout = FlushProbe {
            bytes: Vec::new(),
            flushes: 0,
            flush_error: Some(std::io::ErrorKind::BrokenPipe),
        };
        let mut stderr = Vec::new();

        let error = write_aot_completion(
            &host,
            AotCompletion::Success(&outcome),
            &mut stdout,
            &mut stderr,
        )
        .expect_err("stdout flush failure is reported");

        assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe);
        assert_eq!(stdout.flushes, 1);
    }

    #[cfg(unix)]
    #[test]
    fn aot_process_context_rejects_non_unicode_without_mutating_host() {
        use std::os::unix::ffi::OsStringExt;

        let mut host = NodeHost::new();
        let error = initialize_aot_process_context(
            &mut host,
            [std::ffi::OsString::from_vec(vec![0xff])],
            [(
                std::ffi::OsString::from("SAFE"),
                std::ffi::OsString::from("value"),
            )],
        )
        .unwrap_err();

        assert_eq!(error, AotProcessContextError::Argument);
        assert!(host.argv().is_empty());
        assert_eq!(host.env("SAFE"), None);
    }

    #[test]
    fn clocks_and_random_are_capabilities() {
        let mut host = NodeHost::new();
        assert!(Host::now_ms(&mut host) > 0);
        let first = Host::monotonic_ns(&mut host);
        let second = Host::monotonic_ns(&mut host);
        assert!(second >= first);
        let random = Host::random(&mut host);
        assert!((0.0..1.0).contains(&random));
    }

    #[cfg(unix)]
    #[test]
    fn aot_process_context_rejects_non_unicode_environment_without_mutating_host() {
        use std::os::unix::ffi::OsStringExt;

        let mut host = NodeHost::new();
        let error = initialize_aot_process_context(
            &mut host,
            [std::ffi::OsString::from("/tmp/program")],
            [(
                std::ffi::OsString::from("SAFE"),
                std::ffi::OsString::from_vec(vec![0xff]),
            )],
        )
        .unwrap_err();

        assert_eq!(error, AotProcessContextError::EnvironmentValue);
        assert!(host.argv().is_empty());
        assert_eq!(host.env("SAFE"), None);
    }

    #[cfg(feature = "script-compiler")]
    #[test]
    fn compile_script_passes_exact_resource_name_to_compiler() {
        use bamts_bytecode::Constant;
        use bamts_runtime::{CompileProvider, ScriptSource};

        // A non-ASCII name proves the UTF-16 → UTF-8 path preserves every
        // code point the caller supplied, rather than substituting or
        // dropping characters.
        let name: Vec<u16> = "café-σ-script.js".encode_utf16().collect();
        let source: Vec<u16> = "1 + 1".encode_utf16().collect();

        let program = ScriptCompiler
            .compile_script(ScriptSource {
                source: &source,
                name: &name,
            })
            .expect("script compiles");

        let module = &program.modules()[program.entry().get() as usize];
        match &module.code().constants()[module.name().get() as usize] {
            Constant::String(stored) => {
                assert_eq!(
                    stored
                        .to_utf8_strict()
                        .expect("module name is valid UTF-16"),
                    "café-σ-script.js",
                );
            }
            other => panic!("module name is a string constant, got {other:?}"),
        }
    }

    #[cfg(feature = "script-compiler")]
    #[test]
    fn compile_script_rejects_ill_formed_resource_name() {
        use bamts_runtime::{CompileProvider, ScriptCompileError, ScriptSource};

        // An unpaired high surrogate must not be silently replaced with
        // U+FFFD; the caller should learn the name was ill-formed.
        let name = [0xD800_u16];
        let source: Vec<u16> = "1 + 1".encode_utf16().collect();

        let error = ScriptCompiler
            .compile_script(ScriptSource {
                source: &source,
                name: &name,
            })
            .unwrap_err();

        assert_eq!(
            error,
            ScriptCompileError::IllFormedSource { unit_offset: 0 }
        );
    }
}

#[cfg(test)]
mod timer_tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn real_timers_expire_in_deadline_order_through_one_delay_queue() {
        let mut host = NodeHost::new();
        let timers = Host::timers(&mut host).expect("timer capability is always present");

        // The later-deadline timer is scheduled first to prove ordering comes
        // from the deadline, not insertion order.
        let late = timers.schedule(1, 12).expect("schedule id 1");
        let early = timers.schedule(2, 4).expect("schedule id 2");
        assert!(early <= late, "smaller delay yields an earlier deadline");
        assert!(timers.has_pending());

        let first = timers
            .wait_expired(&bamts_runtime::CancellationToken::new())
            .expect("wait")
            .expect("a wakeup");
        let second = timers
            .wait_expired(&bamts_runtime::CancellationToken::new())
            .expect("wait")
            .expect("a wakeup");
        assert_eq!(first.id, 2, "the earlier deadline fires first");
        assert_eq!(second.id, 1);
        assert_eq!(first.deadline_ms, early);
        assert_eq!(second.deadline_ms, late);

        assert!(!timers.has_pending());
        assert!(
            timers
                .wait_expired(&bamts_runtime::CancellationToken::new())
                .expect("wait")
                .is_none(),
            "an empty pending set never blocks"
        );
    }

    #[test]
    fn cancellation_removes_exactly_the_target_id() {
        let mut host = NodeHost::new();
        let timers = Host::timers(&mut host).unwrap();

        timers.schedule(10, 20).expect("schedule id 10");
        timers.schedule(11, 4).expect("schedule id 11");

        assert!(timers.cancel(10).expect("cancel"), "an armed timer cancels");
        assert!(
            !timers.cancel(10).expect("cancel"),
            "a second cancel of the same id is false"
        );
        assert!(
            !timers.cancel(999).expect("cancel"),
            "an unknown id cancels to false"
        );

        let wakeup = timers
            .wait_expired(&bamts_runtime::CancellationToken::new())
            .expect("wait")
            .expect("a wakeup");
        assert_eq!(wakeup.id, 11, "only the surviving timer fires");
        assert!(!timers.has_pending());
        assert!(
            timers
                .wait_expired(&bamts_runtime::CancellationToken::new())
                .expect("wait")
                .is_none()
        );
    }

    #[test]
    fn expiry_that_races_a_cancel_is_dropped_as_stale() {
        let mut host = NodeHost::new();
        let timers = Host::timers(&mut host).unwrap();

        timers.schedule(7, 1).expect("schedule id 7");
        // Let the worker fire and queue the wakeup while the caller has not yet
        // polled it, then cancel: the caller-side pending set is authoritative.
        std::thread::sleep(Duration::from_millis(40));
        assert!(
            timers.cancel(7).expect("cancel"),
            "still pending from the caller's view until polled"
        );

        let mut output = Vec::new();
        timers.poll_expired(&mut output).expect("poll");
        assert!(output.is_empty(), "a cancelled id is never delivered");
        assert!(!timers.has_pending());
        assert!(
            timers
                .wait_expired(&bamts_runtime::CancellationToken::new())
                .expect("wait")
                .is_none()
        );
    }

    #[test]
    fn rearmed_timer_drops_stale_wakeup_from_previous_arming() {
        let mut host = NodeHost::new();
        let timers = Host::timers(&mut host).unwrap();

        let _first_deadline = timers.schedule(7, 1).expect("schedule id 7 (first)");
        // Let the worker fire and queue the wakeup while the caller has not yet
        // polled it.
        std::thread::sleep(Duration::from_millis(40));

        // Re-arm id 7 with a much longer delay before polling the expired wakeup.
        let _second_deadline = timers.schedule(7, 1000).expect("schedule id 7 (re-arm)");

        let mut output = Vec::new();
        timers.poll_expired(&mut output).expect("poll");
        assert!(
            output.is_empty(),
            "stale wakeup from previous arming must be dropped on re-arm"
        );
        assert!(
            timers.has_pending(),
            "re-armed timer 7 must remain pending for its new deadline"
        );
    }

    #[test]
    fn worker_is_lazy_and_shuts_down_cleanly_on_drop() {
        let mut host = NodeHost::new();
        assert!(
            !host.timers.worker_active(),
            "no worker thread before the first schedule"
        );

        // Merely returning the capability must not spawn the worker.
        let _ = Host::timers(&mut host);
        assert!(
            !host.timers.worker_active(),
            "returning the capability is not a schedule"
        );

        Host::timers(&mut host)
            .unwrap()
            .schedule(1, 1)
            .expect("schedule id 1");
        assert!(
            host.timers.worker_active(),
            "the worker starts lazily on first schedule"
        );

        // Dropping the host drops the worker handle, which closes the command
        // channel and joins the thread even with a still-armed timer. A hang or
        // panic here fails the test.
        drop(host);
    }

    #[test]
    fn constructs_and_runs_inside_an_ambient_tokio_runtime_without_panic() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_time()
            .build()
            .expect("ambient runtime builds");
        let _guard = runtime.enter();

        // With an ambient Tokio runtime on this thread, the provider must still
        // spawn its own dedicated worker thread/runtime and never `block_on`
        // here, so none of these operations panic.
        let mut host = NodeHost::new();
        let timers = Host::timers(&mut host).unwrap();
        let deadline = timers
            .schedule(1, 2)
            .expect("schedule under ambient runtime");
        assert!(deadline >= 2);
        let wakeup = timers
            .wait_expired(&bamts_runtime::CancellationToken::new())
            .expect("wait")
            .expect("a wakeup");
        assert_eq!(wakeup.id, 1);
        assert!(!timers.has_pending());
    }
}
