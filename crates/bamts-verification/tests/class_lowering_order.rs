use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use bamts_compiler::emitter::transforms::ScriptTarget;
use bamts_compiler::emitter::transpile::transpile_text;
use bamts_compiler::emitter::{EmitFileNames, EmitOptions};
use bamts_compiler::source::{ScriptKind, SourceId};

struct FixtureDir(PathBuf);

impl FixtureDir {
    fn new() -> Self {
        // The process id and a process-wide counter keep parallel tests from
        // sharing a fixture directory name, which a clock reading could not.
        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "bamts-class-lowering-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).expect("create class lowering fixture directory");
        Self(path)
    }
}

impl Drop for FixtureDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn node() -> String {
    std::env::var("BAMTS_NODE24").unwrap_or_else(|_| "node".to_owned())
}

fn run_node(path: &Path) -> String {
    let output = Command::new(node())
        .arg(path)
        .output()
        .expect("execute Node 24");
    assert!(
        output.status.success(),
        "Node failed for {}: {}",
        path.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("Node stdout is UTF-8")
}

fn assert_node24() {
    let output = Command::new(node())
        .arg("--version")
        .output()
        .expect("query Node version");
    let version = String::from_utf8(output.stdout).expect("Node version is UTF-8");
    if std::env::var_os("BAMTS_ALLOW_NODE_COMPAT").is_some() {
        let major = version
            .trim_start_matches('v')
            .split('.')
            .next()
            .and_then(|value| value.parse::<u32>().ok())
            .expect("Node version has a major component");
        assert!(major >= 24, "Node 24 or later required, found {version}");
    } else {
        assert!(
            version.starts_with("v24."),
            "Node 24 required, found {version}"
        );
    }
}

fn lowered(source: &str) -> String {
    let output = transpile_text(
        SourceId::new(1),
        ScriptKind::TypeScript,
        Arc::from(source),
        &EmitOptions {
            target: ScriptTarget::Es2015,
            use_define_for_class_fields: Some(false),
            ..EmitOptions::default()
        },
        &EmitFileNames {
            source_name: Arc::from("input.ts"),
            js_file_name: Some(Arc::from("output.mjs")),
            declaration_file_name: None,
            source_root: None,
            ..EmitFileNames::default()
        },
    );
    assert!(
        output
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.is_warning()),
        "unexpected transpile diagnostics: {:?}",
        output.diagnostics
    );
    output
        .javascript
        .expect("transpile emits JavaScript")
        .code
        .to_string()
}

fn assert_native_and_lowered(source: &str, expected: &str) {
    assert_node24();
    let fixture = FixtureDir::new();
    let native = fixture.0.join("native.ts");
    let emitted = fixture.0.join("lowered.mjs");
    fs::write(&native, source).expect("write native TypeScript fixture");
    fs::write(&emitted, lowered(source)).expect("write lowered JavaScript fixture");
    let native_stdout = run_node(&native);
    let lowered_stdout = run_node(&emitted);
    assert_eq!(native_stdout, expected);
    assert_eq!(lowered_stdout, native_stdout);
}

#[test]
fn preserves_heritage_key_static_order_and_single_evaluation() {
    let source = r#"
const log = [];
let n = 0;
function heritage() { log.push('heritage'); return class {}; }
function key(tag) { log.push(tag); n++; return tag; }
class C extends heritage() {
  [key('method')]() {}
  static [key('first')] = (log.push('first-value'), 1);
  static { log.push('block'); }
  static [key('second')] = (log.push('second-value'), 2);
}
console.log(JSON.stringify([log, n, C.first, C.second]));
"#;
    assert_native_and_lowered(
        source,
        "[[\"heritage\",\"method\",\"first\",\"second\",\"first-value\",\"block\",\"second-value\"],3,1,2]\n",
    );
}

#[test]
fn preserves_recursive_super_class_expression_and_static_receivers() {
    let source = r#"
const writes = [];
function key() { writes.push('key'); return 'score'; }
function rhs() { writes.push('rhs'); return 3; }
class Base {
  constructor(value) { this.base = value; }
  static answer() { return this.name === 'Derived' ? 41 : 0; }
  static get score() { writes.push('get'); return this._score ?? 1; }
  static set score(value) { writes.push('set'); this._score = value; }
}
class Derived extends Base {
  field = this.base + 1;
  constructor(flag) { if (flag) super(1); else { super(2); } }
  static self = this;
  static {
    if (true) {
      super.score = 2;
      try {
        super[key()] += rhs();
        this.nested = this;
      } finally {
        this.done = true;
      }
    }
    this.total = super.answer() + 1;
  }
}
const A = consume(class { static x = 7; value = 8; });
function consume(value) { return value; }
console.log(JSON.stringify([
  new Derived(true).field,
  new Derived(false).field,
  Derived.self === Derived,
  Derived.total,
  Derived._score,
  writes,
  Derived.nested === Derived,
  Derived.done,
  A.x,
  new A().value,
  A.name
]));
"#;
    assert_native_and_lowered(
        source,
        "[2,3,true,42,5,[\"set\",\"key\",\"get\",\"rhs\",\"set\"],true,true,7,8,\"\"]\n",
    );
}

#[test]
fn preserves_default_name_forwarding_and_abrupt_super_completion() {
    let source = r#"
class Base { constructor(...args) { this.args = args; } }
const events = [];
class Forward extends Base { field = events.push('field'); }
class Throws extends Base {
  field = events.push('never');
  constructor() { throw new Error('stop'); super(); }
}
try { new Throws(); } catch { events.push('caught'); }
const value = new Forward(1, 2);
const Default = (class { static seen = 'ready'; });
console.log(JSON.stringify([value.args, events, Default.seen]));
"#;
    assert_native_and_lowered(source, "[[1,2],[\"caught\",\"field\"],\"ready\"]\n");
}
