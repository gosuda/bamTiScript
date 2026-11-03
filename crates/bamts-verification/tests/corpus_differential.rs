use std::{fs, path::Path, process};

use bamts_verification::corpus::{
    BamtsRunner, CaseSpec, CorpusFailure, CorpusStage, DigestAlgorithm, ExecutionMode, NodeOracle,
    OracleOutcome, PINNED_CASE_IDS, Provenance, TASK_106_SYNC_CASE_IDS, TASK_107_NODE_CASE_IDS,
    load_corpus, run_corpus_worker_from_env,
};
use sha2::{Digest, Sha256};

/// The repository's pinned `tsc`, launched through `node` because the
/// `node_modules/.bin/tsc` shim is a shell script that Windows cannot run.
fn tsc_command(root: &Path) -> process::Command {
    let mut command = process::Command::new("node");
    command.arg(root.join("node_modules/typescript/bin/tsc"));
    command
}

fn local_test_provenance(root: &Path, source_dir: &str) -> Provenance {
    fn collect(dir: &Path, prefix: &str, records: &mut Vec<(String, Vec<u8>)>) {
        for entry in fs::read_dir(dir).expect("read source_dir") {
            let entry = entry.expect("dir entry");
            let path = entry.path();
            let file_type = entry.file_type().expect("file type");
            if file_type.is_dir() {
                let name = entry.file_name().to_string_lossy().into_owned();
                collect(&path, &format!("{prefix}{name}/"), records);
            } else if file_type.is_file() {
                let name = entry.file_name().to_string_lossy().into_owned();
                let rel = format!("{prefix}{name}");
                let bytes = fs::read(&path).expect("read fixture file");
                records.push((rel, bytes));
            }
        }
    }

    let mut records = Vec::new();
    collect(
        &root.join(source_dir),
        &format!("{source_dir}/"),
        &mut records,
    );
    records.sort_by(|left, right| left.0.cmp(&right.0));
    let mut hasher = Sha256::new();
    for (path, bytes) in records {
        hasher.update(path.as_bytes());
        hasher.update(b"\0");
        hasher.update(&bytes);
        hasher.update(b"\n");
    }
    Provenance::LocalContent {
        digest_algorithm: DigestAlgorithm::Sha256,
        digest: format!("{:x}", hasher.finalize()),
    }
}

#[test]
#[ignore = "subprocess worker invoked by the differential harness"]
fn corpus_differential_worker() {
    if std::env::var_os("BAMTS_CORPUS_WORKER_REQUEST").is_none() {
        return;
    }
    run_corpus_worker_from_env().expect("corpus worker completes");
}

#[test]
fn every_execution_mode_enforces_the_case_timeout() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("corpus-timeout-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.ts");
    let path = root.join(&entrypoint);
    fs::write(&path, "while (true) {}\n").expect("write timeout fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 100,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    for mode in ExecutionMode::ALL {
        let outcome = bamts
            .run_case(&spec, mode)
            .unwrap_or_else(|error| panic!("{} timeout run failed: {error}", mode.as_str()));
        assert!(
            outcome.timed_out,
            "{} infinite loop escaped its case timeout: {}",
            mode.as_str(),
            evidence(&outcome)
        );
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
}

#[test]
fn all_pinned_cases_match_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let corpus = load_corpus(&root).expect("the pinned corpus must parse and validate");
    let ids = corpus
        .cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        ids, PINNED_CASE_IDS,
        "the differential harness must cover exactly the 27 pinned cases in manifest order"
    );

    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();

    for case in &corpus.cases {
        let expected = oracle.run_case(case);
        for mode in ExecutionMode::ALL {
            let actual = bamts.run_case(case, mode);
            compare_case(&case.id, mode, &expected, &actual, &mut failures);
        }
    }

    assert!(
        failures.is_empty(),
        "corpus differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn p_map_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let corpus = load_corpus(&root).expect("the pinned corpus must parse and validate");
    let case = corpus.case("p-map").expect("p-map is pinned");
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let expected = oracle.run_case(case);
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();

    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(case, mode);
        compare_case(&case.id, mode, &expected, &actual, &mut failures);
    }

    assert!(
        failures.is_empty(),
        "p-map differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn for_await_sync_thenable_unwrap_and_iterator_result_not_assimilated() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("for-await-sync-thenable-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.ts");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"(async () => {
  const out: string[] = [];

  for await (const v of [Promise.resolve(42)]) {
    out.push(`promise.unwrapped=${v === 42}`);
  }

  let thenableCounter = 0;
  const thenableIterator = {
    [Symbol.iterator]() {
      let step = 0;
      return {
        next() {
          if (step++ === 0) {
            return {
              value: "raw",
              done: false,
              then(resolve: (value: string) => void, _reject: unknown) {
                thenableCounter += 1;
                resolve("assimilated");
              },
            };
          }
          return { value: undefined, done: true };
        },
      };
    },
  };

  for await (const v of thenableIterator) {
    out.push(`thenable.yield=${v}`);
    out.push(`thenable.counter=${thenableCounter}`);
  }

  let rejectionCloseCount = 0;
  const rejectingIterator = {
    [Symbol.iterator]() {
      let step = 0;
      return {
        next() {
          if (step++ === 0) {
            return { value: Promise.reject("value-rejection"), done: false };
          }
          return { value: undefined, done: true };
        },
        return() {
          rejectionCloseCount = rejectionCloseCount + 1;
          return { value: undefined, done: true };
        },
      };
    },
  };

  try {
    for await (const _v of rejectingIterator) {}
  } catch (error) {
    out.push(`rejection.reason=${error === "value-rejection"}`);
  }
  out.push(`rejection.close-count=${rejectionCloseCount}`);

  let stepFailureCloseCount = 0;
  const failingStepIterator = {
    [Symbol.iterator]() {
      return {
        next() {
          throw "step-failure";
        },
        return() {
          stepFailureCloseCount = stepFailureCloseCount + 1;
          return { value: undefined, done: true };
        },
      };
    },
  };

  try {
    for await (const _v of failingStepIterator) {}
  } catch (error) {
    out.push(`step-failure.reason=${error === "step-failure"}`);
  }
  out.push(`step-failure.close-count=${stepFailureCloseCount}`);
  console.log(out.join("\n"));
})();"#,
    )
    .expect("write for-await thenable fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "for-await sync thenable differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn iterator_close_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("iterator-close-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"(async () => {
  const trace = [];
  function sync(tag, values, closeError, closeResult) {
    let index = 0;
    return {
      [Symbol.iterator]() { return this; },
      next() {
        return index < values.length
          ? { value: values[index++], done: false }
          : { value: undefined, done: true };
      },
      return() {
        trace.push(`${tag}:return`);
        if (closeError !== undefined) throw closeError;
        if (closeResult !== undefined) return closeResult;
        return { value: undefined, done: true };
      },
    };
  }

  for (const value of sync("break", [1])) {
    trace.push(`break:body:${value}`);
    break;
  }
  for (const value of sync("normal", [1, 2])) {
    trace.push(`normal:body:${value}`);
  }
  for (const value of sync("continue", [1, 2])) {
    trace.push(`continue:body:${value}`);
    continue;
  }
  for (const value of [1]) {
    trace.push(`absent:body:${value}`);
    break;
  }
  try {
    for (const value of sync("primitive", [1], undefined, 1)) {
      trace.push(`primitive:body:${value}`);
      break;
    }
  } catch (_error) {
    trace.push("primitive:catch");
  }
  function returnFromLoop() {
    for (const value of sync("function", [1])) {
      try {
        trace.push(`function:body:${value}`);
        return "returned";
      } finally {
        trace.push("function:finally");
      }
    }
  }
  trace.push(`function:result:${returnFromLoop()}`);
  try {
    const bindingValue = {
      get value() {
        trace.push("binding:get");
        throw "binding-error";
      },
    };
    for (const { value } of sync("binding", [bindingValue])) {
      trace.push(`binding:body:${value}`);
    }
  } catch (_error) {
    trace.push("binding:catch");
  }
  exit: {
    for (const _value of sync("label-break", [1])) {
      try {
        trace.push("label-break:body");
        break exit;
      } finally {
        trace.push("label-break:finally");
      }
    }
  }
  outer: for (let i = 0; i < 2; i++) {
    for (const _value of sync(`label:${i}`, [i])) {
      try {
        trace.push(`label:body:${i}`);
        continue outer;
      } finally {
        trace.push(`label:finally:${i}`);
      }
    }
  }
  try {
    for (const _value of sync("throw", [1], "close-error")) {
      try {
        trace.push("throw:body");
        throw "body-error";
      } finally {
        trace.push("throw:finally");
      }
    }
  } catch (error) {
    trace.push(`throw:catch:${error}`);
  }
  for await (const value of [1]) {
    trace.push(`async-absent:body:${value}`);
    break;
  }
  const asyncPrimitive = {
    [Symbol.asyncIterator]() {
      return {
        next() { return Promise.resolve({ value: 1, done: false }); },
        return() {
          trace.push("async-primitive:return");
          return Promise.resolve(1);
        },
      };
    },
  };
  try {
    for await (const value of asyncPrimitive) {
      trace.push(`async-primitive:body:${value}`);
      break;
    }
  } catch (_error) {
    trace.push("async-primitive:catch");
  }
  const asyncIterable = {
    [Symbol.asyncIterator]() {
      let started = false;
      return {
        next() {
          if (started) return Promise.resolve({ value: undefined, done: true });
          started = true;
          return Promise.resolve({ value: 1, done: false });
        },
        return() {
          trace.push("async:return");
          return Promise.resolve().then(() => {
            trace.push("async:return-reject");
            throw "async-close-error";
          });
        },
      };
    },
  };
  try {
    for await (const value of asyncIterable) {
      try {
        trace.push(`async:body:${value}`);
        throw "async-body-error";
      } finally {
        trace.push("async:finally");
      }
    }
  } catch (error) {
    trace.push(`async:catch:${error}`);
  }
  console.log(trace.join("\n"));
})();"#,
    )
    .expect("write iterator-close fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "iterator-close differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn derived_constructor_super_flow_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("derived-constructor-super-flow-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"class Base {
  constructor(value) {
    this.value = value;
  }
}
function capture(label, construct) {
  try {
    const value = construct();
    console.log(`${label}:value=${value.value}`);
  } catch (error) {
    console.log(`${label}:ReferenceError=${error instanceof ReferenceError}`);
  }
}
capture("conditional-true", () => new class extends Base {
  constructor() {
    if (true) super(1);
  }
}());
capture("conditional-false", () => new class extends Base {
  constructor() {
    if (false) super(2);
  }
}());
capture("conditional-branches", () => new class extends Base {
  constructor(flag) {
    if (flag) super(3); else super(4);
  }
}(false));
capture("repeated", () => new class extends Base {
  constructor() {
    super(5);
    super(6);
  }
}());
capture("looped", () => new class extends Base {
  constructor() {
    while (true) {
      super(7);
    }
  }
}());
capture("nested-control", () => new class extends Base {
  constructor() {
    for (const value of [8]) {
      if (value === 8) {
        super(value);
      }
    }
  }
}());
let retryCount = 0;
class RetryBase {
  constructor(value) {
    if (retryCount++ === 0) {
      throw new Error("x");
    }
    this.value = value;
  }
}
capture("retry", () => new class extends RetryBase {
  constructor() {
    try {
      super(1);
    } catch (error) {}
    super(2);
  }
}());
capture("early-object", () => new class extends Base {
  constructor() {
    return { value: "early" };
  }
}());
capture("state-u-undefined", () => new class extends Base {
  constructor() {}
}());
"#,
    )
    .expect("write derived-constructor super-flow fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "derived-constructor super-flow differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn derived_constructor_returns_match_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("derived-constructor-returns-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"class Base {}
function capture(label, construct) {
  try {
    const value = construct();
    const result = typeof value === "function"
      ? "function"
      : value.kind;
    console.log(`${label}:${result}`);
  } catch (error) {
    console.log(`${label}:TypeError=${error instanceof TypeError}`);
  }
}
capture("object", () => new class extends Base {
  constructor() {
    super();
    return { kind: "object" };
  }
}());
capture("function", () => new class extends Base {
  constructor() {
    super();
    return function replacement() {};
  }
}());
capture("undefined", () => new class extends Base {
  constructor() {
    super();
    this.kind = "initialized-this";
    return undefined;
  }
}());
capture("null", () => new class extends Base {
  constructor() {
    super();
    return null;
  }
}());
capture("number", () => new class extends Base {
  constructor() {
    super();
    return 1;
  }
}());
capture("string", () => new class extends Base {
  constructor() {
    super();
    return "primitive";
  }
}());
capture("bare", () => new class extends Base {
  constructor() {
    super();
    this.kind = "bare-this";
    return;
  }
}());
capture("finally", () => new class extends Base {
  constructor() {
    super();
    try {
      return 1;
    } finally {
      return { kind: "finally-object" };
    }
  }
}());
"#,
    )
    .expect("write derived-constructor return fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "derived-constructor return differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn default_derived_construction_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("default-derived-construction-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"class Base {
  constructor(first, second) {
    this.sum = first + second;
    Base.seenNewTarget = new.target;
  }
}
function capture(label, construct) {
  try {
    const value = construct();
    console.log(`${label}:value=${value.sum}:fields=${value.field}:target=${Base.seenNewTarget && Base.seenNewTarget.name}:instanceof=${value instanceof Base}`);
  } catch (error) {
    console.log(`${label}:threw=${error.constructor.name}:${error.message}`);
  }
}
capture("args-target-prototype", () => new (class extends Base {
  field = "initialized";
})(2, 3));
class PrimitiveReturnBase {
  constructor() {
    this.marker = "base-this";
    return 42;
  }
}
try {
  const value = new (class extends PrimitiveReturnBase {
    field = "derived-field";
  })();
  console.log(`return-override:marker=${value.marker}:field=${value.field}:proto=${Object.getPrototypeOf(value).constructor.name}`);
} catch (error) {
  console.log(`return-override:threw=${error.constructor.name}`);
}
class ThrowingBase {
  constructor() {
    throw new RangeError("abrupt-base");
  }
}
try {
  new (class extends ThrowingBase {
    field = (() => { console.log("field-init-after-abrupt"); return 1; })();
  })();
  console.log("abrupt:unexpected-success");
} catch (error) {
  console.log(`abrupt:threw=${error.constructor.name}:${error.message}`);
}
class ObjectReturnBase {
  constructor() {
    this.marker = "base-this";
    return { marker: "replacement", field: "no-fields" };
  }
}
try {
  const value = new (class extends ObjectReturnBase {
    field = "derived-field";
  })();
  console.log(`object-return:marker=${value.marker}:field=${value.field}`);
} catch (error) {
  console.log(`object-return:threw=${error.constructor.name}`);
}
"#,
    )
    .expect("write default derived construction fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "default derived construction differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn explicit_new_target_construction_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("explicit-new-target-construction-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"class Base {
  constructor(first, second) {
    this.sum = first + second;
    Base.seenNewTarget = new.target;
  }
}
class ExplicitMiddle extends Base {
  constructor(first, second, third) {
    super(first, second);
    this.third = third;
  }
}
class ImplicitMiddle extends ExplicitMiddle {}
class Leaf extends ImplicitMiddle {}
function capture(label, construct) {
  try {
    const value = construct();
    console.log(`${label}:value=${value.sum}:third=${value.third}:target=${Base.seenNewTarget && Base.seenNewTarget.name}:base=${value instanceof Base}:explicit=${value instanceof ExplicitMiddle}:implicit=${value instanceof ImplicitMiddle}:leaf=${value instanceof Leaf}`);
  } catch (error) {
    console.log(`${label}:threw=${error.constructor.name}:${error.message}`);
  }
}
capture("leaf-most-derived", () => new Leaf(2, 3, 4));
capture("implicit-as-leaf", () => new ImplicitMiddle(5, 6, 7));
capture("explicit-as-leaf", () => new ExplicitMiddle(8, 9, 10));
"#,
    )
    .expect("write explicit new.target construction fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "explicit new.target construction differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn import_meta_identity_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("import-meta-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.mjs");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        "import.meta.custom = 1;
console.log(import.meta === import.meta);
console.log(import.meta.custom === 1);
console.log(typeof import.meta.url === 'string' && import.meta.url.length > 0);
",
    )
    .expect("write import-meta fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "import-meta differential failures:
{}",
        failures.join(
            "

"
        )
    );
}

#[test]
fn declaration_owned_self_captures_match_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("task-106-self-captures-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        "function run() {
  const arrow = () => arrow;
  function recursive() { return recursive; }
  class Self { method() { return Self; } }
  const { destructured = () => destructured } = {};
  const shadowed = () => shadowed;
  { const shadowed = 0; }
  console.log(arrow() === arrow);
  console.log(recursive() === recursive);
  console.log(new Self().method() === Self);
  console.log(destructured() === destructured);
  console.log(shadowed() === shadowed);
}
run();
",
    )
    .expect("write self-capture fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "declaration-owned self-capture differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn local_lexical_tdz_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("task-106-local-tdz-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        "function outcome(operation) {
  try { return String(operation()); }
  catch (error) { return error.name; }
}
function earlyRead() {
  const read = () => later;
  const observed = outcome(read);
  let later = 1;
  return observed;
}
function lateRead() {
  const read = () => later;
  let later = 1;
  return read();
}
function hoisted() {
  return declaredLater();
  function declaredLater() { return 2; }
}
function blockRead() {
  let value = 1;
  {
    const read = () => value;
    const observed = outcome(read);
    let value = 2;
    return observed;
  }
}
function localClassName() {
  class LocalClass { static value = LocalClass; }
  return LocalClass.value === LocalClass;
}
const C = class {};
const heritage = outcome(() => { class C extends C {}; return C; });
const expressionHeritage = outcome(() => class C extends C {});
class StaticClass { static value = StaticClass; }
const staticClassName = String(StaticClass.value === StaticClass);
const typeResult = outcome(() => { return typeof value; let value; });
process.stdout.write([
  earlyRead(),
  lateRead(),
  hoisted(),
  heritage,
  expressionHeritage,
  staticClassName,
  String(localClassName()),
  blockRead(),
  typeResult,
].join('\\n') + '\\n');
",
    )
    .expect("write local TDZ fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "local lexical TDZ differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn task_106_sync_cases_match_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let corpus = load_corpus(&root).expect("the pinned corpus must parse and validate");
    let ids = corpus
        .cases
        .iter()
        .filter(|case| TASK_106_SYNC_CASE_IDS.contains(&case.id.as_str()))
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        ids, TASK_106_SYNC_CASE_IDS,
        "the Task 106 gate must cover exactly its synchronous cases in manifest order"
    );

    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();
    for id in TASK_106_SYNC_CASE_IDS {
        let case = corpus.case(id).expect("Task 106 case must exist");
        let expected = oracle.run_case(case);
        for mode in ExecutionMode::ALL {
            let actual = bamts.run_case(case, mode);
            compare_case(&case.id, mode, &expected, &actual, &mut failures);
        }
    }
    assert!(
        failures.is_empty(),
        "Task 106 differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn task_107_node_cases_match_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let corpus = load_corpus(&root).expect("the pinned corpus must parse and validate");
    let ids = corpus
        .cases
        .iter()
        .filter(|case| TASK_107_NODE_CASE_IDS.contains(&case.id.as_str()))
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        ids, TASK_107_NODE_CASE_IDS,
        "the Task 107 gate must cover exactly citty, is-plain-obj, and ohash in manifest order"
    );

    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();
    for id in TASK_107_NODE_CASE_IDS {
        let case = corpus.case(id).expect("Task 107 case must exist");
        let expected = oracle.run_case(case);
        for mode in ExecutionMode::ALL {
            let actual = bamts.run_case(case, mode);
            compare_case(&case.id, mode, &expected, &actual, &mut failures);
        }
    }
    assert!(
        failures.is_empty(),
        "Task 107 differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn task_110_event_loop_drives_to_quiescence_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("task-110-event-loop-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        "console.log('sync');
Promise.resolve().then(() => console.log('micro'));
setTimeout(() => {
  console.log('timer');
  Promise.resolve().then(() => console.log('timer-micro'));
}, 1);
",
    )
    .expect("write event-loop fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "Task 110 event-loop differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn first_tla_rejection_aborts_root_body_before_pending_dependency_completes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("tla-reject-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.ts");
    let root_path = root.join(&entrypoint);
    let rejecting_path = root.join(format!("{source_dir}/{id}-rejecting.ts"));
    let pending_path = root.join(format!("{source_dir}/{id}-pending.ts"));

    fs::write(
        &rejecting_path,
        "await Promise.resolve();\nthrow 'first-rejection';\n",
    )
    .expect("write rejecting dependency");
    fs::write(
        &pending_path,
        "await Promise.resolve();\nawait Promise.resolve();\n",
    )
    .expect("write pending dependency");
    fs::write(
        &root_path,
        format!(
            "import './{id}-rejecting.ts';\nimport './{id}-pending.ts';\nconsole.log('ROOT-BODY-EXECUTED');\n"
        ),
    )
    .expect("write root fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();
    match &expected {
        Ok(outcome)
            if outcome.is_reliable()
                && outcome.exit_code == Some(1)
                && outcome.stdout.is_empty() => {}
        Ok(outcome) => failures.push(format!(
            "case `{}` / Node: expected a clean rejection with no root output; got {}",
            spec.id,
            evidence(outcome)
        )),
        Err(error) => failures.push(format!(
            "case `{}` / Node: oracle failed before comparison: {error}",
            spec.id
        )),
    }
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "TLA first-rejection differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn top_level_throws_are_comparable_process_outcomes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("task-113-top-level-throw-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(&path, "throw new Error('boom');\n").expect("write top-level throw fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "top-level throw differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn class_decorators_match_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("class-decorators-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Strengthened class-decorator ordering: static computed keys evaluate before
    // application; static field/auto-accessor/block drain in source order after
    // replacement on the raw constructor; final `this` diverges from raw
    // ownership; class extras run FIFO after that static drain.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function evaluate(label) { log(`evaluate:${label}`); return (value, context) => { log(`apply:${label}:${context.kind}:${context.name}:${value.name}`); }; }
function computed(label) { log(`key:${label}`); return label; }
let capturedAddInitializer;
let capturedRawOwned;
function replace(value, context) {
  log(`replace:${context.name}:${value.name}`);
  capturedAddInitializer = context.addInitializer;
  if (context.name === 'Owned') {
    capturedRawOwned = value;
  }
  context.addInitializer(function () { log(`extraThis:first:${this.name}`); });
  context.addInitializer(function () { log(`extraThis:second:${this.name}`); });
  return class Replacement extends value {};
}
function replaceExpression(value, context) {
  log(`replaceExpression:${context.name}:${value.name}`);
  return class ReplacementExpression extends value {
    method() { return 'replacement'; }
  };
}
const Named = @evaluate('before') @evaluate('after') @replaceExpression class ExpressionBase extends (function () { log('extends'); return Object; })() {
  static {
    log(`internalSelf:${ExpressionBase.name}`);
    log(`expressionThis:${this.name}`);
  }
  method() { return 'base'; }
};
@replace
@evaluate('after')
class Ordered { name() { return 'ordered'; } }
@replace
class Owned {
  static [computed('owned')] = (log('drain:field'), 41);
  static accessor ownedAcc = (log('drain:accessor'), 3);
  static { log(`drain:block:${this.name}`); }
}
class InvalidParent { }
@evaluate('invalid-expression')
class Invalid extends InvalidParent { name() { return 'invalid'; } }
function attempt(label, operation) { try { log(`${label}:${operation()}`); } catch (error) { log(`${label}:error:${error instanceof TypeError}`); } }
attempt('named-expression', () => new Named().method());
attempt('ordered', () => new Ordered().name());
attempt('invalid', () => new Invalid().name());
attempt('late-addInitializer', () => capturedAddInitializer(function () { log('late'); }));
log(`hasOwnFinal:${Object.hasOwn(Owned, 'owned')}`);
log(`hasOwnRaw:${Object.hasOwn(capturedRawOwned, 'owned')}`);
log(`fieldValue:${capturedRawOwned["owned"]}`);
log(`hasOwnFinalAcc:${Object.hasOwn(Owned, 'ownedAcc')}`);
log(`hasOwnRawAcc:${Object.hasOwn(capturedRawOwned, 'ownedAcc')}`);
log(`accValue:${capturedRawOwned.ownedAcc}`);
log(`sameRef:${Owned === capturedRawOwned}`);
log(`prototypeConstructorEnumerable:${Object.getOwnPropertyDescriptor(capturedRawOwned.prototype, 'constructor').enumerable}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write class decorator fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript decorator oracle");
    assert!(
        status.success(),
        "TypeScript decorator oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "class decorator differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn class_decorator_initializer_state_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("class-decorator-state-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Open during decorator application: enqueue two callbacks. Closed after
    // evaluation: escaped addInitializer throws TypeError and the rejected
    // callback never runs. FIFO extras and the final binding observe the exact
    // replacement object, not merely a shared class name.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
let escaped;
let replacement;
function replace(value, context) {
  escaped = context.addInitializer;
  replacement = class Replacement extends value {};
  context.addInitializer(function () { log(`extra:first:this===replacement:${this === replacement}`); });
  context.addInitializer(function () { log(`extra:second:this===replacement:${this === replacement}`); });
  return replacement;
}
@replace
class C {}
log(`final:C===replacement:${C === replacement}`);
try {
  escaped(function () { log('late'); });
  log('late:accepted');
} catch (error) {
  log(`late:error:${error instanceof TypeError}`);
}
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write class decorator state fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript decorator state oracle");
    assert!(
        status.success(),
        "TypeScript decorator state oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "class decorator state differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn invalid_class_decorator_return_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("class-decorator-invalid-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"function invalid(value, context) { return 42; }
function invalidClass() {
  @invalid
  class Bad { name() { return 'bad'; } }
  return Bad;
}
console.log('before');
try {
  invalidClass();
  console.log('unexpected');
} catch (error) {
  console.log(`invalid:${error instanceof TypeError}`);
}
"#;
    fs::write(&source_path, source).expect("write invalid class decorator fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript invalid decorator oracle");
    assert!(
        status.success(),
        "TypeScript invalid decorator oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "invalid class decorator differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn invalid_auto_accessor_decorator_return_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("auto-accessor-decorator-invalid-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"let sideEffects = 0;
function invalid(_target, _context) {
  return function () {
    sideEffects += 1;
  };
}
function invalidAccessor() {
  class Bad {
    @invalid
    accessor value = 1;
  }
  return Bad;
}
console.log('before');
try {
  invalidAccessor();
  console.log('unexpected');
} catch (error) {
  console.log(`invalid:${error instanceof TypeError}`);
  console.log(`sideEffects:${sideEffects}`);
}
"#;
    fs::write(&source_path, source).expect("write invalid auto-accessor decorator fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript invalid auto-accessor decorator oracle");
    assert!(
        status.success(),
        "TypeScript invalid auto-accessor decorator oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "invalid auto-accessor decorator differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn interpreter_failure_text_names_mode_stage_and_evidence() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("task-113-interpreter-missing-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");

    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: format!("{source_dir}/{id}.js"),
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let error = bamts
        .run_case(&spec, ExecutionMode::Interpreter)
        .expect_err("a missing entrypoint must fail in interpreter mode");
    let text = error.to_string();
    assert!(
        text.contains(&format!("case `{id}` failed in interpreter mode")),
        "failure must name the case and interpreter mode: {text}"
    );
    assert!(
        text.contains("stage=load"),
        "a missing entrypoint must classify as load: {text}"
    );
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        text.contains("could not read"),
        "failure must carry the observed evidence: {text}"
    );
}

fn compare_case(
    case_id: &str,
    mode: ExecutionMode,
    expected: &bamts_verification::Result<OracleOutcome>,
    actual: &bamts_verification::Result<OracleOutcome>,
    failures: &mut Vec<String>,
) {
    let label = format!("case `{case_id}` / {}", mode.as_str());
    let (expected, actual) = match (expected, actual) {
        (Err(error), Err(actual_error)) => {
            failures.push(format!(
                "{label}: stage=spawn Node oracle failed: {error}\n{label}: BamTS failed: {actual_error}"
            ));
            return;
        }
        (Err(error), Ok(actual)) => {
            failures.push(format!(
                "{label}: stage=spawn Node oracle failed: {error}\nBamTS evidence: {}",
                evidence(actual)
            ));
            return;
        }
        (Ok(expected), Err(error)) => {
            failures.push(format!(
                "{label}: BamTS failed: {error}\nNode evidence: {}",
                evidence(expected)
            ));
            return;
        }
        (Ok(expected), Ok(actual)) => (expected, actual),
    };

    if !expected.is_reliable() {
        failures.push(format!(
            "{label}: stage=spawn Node oracle did not produce a complete result: {}",
            evidence(expected)
        ));
        return;
    }
    if !actual.is_reliable() {
        failures.push(format!(
            "{label}: stage={} BamTS did not produce a complete result: {}",
            bamts_outcome_stage(mode).as_str(),
            evidence(actual)
        ));
        return;
    }
    if expected.exit_code != actual.exit_code || expected.stdout != actual.stdout {
        failures.push(format!(
            "{label}: stage=compare stdout bytes or exit code differ\nNode: {}\nBamTS: {}\nfirst stdout difference: {}",
            evidence(expected),
            evidence(actual),
            first_difference(&expected.stdout, &actual.stdout),
        ));
    }
}

#[test]
fn namespace_export_star_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("namespace-export-star-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.ts");
    let source_path = root.join(format!("{source_dir}/{id}-source.ts"));
    let root_path = root.join(&entrypoint);

    fs::write(&source_path, "export const value = 7;\n").expect("write namespace source fixture");
    fs::write(
        &root_path,
        format!(
            r#"export * as ns from './{id}-source.ts';
import {{ ns }} from './{id}.ts';
console.log(`identity:${{ns === ns}}`);
console.log(`live:${{ns.value}}`);
"#
        ),
    )
    .expect("write namespace root fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let bamts = BamtsRunner::new(&root);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "namespace export-star differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn merged_namespace_function_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("merged-namespace-function-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.ts");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"function Item(x: number) {
  return x * 2;
}
namespace Item {
  export const label = "item";
  export function tag() {
    return "ns";
  }
}
console.log(`fn:${Item(5)};ns:${Item.label};tag:${Item.tag()}`);
"#;
    fs::write(&source_path, source).expect("write merged namespace function fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript merged-namespace oracle");
    assert!(
        status.success(),
        "TypeScript merged-namespace oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "merged namespace function differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn standard_member_decorators_match_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("standard-member-decorators-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function tap(label) {
  log(`evaluate:${label}`);
  return (value, context) => {
    log(`apply:${label}:${context.kind}:${String(context.name)}:static=${context.static}:private=${context.private}:access=${typeof context.access}`);
  };
}
function wrapMethod(label) {
  return (value, context) => {
    log(`wrap:${label}:${String(context.name)}`);
    return function (...args) {
      log(`call:${label}:${String(context.name)}`);
      return value.apply(this, args);
    };
  };
}
function fieldInit(label) {
  return (_value, context) => {
    log(`field:${label}:${String(context.name)}`);
    context.addInitializer(function () { log(`extra:${label}:${String(context.name)}`); });
    return initial => { log(`init:${label}:${String(context.name)}:${initial}`); return initial + 1; };
  };
}
function accessorInit(label) {
  return (target, context) => {
    log(`accessor:${label}:${String(context.name)}`);
    context.addInitializer(function () { log(`extra:${label}:${String(context.name)}`); });
    return {
      get() { log(`get:${label}`); return target.get.call(this) * 10; },
      set(value) { log(`set:${label}:${value}`); target.set.call(this, value); },
      init(initial) { log(`init:${label}:${initial}`); return initial * 2; },
    };
  };
}
function computed(label) { log(`key:${label}`); return label; }
function classDec(label) {
  log(`evaluate:${label}`);
  return (_value, context) => {
    log(`class:${label}:${context.kind}:${context.name}`);
    context.addInitializer(function () { log(`classextra:${label}`); });
  };
}
@classDec('outer')
@classDec('inner')
class Fixture {
  @wrapMethod('instance')
  @tap('instance-tap')
  [computed('method')](value) { return value + 1; }

  @tap('get')
  get pair() { return this.amount; }
  @tap('set')
  set pair(value) { this.amount = value; }

  @fieldInit('inst-field')
  count = 5;

  @accessorInit('acc')
  accessor total = 3;

  @wrapMethod('static')
  static [computed('smethod')](value) { return value * 2; }

  @fieldInit('static-field')
  static level = 7;

  amount = 0;
  constructor() { log('ctor'); }
}
log('--- after class definition ---');
const instance = new Fixture();
log(`method:${instance["method"](1)}`);
instance.pair = 4;
log(`get:${instance.pair}`);
log(`count:${instance.count}`);
log(`total:${instance.total}`);
log(`smethod:${Fixture["smethod"](3)}`);
log(`level:${Fixture.level}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write standard member decorator fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript standard decorator oracle");
    assert!(
        status.success(),
        "TypeScript standard decorator oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "standard member decorator differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn callable_decorator_initializers_precede_fields_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("callable-decorator-initializers-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Method extras are independent of source position: an instance field before a
    // decorated method still sees FIFO extras first; a static field/block before a
    // decorated static method still sees FIFO extras first on the final class.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function instanceMethod(_value, context) {
  context.addInitializer(function () { log('instance:first'); });
  context.addInitializer(function () { log('instance:second'); });
}
function staticMethod(_value, context) {
  context.addInitializer(function () { log(`static:first:${this.name}`); });
  context.addInitializer(function () { log(`static:second:${this.name}`); });
}
function replace(value, context) {
  log(`replace:${context.name}:${value.name}`);
  return class Replacement extends value {};
}
@replace
class Fixture {
  field = (log('field'), 1);
  @instanceMethod
  method() { return 'method'; }
  static sField = (log('sField'), 2);
  static { log(`sBlock:${this.name}`); }
  @staticMethod
  static sMethod() { return 'sMethod'; }
  constructor() { log(`ctor:${this.constructor.name}`); }
}
const instance = new Fixture();
log(`method:${instance.method()}`);
log(`sMethod:${Fixture.sMethod()}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write callable decorator initializer fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript callable decorator initializer oracle");
    assert!(
        status.success(),
        "TypeScript callable decorator initializer oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "callable decorator initializer differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn member_decorator_application_stages_match_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("member-decorator-application-stages-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Static members first in source so evaluation order cannot be mistaken for the
    // four application stages: static callable/accessor → instance callable/accessor →
    // static field → instance field. evaluate:/key: stay on the evaluation timeline;
    // apply: alone proves application-stage order.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function dec(label) {
  log(`evaluate:${label}`);
  return (_value, context) => {
    log(`apply:${label}:${context.kind}:${String(context.name)}:static=${context.static}`);
  };
}
function key(label) { log(`key:${label}`); return label; }
class Fixture {
  @dec('static-callable')
  static [key('sMethod')]() { return 's'; }

  @dec('static-accessor-field-like')
  static accessor [key('sAccessor')] = 3;

  @dec('static-field-like')
  static [key('sField')] = 1;

  @dec('instance-callable')
  [key('iMethod')]() { return 'i'; }

  @dec('instance-accessor-field-like')
  accessor [key('iAccessor')] = 4;

  @dec('instance-field-like')
  [key('iField')] = 2;
}
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write member decorator application-stage fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript member decorator application-stage oracle");
    assert!(
        status.success(),
        "TypeScript member decorator application-stage oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "member decorator application-stage differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn auto_accessor_decorator_call_depth_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("auto-accessor-decorator-call-depth-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"const trace = [];
let applyCount = 0;
let getCount = 0;
function log(value) { trace.push(value); }
function onceDec() {
  log('evaluate');
  return (target, context) => {
    applyCount += 1;
    log(`apply:${applyCount}:${String(context.name)}`);
    return {
      get() {
        getCount += 1;
        log(`get:${getCount}`);
        return target.get.call(this);
      },
      set(value) {
        log(`set:${value}`);
        target.set.call(this, value);
      },
    };
  };
}
class C {
  @onceDec()
  accessor value = 1;
}
log(`afterClass:apply=${applyCount}`);
const instance = new C();
log(`read:${instance.value}`);
instance.value = 2;
log(`read:${instance.value}`);
log(`final:apply=${applyCount}:get=${getCount}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write auto-accessor decorator call-depth fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript auto-accessor decorator oracle");
    assert!(
        status.success(),
        "TypeScript auto-accessor decorator oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "auto-accessor decorator call-depth differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn stacked_auto_accessor_decorators_match_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("stacked-auto-accessor-decorators-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"const trace = [];
const applyCount = { outer: 0, inner: 0 };
const getCount = { outer: 0, inner: 0 };
const setCount = { outer: 0, inner: 0 };
function log(value) { trace.push(value); }
function layer(label) {
  log(`evaluate:${label}`);
  return (target, context) => {
    applyCount[label] += 1;
    log(`apply:${label}:${applyCount[label]}:${String(context.name)}`);
    return {
      get() {
        getCount[label] += 1;
        log(`get:${label}:${getCount[label]}`);
        return target.get.call(this);
      },
      set(value) {
        setCount[label] += 1;
        log(`set:${label}:${setCount[label]}:${value}`);
        target.set.call(this, value);
      },
    };
  };
}
class C {
  @layer('outer')
  @layer('inner')
  accessor value = 1;
}
log(`afterClass:outer=${applyCount.outer}:inner=${applyCount.inner}`);
const instance = new C();
log(`read:${instance.value}`);
instance.value = 2;
log(`read:${instance.value}`);
log(`final:outerApply=${applyCount.outer}:innerApply=${applyCount.inner}:outerGet=${getCount.outer}:innerGet=${getCount.inner}:outerSet=${setCount.outer}:innerSet=${setCount.inner}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write stacked auto-accessor decorator fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript stacked auto-accessor decorator oracle");
    assert!(
        status.success(),
        "TypeScript stacked auto-accessor decorator oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "stacked auto-accessor decorator differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn stacked_field_accessor_initializers_match_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("stacked-field-accessor-initializers-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Non-commutative transforms: reversed/duplicated/skipped init order cannot
    // accidentally produce the same final values or log timeline.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function field(label, op) {
  log(`evaluate:${label}`);
  return (_value, context) => {
    log(`apply:${label}:${String(context.name)}:static=${context.static}`);
    return (initial) => {
      const next = op(initial);
      log(`init:${label}:${initial}->${next}`);
      return next;
    };
  };
}
function accessor(label, op) {
  log(`evaluate:${label}`);
  return (target, context) => {
    log(`apply:${label}:${String(context.name)}`);
    return {
      init(initial) {
        const next = op(initial);
        log(`ainit:${label}:${initial}->${next}`);
        return next;
      },
    };
  };
}
class Fixture {
  @field('outer', (v) => v + 'O')
  @field('inner', (v) => v + 'I')
  value = 'S';

  @field('sOuter', (v) => v + 'SO')
  @field('sInner', (v) => v + 'SI')
  static sValue = 'SS';

  @accessor('aOuter', (v) => v * 10)
  @accessor('aInner', (v) => v + 1)
  accessor acc = 1;
}
const instance = new Fixture();
log(`value:${instance.value}`);
log(`sValue:${Fixture.sValue}`);
log(`acc:${instance.acc}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write stacked field/accessor initializer fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript stacked field/accessor initializer oracle");
    assert!(
        status.success(),
        "TypeScript stacked field/accessor initializer oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "stacked field/accessor initializer differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn undecorated_auto_accessor_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("undecorated-auto-accessor-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"const trace = [];
function log(value) { trace.push(value); }
class C {
  accessor value = 1;
}
const instance = new C();
log(`read:${instance.value}`);
instance.value = 2;
log(`read:${instance.value}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source).expect("write undecorated auto-accessor fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript undecorated auto-accessor oracle");
    assert!(
        status.success(),
        "TypeScript undecorated auto-accessor oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "undecorated auto-accessor differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn class_decorator_replacement_static_field_and_auto_accessor_match_tsc_oracle_in_every_execution_mode()
 {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!(
        "class-decorator-replacement-static-accessor-{}",
        process::id()
    );
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function replace(value, context) {
  log(`replace:${context.kind}:${context.name}:${value.name}`);
  return class Replacement extends value {};
}
function fieldInit(_value, context) {
  log(`field:${context.kind}:${String(context.name)}:static=${context.static}`);
  return initial => { log(`fieldInit:${initial}`); return initial + 1; };
}
function accessorInit(target, context) {
  log(`accessor:${context.kind}:${String(context.name)}:static=${context.static}`);
  return {
    get() { return target.get.call(this); },
    set(value) { target.set.call(this, value); },
    init(initial) { log(`accInit:${initial}`); return initial * 2; },
  };
}
@replace
class Fixture {
  @fieldInit
  static level = 7;
  @accessorInit
  accessor total = 3;
}
log(`name:${Fixture.name}`);
log(`level:${Fixture.level}`);
const instance = new Fixture();
log(`total:${instance.total}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source)
        .expect("write class decorator replacement static/accessor fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript class decorator replacement static/accessor oracle");
    assert!(
        status.success(),
        "TypeScript class decorator replacement static/accessor oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "class decorator replacement static/accessor differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn decorated_member_same_key_last_definition_wins_match_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("decorated-member-same-key-last-wins-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // The staged decorator observes/wraps the later live descriptor, then call returns
    // the later method's result.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function wrap(value, context) {
  log(`apply:${context.kind}:${String(context.name)}`);
  return function (...args) {
    log(`call:decorated`);
    return value.apply(this, args);
  };
}
class Fixture {
  @wrap
  method() { return 'first'; }
  method() { return 'second'; }
}
const instance = new Fixture();
log(`result:${instance.method()}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source)
        .expect("write decorated member same-key last-definition-wins fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript decorated member same-key last-definition-wins oracle");
    assert!(
        status.success(),
        "TypeScript decorated member same-key last-definition-wins oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "decorated member same-key last-definition-wins differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn decorated_member_distinct_computed_keys_same_runtime_key_match_tsc_oracle_in_every_execution_mode()
 {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!(
        "decorated-member-distinct-computed-same-runtime-key-{}",
        process::id()
    );
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Distinct computed key expressions resolve to the same runtime property key in
    // source order. The staged decorator observes the later live descriptor, then
    // call/result use the later undecorated method.
    let source = r#"const trace = [];
function log(value) { trace.push(value); }
function key(label) { log(`key:${label}`); return 'method'; }
function wrap(value, context) {
  log(`apply:${context.kind}:${String(context.name)}`);
  return function (...args) {
    log(`call:decorated`);
    return value.apply(this, args);
  };
}
class Fixture {
  @wrap
  [key('first')]() { return 'first'; }
  [key('second')]() { return 'second'; }
}
const instance = new Fixture();
log(`result:${instance.method()}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source)
        .expect("write decorated member distinct computed same-runtime-key fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript decorated member distinct computed same-runtime-key oracle");
    assert!(
        status.success(),
        "TypeScript decorated member distinct computed same-runtime-key oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "decorated member distinct computed same-runtime-key differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn computed_member_source_order_key_once_and_accessor_init_match_tsc_oracle_in_every_execution_mode()
 {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!(
        "computed-member-source-order-key-once-accessor-init-{}",
        process::id()
    );
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.js");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Undecorated computed members must evaluate/install before later decorated
    // computed members in source order; plain computed instance fields must
    // capture their key once at class definition while initializer runs per
    // instance; decorated auto-accessor init() must observe the captured
    // initializer value.
    let source = r#"const trace = [];
const keyCounts = { plain: 0, decorated: 0, field: 0, acc: 0 };
function log(value) { trace.push(value); }
function key(label) {
  keyCounts[label] += 1;
  log(`key:${label}:${keyCounts[label]}`);
  return label === 'plain' ? 'plainMethod'
    : label === 'decorated' ? 'decorMethod'
    : label === 'field' ? 'plainField'
    : 'accProp';
}
function dec(label) {
  log(`evaluate:${label}`);
  return (_value, context) => {
    log(`apply:${label}:${String(context.name)}`);
  };
}
function accessorInit() {
  log('evaluate:accInit');
  return (target, context) => {
    log(`apply:accInit:${String(context.name)}`);
    return {
      get() { return target.get.call(this); },
      set(value) { target.set.call(this, value); },
      init(initial) { log(`accInit:${initial}`); return initial * 2; },
    };
  };
}
class Fixture {
  [key('plain')]() { return 'plain'; }
  @dec('decorated')
  [key('decorated')]() { return 'decorated'; }
  [key('field')] = (log('init:field'), 10);
  @accessorInit()
  accessor [key('acc')] = 3;
}
log('--- after class definition ---');
const first = new Fixture();
const second = new Fixture();
log(`plainMethod:${first.plainMethod()}`);
log(`decorMethod:${first.decorMethod()}`);
log(`plainField:${first.plainField}:${second.plainField}`);
log(`accProp:${first.accProp}`);
log(`keyCounts:plain=${keyCounts.plain}:decorated=${keyCounts.decorated}:field=${keyCounts.field}:acc=${keyCounts.acc}`);
console.log(trace.join('\n'));
"#;
    fs::write(&source_path, source)
        .expect("write computed member source-order/key-once/accessor-init fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
        "--allowJs".into(),
        "--checkJs".into(),
        "false".into(),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript computed member source-order/key-once/accessor-init oracle");
    assert!(
        status.success(),
        "TypeScript computed member source-order/key-once/accessor-init oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "computed member source-order/key-once/accessor-init differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn sync_explicit_resource_management_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("sync-explicit-resource-management-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.ts");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Observable trace: declaration/use order, sibling and nested LIFO disposal,
    // and per-iteration disposal via loop-head `for (using r of ...)`.
    let source = r#"(() => {
  const out: string[] = [];

  function res(name: string) {
    return {
      name,
      [Symbol.dispose]() {
        out.push(`dispose:${name}`);
      },
    };
  }

  {
    using a = res("a");
    using b = res("b");
    out.push(`use:${a.name},${b.name}`);
  }
  out.push("block.after");

  {
    using outer = res("outer");
    {
      using inner = res("inner");
      out.push(`nested.use:${outer.name},${inner.name}`);
    }
    out.push("nested.after-inner");
  }
  out.push("nested.after-outer");

  for (using r of [res("i0"), res("i1")]) {
    out.push(`loop.use:${r.name}`);
  }
  out.push("loop.after");

  console.log(out.join("\n"));
})();
"#;
    fs::write(&source_path, source).expect("write sync explicit resource management fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--lib".into(),
        "es2022,dom,esnext.disposable".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript sync explicit resource management oracle");
    assert!(
        status.success(),
        "TypeScript sync explicit resource management oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "sync explicit resource management differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn async_explicit_resource_management_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("async-explicit-resource-management-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.ts");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Observable trace: declaration/use order, sibling and nested LIFO disposal,
    // and per-iteration disposal via loop-head `for (await using r of ...)`.
    let source = r#"(async () => {
  const out: string[] = [];

  function res(name: string) {
    return {
      name,
      async [Symbol.asyncDispose]() {
        out.push(`dispose:${name}`);
      },
    };
  }

  function syncFallback(name: string) {
    const rejected = Promise.reject(new Error(`ignored:${name}`));
    rejected.catch(() => {});
    return {
      name,
      [Symbol.dispose]() {
        out.push(`dispose:${name}`);
        return rejected;
      },
    };
  }

  {
    await using a = res("a");
    await using b = res("b");
    out.push(`use:${a.name},${b.name}`);
  }
  out.push("block.after");

  {
    await using outer = res("outer");
    {
      await using inner = res("inner");
      out.push(`nested.use:${outer.name},${inner.name}`);
    }
    out.push("nested.after-inner");
  }
  out.push("nested.after-outer");

  {
    await using fallback = syncFallback("ignored-reject");
    out.push(`use:${fallback.name}`);
  }
  out.push("fallback.after");

  {
    const empty = null as never;
    await using nullable = empty;
    out.push("nullish.use");
  }
  out.push("nullish.after");

  for (await using r of [res("i0"), res("i1")]) {
    out.push(`loop.use:${r.name}`);
  }
  out.push("loop.after");

  console.log(out.join("\n"));
})();
"#;
    fs::write(&source_path, source).expect("write async explicit resource management fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--lib".into(),
        "es2022,dom,esnext.disposable".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript async explicit resource management oracle");
    assert!(
        status.success(),
        "TypeScript async explicit resource management oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "async explicit resource management differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn sync_explicit_resource_management_suppression_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!(
        "sync-explicit-resource-management-suppression-{}",
        process::id()
    );
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.ts");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Observable trace: when body and every LIFO disposer throw, the catch receives a
    // nested SuppressedError chain exposing outer disposal, inner disposal, and body.
    let source = r#"(() => {
  const out: string[] = [];

  function bad(name: string) {
    return {
      [Symbol.dispose]() {
        throw new Error(name);
      },
    };
  }

  try {
    using a = bad("dispose-a");
    using b = bad("dispose-b");
    throw new Error("body");
  } catch (error) {
    out.push(`${error.constructor.name}:${error.error.message}:${error.suppressed.error.message}:${error.suppressed.suppressed.message}`);
  }

  console.log(out.join("\n"));
})();
"#;
    fs::write(&source_path, source)
        .expect("write sync explicit resource management suppression fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--lib".into(),
        "es2022,dom,esnext.disposable".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript sync explicit resource management suppression oracle");
    assert!(
        status.success(),
        "TypeScript sync explicit resource management suppression oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "sync explicit resource management suppression differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn resource_management_abrupt_completion_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("resource-management-abrupt-completion-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.ts");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Observable chronological trace over custom iterators: return through enclosing
    // finally, same-loop continue without iterator.return, break with user-finally ->
    // dispose -> iterator.return, and labeled continue outer closing the inner iterator.
    let source = r#"(() => {
  const out: string[] = [];

  function res(name: string) {
    return {
      name,
      [Symbol.dispose]() {
        out.push(`dispose:${name}`);
      },
    };
  }

  function iterable(label: string, count: number) {
    let i = 0;
    return {
      [Symbol.iterator]() {
        return {
          next() {
            if (i < count) {
              const idx = i;
              i += 1;
              out.push(`${label}:next:${idx}`);
              return {
                value: {
                  idx,
                  [Symbol.dispose]() {
                    out.push(`${label}:dispose:${idx}`);
                  },
                },
                done: false,
              };
            }
            out.push(`${label}:next:done`);
            return { value: undefined, done: true };
          },
          return() {
            out.push(`${label}:iterator:return`);
            return { value: undefined, done: true };
          },
        };
      },
    };
  }

  function f() {
    try {
      {
        using r = res("return");
        out.push("return:body");
        return "value";
      }
    } finally {
      out.push("return:finally");
    }
  }
  out.push(`return:result:${f()}`);

  for (using r of iterable("continue", 2)) {
    out.push(`continue:body:${r.idx}`);
    if (r.idx === 0) {
      continue;
    }
  }
  out.push("continue:after");

  for (using r of iterable("break", 2)) {
    try {
      out.push(`break:body:${r.idx}`);
      if (r.idx === 0) {
        break;
      }
    } finally {
      out.push(`break:body-finally:${r.idx}`);
    }
  }
  out.push("break:after-loop");

  outer: for (let o = 0; o < 2; o += 1) {
    out.push(`labeled:outer:${o}`);
    for (using r of iterable(`labeled-inner-${o}`, 2)) {
      try {
        out.push(`labeled:body:${o}:${r.idx}`);
        if (r.idx === 0) {
          continue outer;
        }
      } finally {
        out.push(`labeled:body-finally:${o}:${r.idx}`);
      }
    }
  }
  out.push("labeled:after");

  console.log(out.join("\n"));
})();
"#;
    fs::write(&source_path, source).expect("write resource management abrupt completion fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--lib".into(),
        "es2022,dom,esnext.disposable".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript resource management abrupt completion oracle");
    assert!(
        status.success(),
        "TypeScript resource management abrupt completion oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "resource management abrupt completion differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn async_explicit_resource_management_suppression_matches_tsc_oracle_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!(
        "async-explicit-resource-management-suppression-{}",
        process::id()
    );
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let source_relative = format!("{source_dir}/{id}.ts");
    let source_path = root.join(&source_relative);
    let transpiled_relative = format!("{source_dir}/oracles/{id}.js");
    let _transpiled_path = root.join(&transpiled_relative);

    // Observable trace: each async disposer queues a microtask before Await, then throws.
    // The chain includes both SuppressedError nodes.
    let source = r#"(async () => {
  const out: string[] = [];

  function bad(name: string) {
    return {
      async [Symbol.asyncDispose]() {
        out.push(`${name}:start`);
        queueMicrotask(() => out.push(`${name}:checkpoint`));
        await Promise.resolve();
        out.push(`${name}:throw`);
        throw new Error(name);
      },
    };
  }

  try {
    await using a = bad("dispose-a");
    await using b = bad("dispose-b");
    throw new Error("body");
  } catch (error) {
    out.push(`${error.constructor.name}:${error.error.message}:${error.suppressed.constructor.name}:${error.suppressed.error.message}:${error.suppressed.suppressed.message}`);
  }

  console.log(out.join("\n"));
})();
"#;
    fs::write(&source_path, source)
        .expect("write async explicit resource management suppression fixture");
    let tsc_args: Vec<String> = vec![
        "--ignoreConfig".into(),
        "--target".into(),
        "es2022".into(),
        "--module".into(),
        "commonjs".into(),
        "--strict".into(),
        "false".into(),
        "--esModuleInterop".into(),
        "--skipLibCheck".into(),
        "--lib".into(),
        "es2022,dom,esnext.disposable".into(),
        "--rootDir".into(),
        source_dir.clone(),
        "--outDir".into(),
        format!("{source_dir}/oracles"),
    ];
    let status = tsc_command(&root)
        .arg(&source_path)
        .args(&tsc_args)
        .current_dir(&root)
        .status()
        .expect("run TypeScript async explicit resource management suppression oracle");
    assert!(
        status.success(),
        "TypeScript async explicit resource management suppression oracle failed with {status}"
    );
    let spec = CaseSpec {
        id: id.clone(),
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint: transpiled_relative,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: Vec::new(),
    };
    let bamts = BamtsRunner::new(&root);
    let oracle = NodeOracle::discover(&root).expect("Node oracle available");
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    let actual_spec = CaseSpec {
        entrypoint: source_relative,
        ..spec.clone()
    };
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&actual_spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "async explicit resource management suppression differential failures:\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn with_statement_semantics_matches_node_in_every_execution_mode() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let id = format!("with-statement-{}", process::id());
    let source_dir = format!("target/{id}");
    fs::create_dir_all(root.join(&source_dir)).expect("create fixture directory");
    let entrypoint = format!("{source_dir}/{id}.js");
    let path = root.join(&entrypoint);
    fs::write(
        &path,
        r#"(function () {
  var trace = [];

  // with object coercion and normal read/write
  with ("abc") {
    trace.push("coerce:" + length);
  }
  var box = { n: 1 };
  with (box) {
    trace.push("read:" + n);
    n = 10;
  }
  trace.push("box.n=" + box.n);

  // frozen identifier assignment reference
  var outer = 0;
  const o = { x: 1 };
  with (o) {
    x = (delete o.x, 2);
  }
  trace.push("frozen:" + (o.x === 2 && outer === 0));

  // direct identifier method call preserves with object this
  var receiver = {
    who: "receiver",
    method: function () { return this.who; }
  };
  with (receiver) {
    trace.push("method:" + method());
  }

  // nested with chooses inner object
  var outerObj = { v: "outer" };
  var innerObj = { v: "inner" };
  with (outerObj) {
    with (innerObj) {
      trace.push("nested:" + v);
    }
  }

  // closure formed in with body resolves captured property after exit;
  // function parameter of same name shadows it
  var captured = { prop: "captured-value" };
  var capturedGetter;
  var capturedShadowed;
  with (captured) {
    capturedGetter = function () { return prop; };
    capturedShadowed = function (prop) { return prop; };
  }
  trace.push("closure.captured:" + capturedGetter());
  trace.push("closure.shadowed:" + capturedShadowed("param-value"));

  // lexical declaration inside with shadows the with object;
  // closure formed in with body resolves the lexical binding after exit;
  // function parameter of same name shadows the lexical binding
  var lexicalBox = { lexical: "with-object-value" };
  var lexicalGetter;
  var lexicalShadowed;
  with (lexicalBox) {
    let lexical = "lexical";
    lexicalGetter = function () { return lexical; };
    lexicalShadowed = function (lexical) { return lexical; };
  }
  trace.push("closure.lexical:" + lexicalGetter());
  trace.push("closure.lexicalShadowed:" + lexicalShadowed("param-value"));

  // typeof and delete target a matching with property
  var probe = { exists: 42 };
  with (probe) {
    trace.push("typeof:" + typeof exists);
    trace.push("delete:" + delete exists);
  }
  trace.push("probe.exists=" + ("exists" in probe));

  // Symbol.unscopables: const values = "outer"; with ([]) { values }
  const values = "outer";
  with ([]) {
    trace.push("unscopables:" + values);
  }

  console.log(trace.join("\n"));
})();"#,
    )
    .expect("write with-statement fixture");
    let spec = CaseSpec {
        id,
        provenance: local_test_provenance(&root, &source_dir),
        license: "UNLICENSED".to_owned(),
        source_dir: source_dir.clone(),
        entrypoint,
        node_args: Vec::new(),
        expected_timeout_ms: 10_000,
        constructs: Vec::new(),
        source_files: Vec::new(),
        compiler_args: vec!["-A".into(), "no-with".into()],
    };
    let oracle = NodeOracle::discover(&root).expect("the pinned Node oracle must be available");
    let bamts = BamtsRunner::new(&root);
    let expected = oracle.run_case(&spec);
    let mut failures = Vec::new();
    for mode in ExecutionMode::ALL {
        let actual = bamts.run_case(&spec, mode);
        compare_case(&spec.id, mode, &expected, &actual, &mut failures);
    }
    fs::remove_dir_all(root.join(&source_dir)).expect("remove fixture directory");
    assert!(
        failures.is_empty(),
        "with-statement differential failures:\n{}",
        failures.join("\n\n")
    );
}

fn bamts_outcome_stage(mode: ExecutionMode) -> CorpusStage {
    match mode {
        ExecutionMode::Interpreter | ExecutionMode::Jit => CorpusStage::Evaluate,
        ExecutionMode::Aot => CorpusStage::Spawn,
    }
}

fn evidence(outcome: &OracleOutcome) -> String {
    format!(
        "exit={:?}, signal={:?}, timed_out={}, stdout_len={}, stdout_truncated={}, stdout=`{}`, stderr_len={}, stderr_truncated={}, stderr=`{}`",
        outcome.exit_code,
        outcome.signal,
        outcome.timed_out,
        outcome.stdout.len(),
        outcome.stdout_truncated,
        preview(&outcome.stdout),
        outcome.stderr.len(),
        outcome.stderr_truncated,
        preview(&outcome.stderr),
    )
}

fn first_difference(expected: &[u8], actual: &[u8]) -> String {
    let shared = expected.len().min(actual.len());
    if let Some(index) = (0..shared).find(|&index| expected[index] != actual[index]) {
        return format!(
            "byte {index}: Node=0x{:02x}, BamTS=0x{:02x}",
            expected[index], actual[index]
        );
    }
    format!(
        "shared prefix is identical; Node length={}, BamTS length={}",
        expected.len(),
        actual.len()
    )
}

fn preview(bytes: &[u8]) -> String {
    const PREVIEW_BYTES: usize = 256;
    let mut rendered = bytes
        .iter()
        .take(PREVIEW_BYTES)
        .flat_map(|byte| byte.escape_ascii())
        .map(char::from)
        .collect::<String>();
    if bytes.len() > PREVIEW_BYTES {
        rendered.push_str("...");
    }
    rendered
}

#[cfg(test)]
mod formatting_tests {
    use std::ffi::OsString;

    use bamts_bytecode::{ConstantId, FunctionId, Instruction, Pc, Register};
    use bamts_cli::driver::DriverError;
    use bamts_runtime::{NativeError, RuntimeError, RuntimeErrorKind, RuntimeSource};

    use super::*;

    fn outcome(stdout: &[u8]) -> OracleOutcome {
        OracleOutcome {
            timed_out: false,
            exit_code: Some(0),
            signal: None,
            stdout: stdout.to_vec(),
            stdout_truncated: false,
            stderr: Vec::new(),
            stderr_truncated: false,
            compile_stderr: Vec::new(),
            compile_stderr_truncated: false,
        }
    }

    #[test]
    fn formats_check_failure_with_its_first_diagnostic_code() {
        let failure = CorpusFailure::from_driver_error(&DriverError::Diagnostics {
            rendered: "error BAMTS-C004: unresolved name".to_owned(),
            truncation: None,
        });

        assert_eq!(failure.stage, CorpusStage::Check);
        assert!(
            failure
                .to_string()
                .contains("stage=check: diagnostic=BAMTS-C004")
        );
    }

    #[test]
    fn formats_import_at_pc_zero_as_runtime_evaluation() {
        let failure = CorpusFailure::from_driver_error(&DriverError::Native(NativeError::Runtime(
            RuntimeError {
                kind: RuntimeErrorKind::FuelExhausted { limit: 1 },
                function: FunctionId::new(0),
                pc: Pc::new(0),
                source: RuntimeSource {
                    function_name: None,
                    instruction: Instruction::Import {
                        dst: Register::new(0),
                        specifier: ConstantId::new(0),
                    },
                },
            },
        )));

        let rendered = failure.to_string();
        assert_eq!(failure.stage, CorpusStage::Evaluate);
        assert!(rendered.contains("runtime function=0 pc=0 opcode=Import"));
    }

    #[test]
    fn formats_link_failure_at_link_stage() {
        let failure = CorpusFailure::from_driver_error(&DriverError::ToolchainMissing {
            program: OsString::from("missing-cc"),
        });

        assert_eq!(failure.stage, CorpusStage::Link);
        assert!(failure.to_string().starts_with("stage=link:"));
    }

    #[test]
    fn formats_timeout_at_the_execution_stage() {
        let expected = OracleOutcome {
            timed_out: true,
            exit_code: None,
            signal: Some(9),
            stdout: b"partial".to_vec(),
            stdout_truncated: false,
            stderr: Vec::new(),
            stderr_truncated: false,
            compile_stderr: Vec::new(),
            compile_stderr_truncated: false,
        };
        let actual = outcome(b"partial");
        let mut failures = Vec::new();

        compare_case(
            "timeout",
            ExecutionMode::Jit,
            &Ok(expected),
            &Ok(actual),
            &mut failures,
        );

        assert_eq!(failures.len(), 1);
        assert!(failures[0].contains("stage=spawn Node oracle did not produce a complete result"));
        assert!(failures[0].contains("stdout=`partial`"));
    }

    #[test]
    fn formats_byte_difference_at_compare_stage() {
        let mut failures = Vec::new();

        compare_case(
            "bytes",
            ExecutionMode::Aot,
            &Ok(outcome(b"a")),
            &Ok(outcome(b"b")),
            &mut failures,
        );

        assert_eq!(failures.len(), 1);
        assert!(failures[0].contains("stage=compare stdout bytes or exit code differ"));
        assert!(failures[0].contains("byte 0: Node=0x61, BamTS=0x62"));
    }
}
