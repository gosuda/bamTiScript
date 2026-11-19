use std::env;
use std::path::PathBuf;

pub fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

pub fn authority_root() -> PathBuf {
    PathBuf::from(env::var("BAMTS_AUTHORITY_ROOT").unwrap_or_else(|_| {
        "/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests".to_owned()
    }))
}

pub fn baseline_dir() -> PathBuf {
    authority_root().join("tests/baselines/reference")
}

pub fn authority_case_path(logical: &str) -> PathBuf {
    let stripped = logical
        .strip_prefix("compiler/tests/cases/")
        .or_else(|| logical.strip_prefix("conformance/tests/cases/"))
        .unwrap_or(logical);
    authority_root().join("tests/cases").join(stripped)
}
