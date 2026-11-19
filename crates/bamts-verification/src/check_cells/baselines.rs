use super::*;

/// Build the stem/suffix groups once from the snapshot index (flat entries
/// only; `reference/project/…` rows are excluded).
pub fn baseline_groups(index: &SuiteIndex) -> BaselineGroups {
    let mut groups: BaselineGroups = BTreeMap::new();
    for entry in index.entries.values() {
        let Some(file_name) = entry.logical_path.strip_prefix(BASELINE_REFERENCE_PREFIX) else {
            continue;
        };
        if file_name.contains('/') {
            continue;
        }
        let Some((stem, extension, suffix)) = split_baseline_file_name(file_name) else {
            continue;
        };
        groups
            .entry((stem.to_owned(), extension.to_owned()))
            .or_default()
            .push((suffix.to_owned(), entry.logical_path.clone()));
    }
    groups
}

/// Split `<stem>[(suffix)].<ext>`; returns `None` for unrecognized names.
pub(super) fn split_baseline_file_name(file_name: &str) -> Option<(&str, &str, &str)> {
    let extensions = [
        ".errors.txt",
        ".trace.json",
        ".types",
        ".symbols",
        ".jsx",
        ".js.map",
        ".js",
    ];
    let extension = extensions
        .iter()
        .find(|extension| file_name.ends_with(*extension))?;
    let base = &file_name[..file_name.len() - extension.len()];
    if let Some(open) = base.find('(') {
        let suffix = &base[open..];
        if !suffix.ends_with(')') {
            return None;
        }
        Some((&base[..open], &extension[1..], suffix))
    } else {
        Some((base, &extension[1..], ""))
    }
}

/// Parse a `(opt=value,...)` baseline suffix and check whether it matches the
/// first-value compile options used for the current case.
pub(super) fn suffix_matches_options(suffix: &str, compile_options: &[(String, String)]) -> bool {
    let Some(inner) = suffix.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return suffix.is_empty();
    };
    if inner.is_empty() {
        return true;
    }
    let options: std::collections::HashMap<String, String> = compile_options
        .iter()
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect();
    for part in inner.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let Some((key, value)) = part.split_once('=') else {
            return false;
        };
        let key = key.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        let Some(compile_value) = options.get(&key) else {
            return false;
        };
        if compile_value.to_ascii_lowercase() != value {
            return false;
        }
    }
    true
}

/// The stem of a case logical path: basename minus extension, with `.d` kept
/// (`parserEnumDeclaration2.d.ts` ⇒ stem `parserEnumDeclaration2.d`).
pub fn case_stem(logical_path: &str) -> &str {
    let name = logical_path.rsplit('/').next().unwrap_or(logical_path);
    for suffix in [".tsx", ".ts", ".jsx", ".js", ".mts", ".cts", ".mjs", ".cjs"] {
        if let Some(stem) = name.strip_suffix(suffix) {
            return stem;
        }
    }
    name
}

/// The `tests/cases/<area>/` segment owning a harness logical path;
/// empty when the path carries no area (flat trees). Shared by the
/// facet samplers so baseline selection agrees on ownership.
#[must_use]
pub fn baseline_area(harness_logical: &str) -> &str {
    harness_logical
        .split("cases/")
        .nth(1)
        .and_then(|rest| rest.split('/').next())
        .unwrap_or("")
}

/// Resolve a `{stem}[ (variant)].{extension}` authority baseline file
/// under `base`, preferring the owning `area` directory when one stem
/// exists in several areas, then the variant matching the compile
/// options. Authority trees nest baselines one level down
/// (`reference/<area>/*`); the top level is scanned too.
#[must_use]
pub fn resolve_baseline_file(
    base: &Path,
    stem: &str,
    area: &str,
    extension: &str,
    pragmas: &CasePragmas,
) -> Option<std::path::PathBuf> {
    let area_dir = base.join(area);
    let mut dirs = Vec::new();
    if !area.is_empty() {
        dirs.push(area_dir.clone());
    }
    dirs.push(base.to_path_buf());
    if let Ok(entries) = fs::read_dir(base) {
        // `read_dir` order is filesystem-dependent: sort so the first
        // plain baseline found is deterministic across machines.
        let mut siblings: Vec<std::path::PathBuf> = entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.is_dir() && path != &area_dir)
            .collect();
        siblings.sort();
        dirs.extend(siblings);
    }
    let plain_name = format!("{stem}.{extension}");
    let prefix = format!("{stem}(");
    let suffix_end = format!(").{extension}");
    let mut plain: Option<(std::path::PathBuf, bool)> = None;
    let mut variants: Vec<(String, std::path::PathBuf, bool)> = Vec::new();
    for dir in &dirs {
        let in_area = dir == &area_dir;
        let Ok(entries) = fs::read_dir(dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_string();
            if name == plain_name && plain.is_none() {
                plain = Some((entry.path(), in_area));
            } else if name.starts_with(&prefix) && name.ends_with(&suffix_end) {
                let suffix = &name[prefix.len()..name.len() - suffix_end.len()];
                variants.push((suffix.to_owned(), entry.path(), in_area));
            }
        }
        if plain.is_some() {
            break;
        }
    }
    let compile_options: Vec<(String, String)> = pragmas
        .options
        .iter()
        .filter_map(|(name, values)| values.first().map(|v| (name.clone(), v.clone())))
        .collect();
    if !compile_options.is_empty() {
        let matches: Vec<&(String, std::path::PathBuf, bool)> = variants
            .iter()
            .filter(|(suffix, _, _)| baseline_suffix_matches(suffix, &compile_options))
            .collect();
        // Baselines are per-case files: a same-stem variant in another
        // area belongs to another case (the twin precedent). When the
        // owning area holds any stem file, the stem is owned: only
        // owning variants may match, else the owning plain file covers
        // generic options, else there is no compatible authority. The
        // cross-area pool stays for unowned stems only. Specificity
        // ranks within the pool, then filename, then full path.
        let owned: Vec<&(String, std::path::PathBuf, bool)> = matches
            .iter()
            .filter(|candidate| candidate.2)
            .copied()
            .collect();
        let stem_owned = !owned.is_empty()
            || variants.iter().any(|candidate| candidate.2)
            || plain.as_ref().is_some_and(|(_, in_area)| *in_area);
        let pool_source = if owned.is_empty() {
            if stem_owned {
                return plain
                    .as_ref()
                    .filter(|(_, in_area)| *in_area)
                    .map(|(path, _)| path.clone());
            }
            matches
        } else {
            owned
        };
        if !pool_source.is_empty() {
            // Pool rows are (specificity, suffix, path).
            let mut pool: Vec<(usize, &str, &std::path::PathBuf)> = pool_source
                .iter()
                .map(|candidate| {
                    let specificity = candidate
                        .0
                        .split(',')
                        .filter(|part| part.contains('='))
                        .count();
                    (specificity, candidate.0.as_str(), &candidate.1)
                })
                .collect();
            pool.sort_by(|a, b| {
                b.0.cmp(&a.0)
                    .then_with(|| a.1.cmp(b.1))
                    .then_with(|| a.2.cmp(b.2))
            });
            return Some(pool[0].2.clone());
        }
    }
    if let Some((plain, _)) = plain {
        return Some(plain);
    }
    variants.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)));
    variants.into_iter().next().map(|(_, p, _)| p)
}

/// Whether a `(variant)` suffix selects the given compile options.
fn baseline_suffix_matches(suffix: &str, compile_options: &[(String, String)]) -> bool {
    if suffix.is_empty() {
        return true;
    }
    let options: HashMap<String, String> = compile_options
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    for part in suffix.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let Some((key, value)) = part.split_once('=') else {
            return false;
        };
        let key = key.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        let Some(compile_value) = options.get(&key) else {
            return false;
        };
        if compile_value.to_ascii_lowercase() != value {
            return false;
        }
    }
    true
}

/// The case inputs (compiler/conformance/project/projects only matter here)
/// whose stem equals `stem`.
pub(super) fn case_inputs_with_stem<'a>(
    snapshot: &'a (impl SnapshotAssets + ?Sized),
    stem: &str,
) -> Vec<&'a str> {
    snapshot
        .index()
        .entries
        .values()
        .filter(|entry| {
            matches!(entry.asset_kind, crate::suite::AssetKind::CaseInput)
                && case_stem(&entry.logical_path) == stem
        })
        .map(|entry| entry.logical_path.as_str())
        .collect()
}

/// The first `//// [path] ////` marker of a baseline blob, if any.
pub(super) fn baseline_owner(
    snapshot: &(impl SnapshotAssets + ?Sized),
    logical_path: &str,
) -> Result<(Option<String>, String)> {
    let bytes = read_verified_snapshot_asset(snapshot, logical_path)?;
    let text = String::from_utf8_lossy(&bytes).into_owned();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("//// [") {
            return Ok((
                rest.split_once("] ////")
                    .map(|(path, _)| path.trim().to_owned()),
                text,
            ));
        }
        if !line.is_empty() {
            return Ok((None, text));
        }
    }
    Ok((None, text))
}

pub(super) fn resolve_stem_baseline(
    groups: &BaselineGroups,
    logical_path: &str,
    extension: &str,
    compile_options: &[(String, String)],
) -> Result<Option<String>> {
    let stem = case_stem(logical_path);
    let Some(candidates) = groups.get(&(stem.to_owned(), extension.to_owned())) else {
        return Ok(None);
    };
    if !compile_options.is_empty() {
        let matches: Vec<_> = candidates
            .iter()
            .filter(|(suffix, _)| {
                !suffix.is_empty() && suffix_matches_options(suffix, compile_options)
            })
            .collect();
        if matches.len() > 1 {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("ambiguous `{extension}` baseline selection for `{logical_path}`"),
            ));
        }
        if let Some((_, path)) = matches.first() {
            return Ok(Some((*path).clone()));
        }
    }
    let plains: Vec<_> = candidates
        .iter()
        .filter(|(suffix, _)| suffix.is_empty())
        .collect();
    if plains.len() > 1 {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!("duplicate plain `{extension}` baselines for `{logical_path}`"),
        ));
    }
    if let Some((_, path)) = plains.first() {
        return Ok(Some((*path).clone()));
    }
    Ok(candidates
        .iter()
        .min_by(|left, right| left.0.cmp(&right.0))
        .map(|(_, path)| path.clone()))
}
