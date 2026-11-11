//! Upstream-compatible module-resolution trace rendering.
//!
//! The rendered ESM/CJS mode word follows [`ResolutionMode`], and candidate
//! narration follows [`ResolutionFlavor`] so it matches the order the resolver
//! actually probes.
use super::{
    ProjectRoot, ResolutionFlavor,
    resolution::{
        ModuleResolutionKind, ResolutionError, ResolutionMode, ResolutionTraceStep, ResolvedModule,
    },
};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

/// Resolution features whose upstream trace templates are not emitted yet.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UnsupportedTraceKind {
    /// Directory/package lookups (`package.json`, `index.*`) are not rendered.
    DirectoryPackage,
    /// `#imports` package redirects are not resolved by this tracer.
    PackageImport,
    /// Bare package specifiers are not resolved by this tracer.
    PackageName,
    /// `paths` mappings are not rendered.
    PathsMapping,
}

/// Ordered `traceResolution` lines collected across one compilation.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolutionTraceLog {
    lines: Vec<String>,
    unsupported: BTreeSet<UnsupportedTraceKind>,
}

enum BareItem<'a> {
    Skip(&'a PathBuf),
    File(&'a PathBuf, bool),
}
impl ResolutionTraceLog {
    #[must_use]
    pub fn lines(&self) -> &[String] {
        &self.lines
    }

    #[must_use]
    pub fn unsupported(&self) -> &BTreeSet<UnsupportedTraceKind> {
        &self.unsupported
    }
    pub(crate) fn record_module(
        &mut self,
        root: &ProjectRoot,
        importer: &Path,
        specifier: &str,
        strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
        explicit_kind: bool,
        cached: bool,
        result: &Result<ResolvedModule, ResolutionError>,
    ) {
        if !(specifier.starts_with("./") || specifier.starts_with("../")) {
            if specifier.starts_with('#') {
                self.unsupported
                    .insert(UnsupportedTraceKind::PackageImport);
                return;
            }
            if strategy.0 == ModuleResolutionKind::Bundler
                && !cached
                && self.render_bundler_bare(
                    importer,
                    specifier,
                    (strategy.0, strategy.1),
                    explicit_kind,
                    result,
                )
            {
                return;
            }
            self.unsupported.insert(UnsupportedTraceKind::PackageName);
            return;
        }

        let directory = importer.parent().unwrap_or_else(|| root.path());
        let Ok(candidate_location) = root.resolve_from(directory, specifier) else {
            return;
        };
        let resolved_parent = result
            .as_ref()
            .ok()
            .and_then(|resolved| resolved.path().parent().map(Path::to_path_buf));
        let extension = candidate_location
            .extension()
            .and_then(|value| value.to_str());

        self.lines.push(format!(
            "======== Resolving module '{specifier}' from '{}'. ========",
            display_path(importer)
        ));
        if cached {
            self.lines.push(format!(
                "Resolution for module '{specifier}' was found in cache from location '{}'.",
                display_path(directory)
            ));
        } else {
            if explicit_kind {
                self.lines.push(format!(
                    "Explicitly specified module resolution kind: '{}'.",
                    strategy.0.trace_name()
                ));
            } else {
                self.lines.push(format!(
                    "Module resolution kind is not specified, using '{}'.",
                    strategy.0.trace_name()
                ));
            }
            self.lines.push(format!(
                "Resolving in {} mode with conditions '{}', 'types'.",
                match strategy.1 {
                    ResolutionMode::Import => "ESM",
                    ResolutionMode::Require => "CJS",
                },
                strategy.1.as_str()
            ));
            self.lines.push(format!(
                "Loading module as file / folder, candidate module location '{}', target file types: TypeScript, JavaScript, Declaration, JSON.",
                display_path(&candidate_location)
            ));
            self.render_candidates(&candidate_location, extension, strategy.2, result);
        }

        match result {
            Ok(resolved) => self.lines.push(format!(
                "======== Module name '{specifier}' was successfully resolved to '{}'. ========",
                display_path(resolved.path())
            )),
            Err(_) => self.lines.push(format!(
                "======== Module name '{specifier}' was not resolved. ========"
            )),
        }
        if resolved_parent.is_some_and(|parent| parent == candidate_location) {
            self.unsupported
                .insert(UnsupportedTraceKind::DirectoryPackage);
        }
        if extension.is_none() && !result.is_ok() {
            self.unsupported
                .insert(UnsupportedTraceKind::DirectoryPackage);
        }
    }


    fn render_bundler_bare(
        &mut self,
        importer: &Path,
        specifier: &str,
        strategy: (ModuleResolutionKind, ResolutionMode),
        explicit_kind: bool,
        result: &Result<ResolvedModule, ResolutionError>,
    ) -> bool {
        let trace = match result {
            Ok(resolved) => Some(resolved.trace()),
            Err(error) => error.trace(),
        };
        let Some(trace) = trace else { return false };
        if Path::new(specifier).extension().is_some() || specifier.starts_with('@') {
            return false;
        }
        let mut probes = Vec::new();
        let mut preferred = Vec::new();
        let mut fallback = Vec::new();
        let mut realpath = None;
        let mut in_fallback = false;
        for step in trace.steps() {
            match step {
                ResolutionTraceStep::PackageJsonProbe { path, exists } => {
                    if *exists {
                        return false;
                    }
                    probes.push(path);
                }
                ResolutionTraceStep::NodeModulesWalk {
                    directory,
                    exists,
                    fallback: is_fallback,
                } => {
                    if *is_fallback {
                        in_fallback = true;
                    }
                    if !*exists {
                        let items = if *is_fallback { &mut fallback } else { &mut preferred };
                        items.push(BareItem::Skip(directory));
                    }
                }
                ResolutionTraceStep::Candidate { path, exists } => {
                    let items = if in_fallback { &mut fallback } else { &mut preferred };
                    items.push(BareItem::File(path, *exists));
                }
                ResolutionTraceStep::Resolved { path } => {
                    realpath = Some(path);
                }
                ResolutionTraceStep::PackageJson { .. }
                | ResolutionTraceStep::PathsMatch { .. }
                | ResolutionTraceStep::TypesFallback { .. } => return false,
                _ => {}
            }
        }
        self.lines.push(format!(
            "======== Resolving module '{specifier}' from '{}'. ========",
            display_path(importer)
        ));
        if explicit_kind {
            self.lines.push(format!(
                "Explicitly specified module resolution kind: '{}'.",
                strategy.0.trace_name()
            ));
        } else {
            self.lines.push(format!(
                "Module resolution kind is not specified, using '{}'.",
                strategy.0.trace_name()
            ));
        }
        let condition = match strategy.1 {
            ResolutionMode::Import => "import",
            ResolutionMode::Require => "require",
        };
        self.lines.push(format!(
            "Resolving in CJS mode with conditions '{condition}', 'types'."
        ));
        for path in &probes {
            self.lines.push(format!("File '{}' does not exist.", display_path(path)));
        }
        self.lines.push(format!(
            "Loading module '{specifier}' from 'node_modules' folder, target file types: TypeScript, JavaScript, Declaration, JSON."
        ));
        self.lines.push(
            "Searching all ancestor node_modules directories for preferred extensions: TypeScript, Declaration."
                .to_string(),
        );
        for item in &preferred {
            match item {
                BareItem::Skip(directory) => self.lines.push(format!(
                    "Directory '{}/node_modules' does not exist, skipping all lookups in it.",
                    display_path(directory)
                )),
                BareItem::File(path, true) => self.lines.push(format!(
                    "File '{}' exists - use it as a name resolution result.",
                    display_path(path)
                )),
                BareItem::File(path, false) => {
                    self.lines.push(format!("File '{}' does not exist.", display_path(path)))
                }
            }
        }
        if realpath.is_none() || !fallback.is_empty() {
            self.lines.push(
                "Searching all ancestor node_modules directories for fallback extensions: JavaScript, JSON."
                    .to_string(),
            );
            for item in &fallback {
                match item {
                    BareItem::Skip(directory) => self.lines.push(format!(
                        "Directory '{}/node_modules' does not exist, skipping all lookups in it.",
                        display_path(directory)
                    )),
                    BareItem::File(path, true) => self.lines.push(format!(
                        "File '{}' exists - use it as a name resolution result.",
                        display_path(path)
                    )),
                    BareItem::File(path, false) => self
                        .lines
                        .push(format!("File '{}' does not exist.", display_path(path))),
                }
            }
        }
        if let Some(path) = realpath {
            self.lines.push(format!(
                "Resolving real path for '{}', result '{}'.",
                display_path(path),
                display_path(path)
            ));
            self.lines.push(format!(
                "======== Module name '{specifier}' was successfully resolved to '{}'. ========",
                display_path(path)
            ));
        } else {
            self.lines.push(format!(
                "======== Module name '{specifier}' was not resolved. ========"
            ));
        }
        true
    }

    fn render_candidates(
        &mut self,
        requested: &Path,
        extension: Option<&str>,
        flavor: ResolutionFlavor,
        result: &Result<ResolvedModule, ResolutionError>,
    ) {
        let trace = match result {
            Ok(resolved) => Some(resolved.trace()),
            Err(error) => error.trace(),
        };
        let Some(trace) = trace else { return };
        let probes = trace
            .steps()
            .iter()
            .filter_map(|step| match step {
                ResolutionTraceStep::Candidate { path, exists } => Some((path.clone(), *exists)),
                ResolutionTraceStep::PathsMatch { .. } => {
                    self.unsupported.insert(UnsupportedTraceKind::PathsMapping);
                    None
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        if let Some(extension) = extension {
            self.lines.push(format!(
                "File name '{}' has a '.{extension}' extension - stripping it.",
                display_path(requested)
            ));
        }
        for candidate in upstream_candidates(requested, extension, flavor) {
            let Some(exists) = probes
                .iter()
                .find_map(|(path, exists)| (path == &candidate).then_some(*exists))
            else {
                continue;
            };
            self.lines.push(if exists {
                format!(
                    "File '{}' exists - use it as a name resolution result.",
                    display_path(&candidate)
                )
            } else {
                format!("File '{}' does not exist.", display_path(&candidate))
            });
            if exists {
                break;
            }
        }
    }
}

/// Upstream Bundler-mode probe order for the file-level candidates of one stem.
/// `ResolutionFlavor::Types` hoists the family's declaration candidate first,
/// mirroring the ordering [`crate::project::plan_relative_module`] applies.
fn upstream_candidates(
    requested: &Path,
    extension: Option<&str>,
    flavor: ResolutionFlavor,
) -> Vec<PathBuf> {
    let extensions: &[&str] = match (extension, flavor) {
        (None, ResolutionFlavor::Types) => &["d.ts", "ts", "tsx", "js", "jsx"],
        (None, ResolutionFlavor::Runtime) => &["ts", "tsx", "d.ts", "js", "jsx"],
        (Some("js"), ResolutionFlavor::Types) => &["d.ts", "ts", "tsx", "js"],
        (Some("js"), ResolutionFlavor::Runtime) => &["ts", "tsx", "d.ts", "js"],
        (Some("jsx"), ResolutionFlavor::Types) => &["d.ts", "tsx", "jsx"],
        (Some("jsx"), ResolutionFlavor::Runtime) => &["tsx", "d.ts", "jsx"],
        (Some("mjs"), ResolutionFlavor::Types) => &["d.mts", "mts", "mjs"],
        (Some("mjs"), ResolutionFlavor::Runtime) => &["mts", "d.mts", "mjs"],
        (Some("cjs"), ResolutionFlavor::Types) => &["d.cts", "cts", "cjs"],
        (Some("cjs"), ResolutionFlavor::Runtime) => &["cts", "d.cts", "cjs"],
        (Some("ts" | "tsx" | "mts" | "cts"), _) => &[extension.expect("extension matched an arm")],
        (Some("json"), _) => &["json"],
        (Some(_), _) => &[],
    };
    extensions
        .iter()
        .map(|extension| requested.with_extension(extension))
        .collect()
}

/// Renders a path the way upstream traces do: forward slashes, lowercased drive.
///
/// Anything that looks for a path inside a rendered trace must build the text
/// with this function.
#[must_use]
pub fn display_path(path: &Path) -> String {
    let mut value = path.to_string_lossy().replace('\\', "/");
    if value.as_bytes().get(1) == Some(&b':') {
        value.make_ascii_lowercase();
    }
    value
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn types_flavor_hoists_declaration_candidate_per_family() {
        let requested = Path::new("/dir/index.js");
        assert_eq!(
            upstream_candidates(requested, Some("js"), ResolutionFlavor::Runtime),
            vec![
                PathBuf::from("/dir/index.ts"),
                PathBuf::from("/dir/index.tsx"),
                PathBuf::from("/dir/index.d.ts"),
                PathBuf::from("/dir/index.js"),
            ]
        );
        assert_eq!(
            upstream_candidates(requested, Some("js"), ResolutionFlavor::Types)
                .first()
                .map(|path| path.as_path()),
            Some(Path::new("/dir/index.d.ts"))
        );
        assert_eq!(
            upstream_candidates(requested, None, ResolutionFlavor::Types)
                .first()
                .map(|path| path.as_path()),
            Some(Path::new("/dir/index.d.ts"))
        );
    }
}
