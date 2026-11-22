use super::*;

/// Parse the `// @<name>: <value>` directive block of a case text.
///
/// Only whole-line directives are recognized. `@filename:` units are not
/// options; everything else is recorded with a lowercased name, comma-split
/// values, and `@noTypesAndSymbols: true` pinned to the suppression flag.
pub fn parse_case_pragmas(text: &str) -> CasePragmas {
    let mut options = Vec::new();
    let mut no_types_and_symbols = false;
    for line in text.lines() {
        let Some((name, value)) = directive_parts(line) else {
            continue;
        };
        let name = name.to_ascii_lowercase();
        let value = value.trim();
        if name == "filename" {
            continue;
        }
        if name == "notypesandsymbols" {
            no_types_and_symbols |= value.eq_ignore_ascii_case("true");
            continue;
        }
        let values: Vec<String> = value
            .split(',')
            .map(|part| part.trim().to_owned())
            .filter(|part| !part.is_empty())
            .collect();
        options.push((name, values));
    }
    CasePragmas {
        options,
        no_types_and_symbols,
    }
}

/// Split one whole-line directive into its `(name, value)` pair under
/// upstream's option-directive grammar `^//\s*@\w+\s*:`: exactly two leading
/// slashes, a single ASCII-word option name, then a colon. This is the one
/// grammar pragma parsing, unit splitting, and directive stripping share,
/// so `///` reference directives, `////` lines, and multi-word `@param x:`
/// forms are content on every path. The value keeps its post-colon spacing;
/// callers trim it.
pub(super) fn directive_parts(line: &str) -> Option<(&str, &str)> {
    // A leading U+FEFF (BOM) may precede the `//` in files saved with a
    // byte-order mark; strip it before the directive test so coordinates
    // are not shifted by the invisible character.
    let line = line.strip_prefix('\u{feff}').unwrap_or(line);
    let rest = line.strip_prefix("//")?;
    // A third leading slash is a `///` directive, not a `// @option`.
    if rest.starts_with('/') {
        return None;
    }
    let body = rest.trim_start().strip_prefix('@')?;
    let name_len = body
        .bytes()
        .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        .count();
    if name_len == 0 {
        return None;
    }
    let (name, rest) = body.split_at(name_len);
    let value = rest.trim_start().strip_prefix(':')?;
    Some((name, value))
}

/// Strip every whole-line `// @name: value` compiler-option directive from a
/// unit's compiled content, reproducing upstream `makeUnitsFromTest`.
///
/// TypeScript removes each such line (global options and `@filename:` markers
/// alike) before compiling, joins the surviving lines with `\n`, and — because
/// the first accumulated chunk starts empty — collapses the leading blank lines
/// that a stripped prologue leaves behind. Reproducing all three keeps the
/// compiled source, and therefore every emitted `.errors.txt`/`.types`/
/// `.symbols` position, numbered exactly as the baselines are.
pub(super) fn strip_directive_lines(text: &str) -> String {
    // Upstream's `lineDelimiter` splits on `\r?\n` per line, so a CRLF line
    // and a bare `\n` line are distinct lines even within one unit;
    // normalizing `\r\n` to `\n` before splitting reproduces exactly that
    // line set (a lone `\r` is not a delimiter on either side).
    let normalized = text.replace("\r\n", "\n");
    let lines: Vec<&str> = normalized.split('\n').collect();
    let mut content: Option<String> = None;
    for line in lines {
        if is_option_directive_line(line) {
            continue;
        }
        match &mut content {
            None => content = Some(line.to_owned()),
            Some(current) => {
                if !current.is_empty() {
                    current.push('\n');
                }
                current.push_str(line);
            }
        }
    }
    content.unwrap_or_default()
}

/// Whether a terminator-free line matches upstream's option-directive grammar
/// `^//\s*@\w+\s*:` — exactly two leading slashes, a single ASCII-word option
/// name, then a colon. This is the exact set upstream strips from unit content;
/// `///` reference directives and `@word` lines without a colon are kept.
/// Shares its grammar with pragma parsing and unit splitting through
/// [`directive_parts`], so the three paths cannot diverge.
pub(super) fn is_option_directive_line(line: &str) -> bool {
    directive_parts(line).is_some()
}

/// The preamble text is directive-stripped already, so only comments,
/// blanks, strings, and compiled lines remain; block comments may span
/// lines, and a quote hides comment openers.
fn preamble_has_compiled_content(text: &str) -> bool {
    let stripped = strip_directive_lines(text);
    let bytes = stripped.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'/' if bytes.get(index + 1) == Some(&b'/') => {
                index += 2;
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            }
            b'/' if bytes.get(index + 1) == Some(&b'*') => {
                index += 2;
                while index + 1 < bytes.len() && !(bytes[index] == b'*' && bytes[index + 1] == b'/')
                {
                    index += 1;
                }
                index = (index + 2).min(bytes.len());
            }
            b'"' | b'\'' | b'`' => {
                let quote = bytes[index];
                index += 1;
                while index < bytes.len() && bytes[index] != quote {
                    index += usize::from(bytes[index] == b'\\') + 1;
                }
                index += 1;
            }
            byte if byte.is_ascii_whitespace() => index += 1,
            _ => return true,
        }
    }
    false
}

/// Split a case blob at `// @filename:` boundaries.
///
/// A directive must be a whole-line comment. Text before the first directive
/// belongs to the unit named by `logical_path`'s basename; a directive naming
/// the case's own basename is also treated as that first unit (no second
/// empty unit). Unit virtual paths are joined under the case's virtual
/// directory; absolute directive names are remapped to the root.
pub fn split_case_units(logical_path: &str, text: &str) -> Vec<CaseUnit> {
    let case_name = logical_path.rsplit('/').next().unwrap_or(logical_path);
    let case_dir = logical_path
        .rsplit_once('/')
        .map(|(dir, _)| dir)
        .unwrap_or("");

    // Gather directive markers as (line start byte offset, unit name).
    let mut markers: Vec<(usize, String)> = Vec::new();
    let mut offset = 0usize;
    for line in text.split_inclusive('\n') {
        let line_start = offset;
        offset += line.len();
        let name =
            directive_parts(line.trim_end_matches(['\n', '\r'])).and_then(|(name, value)| {
                name.eq_ignore_ascii_case("filename")
                    .then(|| value.trim().to_owned())
            });
        if let Some(name) = name.filter(|name| !name.is_empty()) {
            markers.push((line_start, name));
        }
    }

    let mut units: Vec<CaseUnit> = Vec::new();
    let push_unit = |name: String, text: &str, units: &mut Vec<CaseUnit>| {
        let virtual_path = virtual_unit_path(case_dir, &name);
        // Upstream `makeUnitsFromTest` strips every `// @name: value` directive
        // line (global options and `@filename:` markers alike) from a unit's
        // compiled content, so a case's `.errors.txt`, `.types`, and
        // `.symbols` positions are numbered over directive-free source. Strip
        // the same lines here so emitted positions align with the baselines.
        let content = strip_directive_lines(text);
        // Upstream feeds units into a path-keyed fake FS (`testfs[fileName] =
        // file.Content`), so a directive restating an earlier unit's name
        // makes the later chunk the unit's entire content — it replaces, not
        // appends. Unit order stays at the first-seen position.
        if let Some(existing) = units.iter_mut().find(|u| u.virtual_path == virtual_path) {
            existing.text = content;
        } else {
            units.push(CaseUnit {
                // Slash-normalized verbatim spelling: no `.types` baseline
                // section header ever contains a backslash, but drive-letter
                // (`A:/…`) and dot-slash (`./…`) prefixes are preserved.
                display_name: name.replace('\\', "/"),
                virtual_path,
                text: content,
            });
        }
    };

    if markers.is_empty() {
        push_unit(case_name.to_owned(), text, &mut units);
        return units;
    }

    // Drop a marker that names the case's own basename at position 0: it
    // identifies the entry unit, it does not start a second one.
    let first_names_case = markers
        .first()
        .is_some_and(|(_, name)| name.rsplit('/').next() == Some(case_name));

    let mut body_start = 0usize;
    let mut body_name: Option<String> = None;
    for (index, (marker_start, name)) in markers.iter().enumerate() {
        if index == 0 && first_names_case {
            // The leading marker names the case's own basename: preamble and
            // the marker line both belong to the entry unit.
            body_start = 0;
            body_name = Some(case_name.to_owned());
            continue;
        }
        let end = *marker_start;
        match &body_name {
            Some(name) => push_unit(name.clone(), &text[body_start..end], &mut units),
            None => {
                // Upstream `ParseTestFilesAndSymlinks` (with
                // `AllowImplicitFirstFile: false`) panics on real code before
                // the first `@Filename` and drops comment-only preamble: the
                // implicit case-named unit exists only when it carries
                // compiled content. An options/comment-only preamble is
                // global settings, not a unit, so creating one here echoes a
                // phantom `//// [<case>.ts]` section and emits a phantom
                // `//// [<case>.js]`/`.d.ts` output that shifts every
                // baseline section the emit facets compare.
                if end > 0 && preamble_has_compiled_content(&text[..end]) {
                    push_unit(case_name.to_owned(), &text[..end], &mut units);
                }
            }
        }
        body_start = *marker_start;
        body_name = Some(name.clone());
    }
    if let Some(name) = body_name {
        push_unit(name, &text[body_start..], &mut units);
    }
    if units.is_empty() {
        push_unit(case_name.to_owned(), text, &mut units);
    }
    units
}

/// Map a `@filename:` name onto a root-relative virtual path: relative names
/// join under the case's directory; absolute virtual names (`/ref.d.ts`) and
/// Windows-style drive-letter paths (`c:/root/...`) are remapped to the root
/// so `ProgramLoader` can confine them. The drive letter is a virtual root
/// marker in upstream test cases, not a real directory component; stripping it
/// prevents paths like `/tmp/x/c:/root/...` on Unix hosts.
pub(super) fn virtual_unit_path(case_dir: &str, name: &str) -> String {
    let name = name.replace('\\', "/");
    // Strip a Windows-style drive-letter prefix (`c:/…`, `D:\…` after
    // backslash→slash normalization). The remainder is a root-relative
    // virtual path (like `/`-prefixed absolute names), NOT joined under the
    // case directory — the drive letter marks an absolute virtual root.
    if name.len() >= 3 && name.as_bytes()[1] == b':' && name.as_bytes()[2] == b'/' {
        return name[3..].to_owned();
    }
    if let Some(rest) = name.strip_prefix('/') {
        return rest.to_owned();
    }
    if case_dir.is_empty() {
        name
    } else {
        format!("{case_dir}/{name}")
    }
}
/// Whether a virtual unit path names a TypeScript declaration file.
pub(super) fn is_check_cell_declaration_path(path: &str) -> bool {
    let lower = path.to_lowercase();
    lower.ends_with(".d.ts") || lower.ends_with(".d.mts") || lower.ends_with(".d.cts")
}
/// Virtual prefix test sources use for shared library files.
const SHARED_LIB_PREFIX: &str = "/.lib/";
/// Snapshot subtree holding the shared library files.
const SHARED_LIB_ROOT: &str = "tests/lib/";

/// Whether a `/.lib/` reference target names a loadable support file.
fn shared_lib_target(value: &str) -> Option<&str> {
    let rest = value.strip_prefix(SHARED_LIB_PREFIX)?;
    if rest.is_empty()
        || rest.starts_with('/')
        || rest.contains('\\')
        || rest
            .split('/')
            .any(|part| part.is_empty() || part == "." || part == "..")
    {
        return None;
    }
    rest.to_ascii_lowercase().ends_with(".d.ts").then_some(rest)
}

/// Every `/.lib/` reference target one unit text names, in sorted order.
///
/// Only the prologue counts, mirroring the compiler's own loader
/// (`collect_reference_directives` scans tokens up to the first statement
/// and honors only `LineComment` tokens, rejecting a fourth slash): a
/// `////` line is inert, `Unknown` tokens stay trivia as in the parser,
/// and a directive after the first compiled line is
/// inert, and block-comment bodies never name a target. The scan is a
/// small state machine over the prologue: a `#!` shebang counts only as
/// the first line, block comments may span lines, closing `*/` resumes
/// scanning the same line, and the first other content ends the prologue.
pub(super) fn shared_lib_refs(text: &str) -> Vec<String> {
    let mut refs = Vec::new();
    let Ok(source) = SourceText::new(text) else {
        return refs;
    };
    let scanned = scanner::scan(SourceId::new(0), ScriptKind::TypeScript, Arc::new(source));
    let scanned = scanned.into_product();
    for token in scanned.tokens() {
        match token.kind() {
            TokenKind::Whitespace
            | TokenKind::Shebang
            | TokenKind::BlockComment
            | TokenKind::Unknown => {}
            TokenKind::LineComment => {
                let Some(comment) = scanned.token_text(token) else {
                    continue;
                };
                let comment_bytes = comment.as_bytes();
                if comment_bytes.get(2) == Some(&b'/') && comment_bytes.get(3) != Some(&b'/') {
                    push_directive_refs(comment, &mut refs);
                }
            }
            _ => break,
        }
    }
    refs.sort();
    refs
}

/// Every `/.lib/` target a `/// <reference ... />` comment names.
fn push_directive_refs(comment: &str, refs: &mut Vec<String>) {
    for (name, value) in directive_attributes(comment) {
        if name != "path" {
            continue;
        }
        let Some(target) = shared_lib_target(value) else {
            continue;
        };
        if !refs.iter().any(|existing| existing == target) {
            refs.push(target.to_owned());
        }
    }
}

/// Every `(name, value)` attribute of a `/// <reference ... />` directive.
fn directive_attributes(line: &str) -> Vec<(&str, &str)> {
    let mut pairs = Vec::new();
    let Some(tag) = line.find("<reference") else {
        return pairs;
    };
    let mut rest = &line[tag + "<reference".len()..];
    while let Some(eq) = rest.find('=') {
        let name = rest[..eq].trim().trim_start_matches('/');
        rest = &rest[eq + 1..];
        let Some(value) = quoted_value(&mut rest) else {
            break;
        };
        pairs.push((name, value));
    }
    pairs
}

/// The next quoted attribute value, advancing past it.
fn quoted_value<'a>(rest: &mut &'a str) -> Option<&'a str> {
    let source = *rest;
    let quote = source.trim_start().chars().next().unwrap_or('\0');
    if quote != '"' && quote != '\'' {
        return None;
    }
    let after_quote = &source.trim_start()[1..];
    let end = after_quote.find(quote)?;
    let value = &after_quote[..end];
    *rest = &after_quote[end + 1..];
    Some(value)
}
/// Rewrite `/.lib/<path>` reference targets to the bare subpath the
/// baselines print, returning every referenced subpath in sorted order.
pub(super) fn rewrite_shared_lib_refs(units: &mut [CaseUnit]) -> Vec<String> {
    let mut all = Vec::new();
    for unit in units.iter_mut() {
        for target in shared_lib_refs(&unit.text) {
            unit.text = unit.text.replace(
                &format!("\"{SHARED_LIB_PREFIX}{target}\""),
                &format!("\"{target}\""),
            );
            unit.text = unit.text.replace(
                &format!("'{SHARED_LIB_PREFIX}{target}'"),
                &format!("'{target}'"),
            );
            if !all.iter().any(|existing| existing == &target) {
                all.push(target);
            }
        }
    }
    all.sort();
    all
}

/// Load the referenced shared-library files from the snapshot and place
/// one copy beside each importing unit, rewriting `/.lib/` targets to the
/// bare subpath the baselines print. Support files are written to the temp
/// project for the loader only; they are never paired with case units, so
/// no facet echoes them or reports their diagnostics.
pub(crate) fn shared_lib_support_files(
    snapshot: &(impl SnapshotAssets + ?Sized),
    units: &mut [CaseUnit],
) -> Result<Vec<CaseUnit>> {
    let mut support = Vec::new();
    let mut seen = HashSet::new();
    let targets = rewrite_shared_lib_refs(units);
    for target in &targets {
        let bytes = read_verified_snapshot_asset(snapshot, &format!("{SHARED_LIB_ROOT}{target}"))?;
        let text = String::from_utf8_lossy(&bytes).into_owned();
        place_support_file(&mut support, &mut seen, units, target, &text);
    }
    Ok(support)
}

/// One copy of a shared-library file beside each importing unit.
fn place_support_file(
    support: &mut Vec<CaseUnit>,
    seen: &mut HashSet<String>,
    units: &[CaseUnit],
    target: &str,
    text: &str,
) {
    for unit in units {
        let dir = unit
            .virtual_path
            .rsplit_once('/')
            .map(|(dir, _)| dir)
            .unwrap_or("");
        let virtual_path = if dir.is_empty() {
            target.to_owned()
        } else {
            format!("{dir}/{target}")
        };
        if !seen.insert(virtual_path.clone()) {
            continue;
        }
        support.push(CaseUnit {
            virtual_path,
            display_name: target.to_owned(),
            text: text.to_owned(),
        });
    }
}

/// The virtual path of the unit that acts as the compile entry: the first
/// split unit (single-unit cases and cases whose first `@filename` names the
/// case all lead with the entry unit).
pub fn entry_virtual_path(logical_path: &str, units: &[CaseUnit]) -> String {
    let _ = logical_path;
    units
        .first()
        .map(|unit| unit.virtual_path.clone())
        .unwrap_or_else(|| {
            logical_path
                .rsplit('/')
                .next()
                .unwrap_or(logical_path)
                .to_owned()
        })
}

/// Basename of a virtual path (`foo/b.ts` ⇒ `b.ts`), matching the unit name a
/// baseline prints so both sides of the diagnostics comparator agree.
pub(super) fn unit_basename(virtual_path: &str) -> String {
    virtual_path
        .rsplit('/')
        .next()
        .unwrap_or(virtual_path)
        .to_owned()
}

/// Whether a unit name is a project-config file (`tsconfig.json` /
/// `jsconfig.json`). Upstream parses those as configuration, never as
/// program sources, so no `.types` baseline has a section for either;
/// data `.json` inputs (`b.json`, `package.json`) do get sections with
/// records.
pub(super) fn is_config_unit_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    matches!(
        lower.rsplit('/').next(),
        Some("tsconfig.json") | Some("jsconfig.json")
    )
}

/// Whether a unit name is a JavaScript source file, which tsc compiles only
/// under `allowJs`.
pub(super) fn is_script_input_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    [".js", ".jsx", ".mjs", ".cjs"]
        .iter()
        .any(|extension| lower.ends_with(extension))
}

/// Whether a unit name is itself a declaration file: `.d.ts`, `.d.mts`,
/// `.d.cts`, or a `.ts` file whose name contains `.d.` (`styles.d.css.ts`,
/// an arbitrary-extension declaration). Upstream's output mapping skips
/// declaration inputs entirely: they produce no JavaScript and no
/// declaration output.
pub(super) fn is_declaration_input_name(name: &str) -> bool {
    is_declaration_section_name(name)
        || (name.to_ascii_lowercase().ends_with(".ts") && name.contains(".d."))
}

/// Whether a unit name is a JSON file (`.json`). Upstream's declaration emit
/// never produces a `.d.ts` for JSON inputs: `resolveJsonModule` lets a JSON
/// file be imported as a typed value, but the output mapping skips it for
/// declaration purposes.
pub(super) fn is_json_input_name(name: &str) -> bool {
    name.to_ascii_lowercase().ends_with(".json")
}

/// The `//// [name]` header text of an upstream baseline section, or `None`
/// for any other line. The document header (`//// [case] ////`) carries
/// trailing slashes and is never a section header.
pub(super) fn section_header_name(line: &str) -> Option<&str> {
    line.strip_prefix("//// [")
        .and_then(|rest| rest.strip_suffix(']'))
}

/// Whether a baseline section name is a declaration output (`a.d.ts`,
/// `a.d.mts`, `a.d.cts`).
pub(super) fn is_declaration_section_name(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower.ends_with(".d.ts") || lower.ends_with(".d.mts") || lower.ends_with(".d.cts")
}

/// Whether a baseline section name is a `.tsbuildinfo` output.
pub(super) fn is_tsbuildinfo_section_name(name: &str) -> bool {
    name.ends_with(".tsbuildinfo")
}
