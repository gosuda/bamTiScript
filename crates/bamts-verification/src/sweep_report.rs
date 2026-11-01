//! Read-only reports over evidence receipts.
//!
//! A sweep leaves one receipt per catalog and runner. These reports answer what
//! a repair loop asks of it: how many rows sit in each state, which failures
//! share a cause, and what changed between two receipts. Nothing here writes a
//! receipt or decides a state.

use std::{
    collections::BTreeMap,
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};

use crate::{
    ErrorCode, Result, VerificationError,
    evidence::{EvidenceReader, EvidenceRow, TerminalState},
    shard::ObligationKey,
};

/// Characters of a quoted span that still count toward a family. The rest of a
/// long span is usually a path or an identifier that differs per case.
const QUOTED_KEEP: usize = 48;
/// Longest family handle, so it stays usable as one command-line argument.
const SLUG_MAX: usize = 96;

/// One receipt row reduced to what the reports compare.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReportRow {
    key: ObligationKey,
    facet: String,
    state: TerminalState,
    detail: String,
}

impl ReportRow {
    #[must_use]
    pub fn new(
        key: ObligationKey,
        facet: impl Into<String>,
        state: TerminalState,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            key,
            facet: facet.into(),
            state,
            detail: detail.into(),
        }
    }

    /// The facet is the set of observables the obligation checks, joined by `+`.
    #[must_use]
    pub fn from_evidence(row: &EvidenceRow) -> Self {
        let facet = row
            .observables()
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join("+");
        Self::new(row.key().clone(), facet, row.state(), row.detail())
    }

    #[must_use]
    pub fn key(&self) -> &ObligationKey {
        &self.key
    }

    #[must_use]
    pub fn facet(&self) -> &str {
        &self.facet
    }

    #[must_use]
    pub fn state(&self) -> TerminalState {
        self.state
    }

    /// The failure family of a row that blocks completion, or `None` for a row
    /// that passes or is excluded by policy.
    ///
    /// A family is `<facet>/<slug>`, where the slug is the diagnostic text with
    /// the parts that differ per case removed. Rows in one family failed the
    /// same way. The handle is only as precise as the text a worker records:
    /// when the text is coarse, the family is too.
    #[must_use]
    pub fn family(&self) -> Option<String> {
        blocks_completion(self.state).then(|| family_name(&self.facet, &self.detail))
    }
}

/// States a scoped root does not accept. A policy exclusion is not one of them.
const fn blocks_completion(state: TerminalState) -> bool {
    !matches!(
        state,
        TerminalState::Pass
            | TerminalState::InapplicableLanguageService
            | TerminalState::InapplicableOutOfScopeHostFeature
            | TerminalState::InapplicableV8Internal
    )
}

/// The handle for rows of one facet that fail with this diagnostic text.
#[must_use]
pub fn family_name(facet: &str, detail: &str) -> String {
    let slug = slugify(&normalize_detail(detail));
    let slug = if slug.is_empty() { "no-detail" } else { &slug };
    format!("{facet}/{slug}")
}

/// Drops what differs per case: the mode wrapper test262 workers add, backtick
/// spans, the tail of long quoted spans, absolute paths, and the value of every
/// number.
fn normalize_detail(detail: &str) -> String {
    let detail = strip_mode_wrapper(detail);
    let mut out = String::with_capacity(detail.len());
    let mut chars = detail.chars().peekable();
    while let Some(character) = chars.next() {
        match character {
            '`' => {
                for inner in chars.by_ref() {
                    if inner == '`' {
                        break;
                    }
                }
            }
            '"' => {
                out.push('"');
                let mut kept = 0;
                while let Some(inner) = chars.next() {
                    if inner == '\\' {
                        chars.next();
                    } else if inner == '"' {
                        break;
                    } else if kept < QUOTED_KEEP {
                        out.push(inner);
                        kept += 1;
                    }
                }
                out.push('"');
            }
            digit if digit.is_ascii_digit() => {
                while chars.next_if(char::is_ascii_digit).is_some() {}
                out.push('N');
            }
            other => out.push(other),
        }
    }
    out.split_whitespace()
        .filter(|word| !is_absolute_path(word))
        .collect::<Vec<_>>()
        .join(" ")
}

/// A scratch directory or checkout path names the run, not the failure.
fn is_absolute_path(word: &str) -> bool {
    let bytes = word.as_bytes();
    word.starts_with('/')
        || (bytes.len() > 2
            && bytes[0].is_ascii_alphabetic()
            && bytes[1] == b':'
            && matches!(bytes[2], b'\\' | b'/'))
}

/// test262 workers prefix their text with `test262 <mode> mode failure: `. The
/// mode would split one failure into three, so it is not part of the family.
fn strip_mode_wrapper(detail: &str) -> &str {
    const MARKER: &str = " mode failure: ";
    detail
        .strip_prefix("test262 ")
        .and_then(|rest| {
            let end = rest.find(MARKER)?;
            (end <= QUOTED_KEEP).then(|| &rest[end + MARKER.len()..])
        })
        .unwrap_or(detail)
}

fn slugify(text: &str) -> String {
    let mut slug = String::new();
    for character in text.chars() {
        if character.is_ascii_alphanumeric() {
            slug.push(character.to_ascii_lowercase());
        } else if !slug.ends_with('-') && !slug.is_empty() {
            slug.push('-');
        }
    }
    slug.truncate(SLUG_MAX);
    slug.trim_end_matches('-').to_owned()
}

/// Reads and validates a whole receipt: header, strictly ordered rows, footer.
///
/// The reader returns `None` only once the footer has matched the rows read and
/// nothing follows it, so a truncated or inconsistent receipt is an error here.
pub fn read_receipt(path: &Path) -> Result<Vec<ReportRow>> {
    let mut reader = EvidenceReader::open(path)?;
    let mut rows = Vec::new();
    while let Some(row) = reader.next_row()? {
        rows.push(ReportRow::from_evidence(&row));
    }
    Ok(rows)
}

/// Percentage with one decimal, from integers so the output is exact.
fn percent(part: usize, whole: usize) -> String {
    if whole == 0 {
        return "0.0%".to_owned();
    }
    let tenths = part * 1000 / whole;
    format!("{}.{}%", tenths / 10, tenths % 10)
}

/// Counts of the rows that fail, largest first, ties by name.
fn family_counts(rows: &[ReportRow]) -> Vec<(String, usize)> {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for family in rows.iter().filter_map(ReportRow::family) {
        *counts.entry(family).or_default() += 1;
    }
    let mut ordered: Vec<(String, usize)> = counts.into_iter().collect();
    ordered.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(&right.0)));
    ordered
}

/// Counts by state, by facet, and by failure family.
#[must_use]
pub fn render_status(source: &str, rows: &[ReportRow], top: usize) -> String {
    let mut states: BTreeMap<TerminalState, usize> = BTreeMap::new();
    let mut facets: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    let mut catalogs: BTreeMap<&str, ()> = BTreeMap::new();
    let mut modes: BTreeMap<&str, ()> = BTreeMap::new();
    for row in rows {
        *states.entry(row.state).or_default() += 1;
        let facet = facets.entry(&row.facet).or_default();
        facet.0 += 1;
        facet.1 += usize::from(row.state.is_pass());
        catalogs.insert(row.key.catalog(), ());
        modes.insert(row.key.mode().as_str(), ());
    }
    let join = |names: &BTreeMap<&str, ()>| names.keys().copied().collect::<Vec<_>>().join(",");

    let mut out = String::new();
    let _ = writeln!(out, "receipt: {source}");
    let _ = writeln!(
        out,
        "rows: {}  catalogs: {}  modes: {}",
        rows.len(),
        join(&catalogs),
        join(&modes)
    );
    out.push_str("\nstates:\n");
    for (state, count) in &states {
        let _ = writeln!(
            out,
            "  {:<40} {count:>7}  {:>6}",
            state.as_str(),
            percent(*count, rows.len())
        );
    }
    out.push_str("\nfacets:                                      pass   total\n");
    for (facet, (total, passing)) in &facets {
        let _ = writeln!(out, "  {facet:<40} {passing:>7} {total:>7}");
    }
    let families = family_counts(rows);
    let _ = writeln!(
        out,
        "\nfamilies of rows that block completion ({} total, largest {} shown):",
        families.len(),
        top.min(families.len())
    );
    for (family, count) in families.iter().take(top) {
        let _ = writeln!(out, "  {count:>7}  {family}");
    }
    out
}

/// One row of a family, with the size of its input when the file is found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FamilyCase {
    pub size: Option<u64>,
    pub state: TerminalState,
    pub key: ObligationKey,
}

/// Rows of `family`, smallest input first; rows whose file is not found last.
///
/// A case path starts with the catalog's runner segment. Dropping it leaves the
/// path inside the authority tree at `root`.
#[must_use]
pub fn family_cases(rows: &[ReportRow], family: &str, root: Option<&Path>) -> Vec<FamilyCase> {
    let mut cases: Vec<FamilyCase> = rows
        .iter()
        .filter(|row| row.family().as_deref() == Some(family))
        .map(|row| FamilyCase {
            size: root.and_then(|root| input_size(root, row.key.case())),
            state: row.state,
            key: row.key.clone(),
        })
        .collect();
    cases.sort_by(|left, right| {
        let size = |case: &FamilyCase| (case.size.is_none(), case.size);
        size(left)
            .cmp(&size(right))
            .then_with(|| left.key.cmp(&right.key))
    });
    cases
}

fn input_size(root: &Path, case: &str) -> Option<u64> {
    let (_, inside) = case.split_once('/')?;
    fs::metadata(root.join(inside)).ok().map(|meta| meta.len())
}

#[must_use]
pub fn render_family_cases(family: &str, cases: &[FamilyCase]) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "family: {family}  ({} rows, smallest first)",
        cases.len()
    );
    for case in cases {
        let size = case
            .size
            .map_or_else(|| "?".to_owned(), |bytes| bytes.to_string());
        let _ = writeln!(
            out,
            "  {size:>9}  {:<14}  {}",
            case.state.as_str(),
            case.key
        );
    }
    out
}

/// What changed between two receipts, by obligation identity.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Diff {
    pub common: usize,
    pub unchanged: usize,
    pub only_in_a: Vec<ObligationKey>,
    pub only_in_b: Vec<ObligationKey>,
    pub changed: BTreeMap<(TerminalState, TerminalState), Vec<ObligationKey>>,
}

impl Diff {
    /// Rows that became `PASS`.
    #[must_use]
    pub fn conversions(&self) -> Vec<&ObligationKey> {
        self.moves(|from, to| !from.is_pass() && to.is_pass())
    }

    /// Rows that stopped being `PASS`.
    #[must_use]
    pub fn regressions(&self) -> Vec<&ObligationKey> {
        self.moves(|from, to| from.is_pass() && !to.is_pass())
    }

    fn moves(&self, wanted: impl Fn(TerminalState, TerminalState) -> bool) -> Vec<&ObligationKey> {
        self.changed
            .iter()
            .filter(|((from, to), _)| wanted(*from, *to))
            .flat_map(|(_, keys)| keys)
            .collect()
    }
}

#[must_use]
pub fn diff_rows(a: &[ReportRow], b: &[ReportRow]) -> Diff {
    let after: BTreeMap<&ObligationKey, TerminalState> =
        b.iter().map(|row| (&row.key, row.state)).collect();
    let mut seen = 0usize;
    let mut diff = Diff::default();
    for row in a {
        match after.get(&row.key) {
            None => diff.only_in_a.push(row.key.clone()),
            Some(&state) => {
                seen += 1;
                if state == row.state {
                    diff.unchanged += 1;
                } else {
                    diff.changed
                        .entry((row.state, state))
                        .or_default()
                        .push(row.key.clone());
                }
            }
        }
    }
    diff.common = seen;
    let before: BTreeMap<&ObligationKey, ()> = a.iter().map(|row| (&row.key, ())).collect();
    diff.only_in_b = b
        .iter()
        .filter(|row| !before.contains_key(&row.key))
        .map(|row| row.key.clone())
        .collect();
    diff
}

#[must_use]
pub fn render_diff(a: &str, b: &str, diff: &Diff, limit: usize) -> String {
    let changed: usize = diff.changed.values().map(Vec::len).sum();
    let mut out = String::new();
    let _ = writeln!(out, "diff: {a} -> {b}");
    let _ = writeln!(
        out,
        "rows in both: {}  only in first: {}  only in second: {}",
        diff.common,
        diff.only_in_a.len(),
        diff.only_in_b.len()
    );
    let _ = writeln!(
        out,
        "unchanged: {}  changed: {changed}  conversions to PASS: {}  regressions from PASS: {}",
        diff.unchanged,
        diff.conversions().len(),
        diff.regressions().len()
    );
    for ((from, to), keys) in &diff.changed {
        let _ = writeln!(
            out,
            "\n{} -> {}  ({})",
            from.as_str(),
            to.as_str(),
            keys.len()
        );
        for key in keys.iter().take(limit) {
            let _ = writeln!(out, "  {key}");
        }
        if keys.len() > limit {
            let _ = writeln!(out, "  ... {} more", keys.len() - limit);
        }
    }
    out
}

/// `suite families`: the status report, or the cases of one family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FamiliesRequest {
    pub receipt: PathBuf,
    pub top: usize,
    pub family: Option<String>,
    pub root: Option<PathBuf>,
}

pub fn families(request: &FamiliesRequest) -> Result<String> {
    let rows = read_receipt(&request.receipt)?;
    let source = request.receipt.display().to_string();
    Ok(match &request.family {
        None => render_status(&source, &rows, request.top),
        Some(family) => {
            let cases = family_cases(&rows, family, request.root.as_deref());
            if cases.is_empty() {
                return Err(VerificationError::new(
                    ErrorCode::Usage,
                    format!("{source}: no row belongs to family `{family}`"),
                ));
            }
            render_family_cases(family, &cases)
        }
    })
}

/// `suite diff`: compares two receipts; optionally fails on any regression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiffRequest {
    pub a: PathBuf,
    pub b: PathBuf,
    pub limit: usize,
    pub fail_on_regression: bool,
}

/// The rendered report, and the number of regressions it found.
pub fn diff(request: &DiffRequest) -> Result<(String, usize)> {
    let a = read_receipt(&request.a)?;
    let b = read_receipt(&request.b)?;
    let diff = diff_rows(&a, &b);
    let report = render_diff(
        &request.a.display().to_string(),
        &request.b.display().to_string(),
        &diff,
        request.limit,
    );
    Ok((report, diff.regressions().len()))
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::{
        evidence::{
            EvidenceHeader, ExecutionBinding, PublishMode, RunBinding, ToolchainPin,
            WorkingDirectoryPolicy, publish_evidence,
        },
        shard::{ExecutionMode, ShardIdentity, ShardSpec},
    };

    const DIGEST: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    static NEXT: AtomicU64 = AtomicU64::new(0);

    struct Scratch(PathBuf);

    impl Scratch {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!(
                "bamts-sweep-report-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let _ = fs::remove_dir_all(&root);
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn key(case: &str) -> ObligationKey {
        ObligationKey::new(
            "typescript-7.0.2",
            case,
            "default#diagnostics",
            ExecutionMode::Aot,
            "aarch64-apple-darwin",
        )
        .unwrap()
    }

    fn row(case: &str, state: TerminalState, detail: &str) -> ReportRow {
        ReportRow::new(key(case), "diagnostics", state, detail)
    }

    fn failing(case: &str, detail: &str) -> ReportRow {
        row(case, TerminalState::BlockingFail, detail)
    }

    fn passing(case: &str) -> ReportRow {
        row(case, TerminalState::Pass, "")
    }

    #[test]
    fn rows_that_differ_only_in_numbers_share_a_family() {
        let one = failing("a", "diagnostic count mismatch: expected 2 actual 1");
        let two = failing("b", "diagnostic count mismatch: expected 17 actual 3");
        let other = failing("c", "diagnostic text mismatch");
        assert_eq!(one.family(), two.family());
        assert_ne!(one.family(), other.family());
        assert_eq!(
            one.family().as_deref(),
            Some("diagnostics/diagnostic-count-mismatch-expected-n-actual-n")
        );
    }

    #[test]
    fn a_test262_family_ignores_the_mode_but_not_the_failure_kind() {
        let detail = |mode: &str, actual: &str| {
            format!(
                "test262 {mode} mode failure: ExpectationMismatch {{ expected: \"success\", actual: \"{actual}\" }}"
            )
        };
        let interpreter = failing("a", &detail("interpreter", "Parse/SyntaxError"));
        let jit = failing("b", &detail("jit", "Parse/SyntaxError"));
        let thrown = failing("c", &detail("jit", "Runtime/Test262Error"));
        assert_eq!(interpreter.family(), jit.family());
        assert_ne!(jit.family(), thrown.family());
    }

    #[test]
    fn the_tail_of_a_long_quoted_span_does_not_split_a_family() {
        let prefix = "compile pipeline failed: could not load program: cannot resolve module";
        let first = failing(
            "a",
            &format!("BlockedRun {{ detail: \"{prefix} one/x.js\" }}"),
        );
        let second = failing(
            "b",
            &format!("BlockedRun {{ detail: \"{prefix} two/y.js\" }}"),
        );
        assert_eq!(first.family(), second.family());
        let short = failing("c", "BlockedRun { detail: \"timeout\" }");
        assert_ne!(first.family(), short.family());
    }

    #[test]
    fn an_absolute_path_in_the_text_does_not_split_a_family() {
        let unix = |directory: &str| {
            failing(
                "a",
                &format!("cannot resolve \"react\" from {directory}/tests/cases/file.tsx"),
            )
        };
        assert_eq!(
            unix("/private/var/folders/x1/T/cell-1").family(),
            unix("/tmp/other-2").family()
        );
        assert_eq!(
            unix("/tmp/a").family().as_deref(),
            Some("diagnostics/cannot-resolve-react-from")
        );
        let windows = failing(
            "b",
            "cannot resolve \"react\" from C:\\Users\\run\\file.tsx",
        );
        let drive = failing("c", "cannot resolve \"react\" from D:/work/file.tsx");
        assert_eq!(windows.family(), unix("/tmp/a").family());
        assert_eq!(drive.family(), unix("/tmp/a").family());
        let other_module = failing("d", "cannot resolve \"vue\" from /tmp/a/file.tsx");
        assert_ne!(other_module.family(), unix("/tmp/a").family());
    }

    #[test]
    fn backtick_spans_and_escaped_quotes_are_dropped_from_the_family() {
        let first = failing("a", "locked classification for `x/one` is stale");
        let second = failing("b", "locked classification for `y/two/three` is stale");
        assert_eq!(first.family(), second.family());
        let escaped = failing("c", "got \"a \\\" b\" here");
        assert_eq!(
            escaped.family().as_deref(),
            Some("diagnostics/got-a-b-here")
        );
    }

    #[test]
    fn only_states_that_block_completion_have_a_family() {
        for state in [
            TerminalState::BlockingFail,
            TerminalState::ExternalBlocked,
            TerminalState::InapplicableCatalogError,
            TerminalState::Timeout,
            TerminalState::Signal,
            TerminalState::ProtocolError,
            TerminalState::WorkerCrash,
        ] {
            assert!(row("a", state, "x").family().is_some(), "{state:?}");
        }
        for state in [
            TerminalState::Pass,
            TerminalState::InapplicableLanguageService,
            TerminalState::InapplicableOutOfScopeHostFeature,
            TerminalState::InapplicableV8Internal,
        ] {
            assert!(row("a", state, "x").family().is_none(), "{state:?}");
        }
    }

    #[test]
    fn a_failure_with_no_text_still_has_a_family() {
        assert_eq!(
            failing("a", "").family().as_deref(),
            Some("diagnostics/no-detail")
        );
    }

    #[test]
    fn status_lists_the_largest_family_first_and_honors_the_limit() {
        let mut rows = vec![passing("p")];
        for index in 0..3 {
            rows.push(failing(&format!("big{index}"), "big failure"));
        }
        rows.push(failing("small", "small failure"));
        let report = render_status("r.jsonl", &rows, 1);
        assert!(report.contains("rows: 5"), "{report}");
        assert!(report.contains("PASS"), "{report}");
        assert!(report.contains("BLOCKING_FAIL"), "{report}");
        assert!(report.contains("20.0%"), "{report}");
        assert!(report.contains("diagnostics/big-failure"), "{report}");
        assert!(!report.contains("diagnostics/small-failure"), "{report}");
        let all = render_status("r.jsonl", &rows, 10);
        let big = all.find("big-failure").unwrap();
        let small = all.find("small-failure").unwrap();
        assert!(big < small, "{all}");
    }

    #[test]
    fn a_receipt_diffed_against_itself_has_no_transitions() {
        let rows = vec![passing("a"), failing("b", "x"), failing("c", "y")];
        let diff = diff_rows(&rows, &rows);
        assert_eq!(diff.common, 3);
        assert_eq!(diff.unchanged, 3);
        assert!(diff.changed.is_empty());
        assert!(diff.only_in_a.is_empty() && diff.only_in_b.is_empty());
        assert!(diff.conversions().is_empty() && diff.regressions().is_empty());
    }

    #[test]
    fn a_diff_names_conversions_regressions_and_unmatched_rows() {
        let before = vec![
            failing("fixed", "x"),
            passing("broken"),
            failing("still", "x"),
            failing("gone", "x"),
        ];
        let after = vec![
            passing("fixed"),
            failing("broken", "x"),
            failing("still", "x"),
            failing("new", "x"),
        ];
        let diff = diff_rows(&before, &after);
        assert_eq!(diff.common, 3);
        assert_eq!(diff.unchanged, 1);
        assert_eq!(diff.conversions(), vec![&key("fixed")]);
        assert_eq!(diff.regressions(), vec![&key("broken")]);
        assert_eq!(diff.only_in_a, vec![key("gone")]);
        assert_eq!(diff.only_in_b, vec![key("new")]);
        let report = render_diff("a", "b", &diff, 10);
        assert!(report.contains("conversions to PASS: 1"), "{report}");
        assert!(report.contains("regressions from PASS: 1"), "{report}");
        assert!(report.contains("BLOCKING_FAIL -> PASS"), "{report}");
    }

    #[test]
    fn a_transition_between_two_failing_states_is_not_a_regression() {
        let before = vec![failing("a", "x")];
        let after = vec![row("a", TerminalState::Timeout, "x")];
        let diff = diff_rows(&before, &after);
        assert_eq!(diff.changed.len(), 1);
        assert!(diff.regressions().is_empty() && diff.conversions().is_empty());
    }

    #[test]
    fn the_report_limit_truncates_each_transition_list() {
        let before: Vec<ReportRow> = (0..5)
            .map(|index| failing(&format!("c{index}"), "x"))
            .collect();
        let after: Vec<ReportRow> = (0..5).map(|index| passing(&format!("c{index}"))).collect();
        let report = render_diff("a", "b", &diff_rows(&before, &after), 2);
        assert!(report.contains("... 3 more"), "{report}");
    }

    #[test]
    fn family_cases_come_smallest_first_with_unknown_sizes_last() {
        let scratch = Scratch::new();
        fs::create_dir_all(scratch.0.join("tests")).unwrap();
        fs::write(scratch.0.join("tests/big.ts"), "x".repeat(900)).unwrap();
        fs::write(scratch.0.join("tests/small.ts"), "x".repeat(10)).unwrap();
        let rows = vec![
            failing("compiler/tests/big.ts", "same"),
            failing("compiler/tests/missing.ts", "same"),
            failing("compiler/tests/small.ts", "same"),
            failing("compiler/tests/other.ts", "different"),
        ];
        let family = rows[0].family().unwrap();
        let cases = family_cases(&rows, &family, Some(&scratch.0));
        let order: Vec<&str> = cases.iter().map(|case| case.key.case()).collect();
        assert_eq!(
            order,
            [
                "compiler/tests/small.ts",
                "compiler/tests/big.ts",
                "compiler/tests/missing.ts"
            ]
        );
        assert_eq!(cases[0].size, Some(10));
        assert_eq!(cases[2].size, None);
        assert!(family_cases(&rows, "diagnostics/none", Some(&scratch.0)).is_empty());
    }

    fn evidence_row(case: &str, state: TerminalState, detail: &str) -> EvidenceRow {
        let mut artifacts = BTreeMap::new();
        if state.is_pass() {
            artifacts.insert("diagnostics".to_owned(), DIGEST.to_owned());
        }
        EvidenceRow::new(
            key(case),
            vec!["run".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            BTreeSet::from(["diagnostics".to_owned()]),
            artifacts,
            state,
            1,
            detail,
        )
        .unwrap()
    }

    fn write_receipt(path: &Path, rows: &[(&str, TerminalState, &str)]) {
        let mut sorted: Vec<_> = rows.to_vec();
        sorted.sort_by_key(|(case, ..)| key(case));
        let catalog: Vec<ObligationKey> = sorted.iter().map(|(case, ..)| key(case)).collect();
        let shard = ShardIdentity::plan(ShardSpec::unsharded(), &catalog).unwrap();
        let pin = ToolchainPin::new("rustc-1.97.1", DIGEST).unwrap();
        let binding = RunBinding::new(DIGEST, DIGEST, DIGEST, DIGEST, pin).unwrap();
        let header =
            EvidenceHeader::new(shard, binding, ExecutionBinding::local_for_tests()).unwrap();
        let evidence: Vec<EvidenceRow> = sorted
            .iter()
            .map(|(case, state, detail)| evidence_row(case, *state, detail))
            .collect();
        publish_evidence(path, header, &evidence, PublishMode::Replace).unwrap();
    }

    #[test]
    fn a_real_receipt_reads_back_with_its_facet_state_and_family() {
        let scratch = Scratch::new();
        let path = scratch.0.join("r.jsonl");
        write_receipt(
            &path,
            &[
                ("a", TerminalState::Pass, ""),
                (
                    "b",
                    TerminalState::BlockingFail,
                    "types mismatch at line 12",
                ),
            ],
        );
        let rows = read_receipt(&path).unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].facet(), "diagnostics");
        assert!(rows[0].state().is_pass() && rows[0].family().is_none());
        assert_eq!(
            rows[1].family().as_deref(),
            Some("diagnostics/types-mismatch-at-line-n")
        );
    }

    #[test]
    fn a_truncated_receipt_is_rejected_not_reported_short() {
        let scratch = Scratch::new();
        let path = scratch.0.join("r.jsonl");
        write_receipt(
            &path,
            &[
                ("a", TerminalState::Pass, ""),
                ("b", TerminalState::Pass, ""),
            ],
        );
        let text = fs::read_to_string(&path).unwrap();
        let without_footer: Vec<&str> = text.lines().collect::<Vec<_>>();
        let cut = without_footer[..without_footer.len() - 1].join("\n");
        fs::write(&path, cut).unwrap();
        assert!(read_receipt(&path).is_err());
    }

    #[test]
    fn a_receipt_whose_footer_disagrees_with_its_rows_is_rejected() {
        let scratch = Scratch::new();
        let path = scratch.0.join("r.jsonl");
        write_receipt(
            &path,
            &[
                ("a", TerminalState::Pass, ""),
                ("b", TerminalState::Pass, ""),
            ],
        );
        let text = fs::read_to_string(&path).unwrap();
        assert_eq!(text.matches("\"row_count\":2").count(), 1, "{text}");
        fs::write(&path, text.replace("\"row_count\":2", "\"row_count\":9")).unwrap();
        assert!(read_receipt(&path).is_err());
    }

    #[test]
    fn the_request_functions_report_through_real_receipts() {
        let scratch = Scratch::new();
        let (first, second) = (scratch.0.join("a.jsonl"), scratch.0.join("b.jsonl"));
        write_receipt(
            &first,
            &[
                ("a", TerminalState::Pass, ""),
                ("b", TerminalState::BlockingFail, "x"),
            ],
        );
        write_receipt(
            &second,
            &[
                ("a", TerminalState::BlockingFail, "x"),
                ("b", TerminalState::BlockingFail, "x"),
            ],
        );

        let (report, regressions) = diff(&DiffRequest {
            a: first.clone(),
            b: second.clone(),
            limit: 5,
            fail_on_regression: false,
        })
        .unwrap();
        assert_eq!(regressions, 1, "{report}");

        let (_, none) = diff(&DiffRequest {
            a: first.clone(),
            b: first.clone(),
            limit: 5,
            fail_on_regression: true,
        })
        .unwrap();
        assert_eq!(none, 0);

        let status = families(&FamiliesRequest {
            receipt: second.clone(),
            top: 5,
            family: None,
            root: None,
        })
        .unwrap();
        assert!(status.contains("diagnostics/x"), "{status}");

        let missing = families(&FamiliesRequest {
            receipt: second,
            top: 5,
            family: Some("diagnostics/not-there".to_owned()),
            root: None,
        });
        assert!(missing.is_err());
    }
}
