//! Repository architecture ratchet for continuing holonic machinery.
//!
//! This is an observer and build tool, so it may use cpu collections internally.  Its output is
//! never machine standing.  Production modules are checked against a committed per-file census:
//! an inherited dependency may disappear, but no file may add another occurrence and a new file
//! begins with zero allowance.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// Where the committed census lives, relative to the repository root handed to
/// [`check_repository`]. It sits in `meta/` beside the other tracked ledgers —
/// `AUTHORED_LEVELS.tsv`, `BOUNDARY_ARTIFACTS.tsv`, `OUTPUT_MANIFEST.tsv`,
/// `CLOSURE_MANIFEST.tsv` — because it is the same species of object: a tracked address for
/// something the tree would otherwise be unable to say it had lost.
///
/// It read `HOLONIC_DSA_BASELINE.tsv` at the repository root until 2026-08-10, and no such file
/// has ever existed in this tree; the only copy is `reference/engine-a07ff376/`, which is archive
/// material for a body with a different layout.
pub const BASELINE_PATH: &str = "meta/HOLONIC_DSA_BASELINE.tsv";

/// The aperture: five roots inherited from the laboratory, plus `crates/holonic-structure/src`
/// added 2026-08-15.
///
/// The inherited five are the engine, the reflective runtime, and soma's body, membrane and life.
/// The laboratory kept soma under `src/soma/`; this repository keeps it at `soma/`, and three of
/// those five entries still carried the laboratory prefix. That is `CLAUDE.md` §0 lesson 2 — *no
/// absolute frame in a lineage* — and it was invisible because the missing baseline aborted
/// [`check_repository`] one statement earlier.
///
/// **`crates/holonic-structure/src` is the sixth, and the earlier refusal to add it was wrong on
/// its own terms.** This comment read *"adding them would author a scope the source never
/// declared"*, which is the correct rule applied to the wrong crate: `holonic-structure` is the
/// substrate-container owner, the crate whose declared purpose is holding the ordinal and relation
/// atlases *so that a `BTreeMap` does not become ontology*. A ratchet on ownership constructs that
/// does not watch the ownership crate is watching every consumer of the substrate and not the
/// substrate. The scope was declared by the crate, not authored here. It went unwatched long
/// enough for four modules — `chain.rs`, `face.rs`, `junction.rs`, `relating.rs` — to land there
/// on 2026-08-15 outside the ratchet's view, and `meta/HOLONIC_DSA_BASELINE.tsv` carried zero rows
/// for the crate.
///
/// Still outside, and still for the original reason: `soma/{abi,surface,mount}` and
/// `crates/relational-geometry/src`.
const PROTECTED_ROOTS: &[&str] = &[
    "crates/holonic-engine/src",
    "crates/holonic-language/src",
    "crates/holonic-structure/src",
    "soma/body/src",
    "soma/membrane/src",
    "soma/life/src",
];

// These files are explicitly classified as historical evidence or reference-only test material
// in the ownership ledger. They must be migrated or retired deliberately, but they are not a
// lawful source for new production code and therefore do not define the production ratchet.
//
// `soma/life/src/staging/` has no owner in this tree — `find soma -type d -name staging` returns
// nothing — so it excludes nothing today. It is retained rather than dropped because the
// exclusion is a statement about a *class* of file, and deleting it would silently admit that
// class the day it returns.
const EXCLUDED_PREFIXES: &[&str] = &["soma/life/src/staging/", "soma/body/src/manifold_tests.rs"];

const OWNERSHIP_IDENTIFIERS: &[&str] = &[
    "BTreeMap",
    "BTreeSet",
    "HashMap",
    "HashSet",
    "Vec",
    "VecDeque",
    "BinaryHeap",
    "LinkedList",
];

const MATERIALIZING_METHODS: &[&str] = &["clone", "collect", "flat_map", "into_iter"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchitectureViolation {
    pub path: String,
    pub construct: String,
    pub allowed: usize,
    pub observed: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ArchitectureReport {
    pub protected_files: usize,
    pub inherited_occurrences: usize,
    pub observed_occurrences: usize,
    pub retired_occurrences: usize,
    pub violations: Vec<ArchitectureViolation>,
}

impl ArchitectureReport {
    pub fn is_clean(&self) -> bool {
        self.violations.is_empty()
    }
}

pub fn check_repository(root: &Path) -> Result<ArchitectureReport, String> {
    let baseline = read_baseline(&root.join(BASELINE_PATH))?;
    let observed = census_repository(root)?;
    // `observed` is keyed by (path, construct), so its length is a count of PAIRS. Reporting it
    // as `protected_files` overstated the file count by roughly five to one — 971 against 193 on
    // this tree — in the one line the gate prints. Count the distinct paths.
    let mut report = ArchitectureReport {
        protected_files: observed
            .keys()
            .map(|(path, _)| path.as_str())
            .collect::<BTreeSet<_>>()
            .len(),
        ..ArchitectureReport::default()
    };
    let mut addresses = BTreeSet::new();
    addresses.extend(baseline.keys().cloned());
    addresses.extend(observed.keys().cloned());
    for (path, construct) in addresses {
        let allowed = baseline
            .get(&(path.clone(), construct.clone()))
            .copied()
            .unwrap_or(0);
        let present = observed
            .get(&(path.clone(), construct.clone()))
            .copied()
            .unwrap_or(0);
        report.inherited_occurrences += allowed;
        report.observed_occurrences += present;
        report.retired_occurrences += allowed.saturating_sub(present);
        if present > allowed {
            report.violations.push(ArchitectureViolation {
                path,
                construct,
                allowed,
                observed: present,
            });
        }
    }
    Ok(report)
}

pub fn emit_baseline(root: &Path) -> Result<String, String> {
    let census = census_repository(root)?;
    let mut rendered = String::from(
        "# Holonic production architecture debt.\n\
         # path<TAB>construct=maximum<TAB>construct=maximum...\n\
         # Counts may decrease. Increasing a count requires an explicit ownership-ledger change.\n",
    );
    let mut by_file = BTreeMap::<String, Vec<(String, usize)>>::new();
    for ((path, construct), count) in census {
        if count > 0 {
            by_file.entry(path).or_default().push((construct, count));
        }
    }
    for (path, constructs) in by_file {
        rendered.push_str(&path);
        for (construct, count) in constructs {
            rendered.push('\t');
            rendered.push_str(&construct);
            rendered.push('=');
            rendered.push_str(&count.to_string());
        }
        rendered.push('\n');
    }
    Ok(rendered)
}

fn read_baseline(path: &Path) -> Result<BTreeMap<(String, String), usize>, String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    let mut baseline = BTreeMap::new();
    for (line_at, line) in source.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut fields = line.split('\t');
        let path = fields
            .next()
            .filter(|field| !field.is_empty())
            .ok_or_else(|| format!("baseline line {} has no path", line_at + 1))?;
        let mut found_construct = false;
        for field in fields {
            let (construct, maximum) = field.split_once('=').ok_or_else(|| {
                format!(
                    "baseline line {} has malformed field {field:?}",
                    line_at + 1
                )
            })?;
            if construct.is_empty() {
                return Err(format!(
                    "baseline line {} has an empty construct",
                    line_at + 1
                ));
            }
            let maximum = maximum.parse::<usize>().map_err(|error| {
                format!("baseline line {} has invalid maximum: {error}", line_at + 1)
            })?;
            if baseline
                .insert((path.to_owned(), construct.to_owned()), maximum)
                .is_some()
            {
                return Err(format!(
                    "baseline line {} repeats {path} / {construct}",
                    line_at + 1
                ));
            }
            found_construct = true;
        }
        if !found_construct {
            return Err(format!("baseline line {} has no construct", line_at + 1));
        }
    }
    Ok(baseline)
}

/// Every protected root that does not resolve under `root`.
///
/// A protected root naming a directory that is not there is a frame defect, not a missing file:
/// the ratchet silently stops guarding whatever that root held. Reported by name so it cannot be
/// read as an ordinary I/O failure, which is how three laboratory-relative roots survived here
/// unnoticed.
pub fn unresolved_protected_roots(root: &Path) -> Vec<String> {
    PROTECTED_ROOTS
        .iter()
        .filter(|protected| !root.join(protected).is_dir())
        .map(|protected| (*protected).to_owned())
        .collect()
}

fn census_repository(root: &Path) -> Result<BTreeMap<(String, String), usize>, String> {
    let unresolved = unresolved_protected_roots(root);
    if !unresolved.is_empty() {
        return Err(format!(
            "protected roots do not resolve under {}: {} — the ratchet would guard nothing there",
            root.display(),
            unresolved.join(", ")
        ));
    }
    let mut files = Vec::new();
    for protected in PROTECTED_ROOTS {
        collect_rust_files(&root.join(protected), &mut files)?;
    }
    files.sort();
    let mut census = BTreeMap::new();
    for file in files {
        let source = fs::read_to_string(&file)
            .map_err(|error| format!("failed to read {}: {error}", file.display()))?;
        let relative = file
            .strip_prefix(root)
            .map_err(|_| format!("{} is outside repository root", file.display()))?
            .to_string_lossy()
            .replace('\\', "/");
        if EXCLUDED_PREFIXES
            .iter()
            .any(|excluded| relative.starts_with(excluded))
        {
            continue;
        }
        for (construct, count) in census_source(&source) {
            if count > 0 {
                census.insert((relative.clone(), construct), count);
            }
        }
    }
    Ok(census)
}

fn collect_rust_files(directory: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(directory)
        .map_err(|error| format!("failed to read {}: {error}", directory.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            format!(
                "failed to inspect an entry under {}: {error}",
                directory.display()
            )
        })?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("failed to inspect {}: {error}", path.display()))?;
        if file_type.is_dir() {
            collect_rust_files(&path, files)?;
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }
    Ok(())
}

fn census_source(source: &str) -> BTreeMap<String, usize> {
    let tokens = rust_tokens(source);
    let ownership = OWNERSHIP_IDENTIFIERS
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let methods = MATERIALIZING_METHODS
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut census = BTreeMap::<String, usize>::new();
    let mut prior_was_dot = false;
    for token in tokens {
        match token {
            RustToken::Dot => prior_was_dot = true,
            RustToken::Identifier(identifier) => {
                if ownership.contains(identifier.as_str()) {
                    *census.entry(identifier.clone()).or_default() += 1;
                }
                if prior_was_dot && methods.contains(identifier.as_str()) {
                    *census.entry(format!(".{identifier}()")).or_default() += 1;
                }
                prior_was_dot = false;
            }
            RustToken::Other => prior_was_dot = false,
        }
    }
    census
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RustToken {
    Identifier(String),
    Dot,
    Other,
}

/// Small Rust lexer sufficient for architecture tokens. Comments and string/character bodies are
/// excluded, so documentation and diagnostic text cannot satisfy or violate the policy.
fn rust_tokens(source: &str) -> Vec<RustToken> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut at = 0usize;
    while at < bytes.len() {
        match bytes[at] {
            b'/' if bytes.get(at + 1) == Some(&b'/') => {
                at += 2;
                while at < bytes.len() && bytes[at] != b'\n' {
                    at += 1;
                }
            }
            b'/' if bytes.get(at + 1) == Some(&b'*') => {
                at += 2;
                let mut depth = 1usize;
                while at < bytes.len() && depth > 0 {
                    if bytes.get(at) == Some(&b'/') && bytes.get(at + 1) == Some(&b'*') {
                        depth += 1;
                        at += 2;
                    } else if bytes.get(at) == Some(&b'*') && bytes.get(at + 1) == Some(&b'/') {
                        depth -= 1;
                        at += 2;
                    } else {
                        at += 1;
                    }
                }
            }
            b'"' => {
                at = skip_quoted(bytes, at + 1, b'"');
            }
            b'\'' if character_literal_starts(bytes, at) => {
                at = skip_quoted(bytes, at + 1, b'\'');
            }
            b'.' => {
                tokens.push(RustToken::Dot);
                at += 1;
            }
            byte if identifier_start(byte) => {
                let start = at;
                at += 1;
                while at < bytes.len() && identifier_continue(bytes[at]) {
                    at += 1;
                }
                tokens.push(RustToken::Identifier(source[start..at].to_owned()));
            }
            byte if byte.is_ascii_whitespace() => at += 1,
            _ => {
                tokens.push(RustToken::Other);
                at += 1;
            }
        }
    }
    tokens
}

fn skip_quoted(bytes: &[u8], mut at: usize, terminator: u8) -> usize {
    while at < bytes.len() {
        if bytes[at] == b'\\' {
            at = at.saturating_add(2);
        } else if bytes[at] == terminator {
            return at + 1;
        } else {
            at += 1;
        }
    }
    at
}

fn character_literal_starts(bytes: &[u8], at: usize) -> bool {
    match (bytes.get(at + 1), bytes.get(at + 2), bytes.get(at + 3)) {
        (Some(b'\\'), Some(_), Some(b'\'')) => true,
        (Some(first), Some(b'\''), _) if *first != b'\n' => true,
        _ => false,
    }
}

fn identifier_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn identifier_continue(byte: u8) -> bool {
    identifier_start(byte) || byte.is_ascii_digit()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_ignores_comments_and_literals_but_counts_owned_operations() {
        let source = r#"
            // BTreeMap and value.clone() are prose.
            let note = "VecDeque .collect()";
            let mut actual = BTreeMap::new();
            let body = actual.clone().into_iter().collect::<Vec<_>>();
        "#;
        let census = census_source(source);
        assert_eq!(census.get("BTreeMap"), Some(&1));
        assert_eq!(census.get("Vec"), Some(&1));
        assert_eq!(census.get(".clone()"), Some(&1));
        assert_eq!(census.get(".into_iter()"), Some(&1));
        assert_eq!(census.get(".collect()"), Some(&1));
        assert_eq!(census.get("VecDeque"), None);
    }

    /// The control that would have caught the laboratory frame, and the one that catches the next
    /// layout move. It fails the moment a protected root stops resolving — which is precisely the
    /// state this crate was in from the day it arrived until 2026-08-10, undetected because the
    /// baseline read aborted `check_repository` before the census ever ran.
    ///
    /// What would make it fail: renaming or moving any of `crates/holonic-engine/src`,
    /// `crates/holonic-language/src`, `crates/holonic-structure/src`, `soma/body/src`,
    /// `soma/membrane/src`, `soma/life/src`.
    #[test]
    fn every_protected_root_resolves_in_this_repository() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("the crate sits two levels under the repository root")
            .to_path_buf();
        assert!(
            root.join("Cargo.toml").is_file(),
            "{} is not the workspace root",
            root.display()
        );
        assert_eq!(
            unresolved_protected_roots(&root),
            Vec::<String>::new(),
            "a protected root does not resolve; the ratchet guards nothing there"
        );
    }

    /// A root with none of the protected directories must be refused by name rather than
    /// returning an empty, clean census. An empty census against an empty baseline is *clean*,
    /// so without this the ratchet passes loudest exactly when it is guarding nothing.
    #[test]
    fn a_root_without_the_protected_directories_is_refused_rather_than_reported_clean() {
        let elsewhere = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let unresolved = unresolved_protected_roots(&elsewhere);
        assert_eq!(unresolved.len(), PROTECTED_ROOTS.len());
        let refusal = census_repository(&elsewhere).expect_err("an absent frame must refuse");
        assert!(refusal.contains("do not resolve"), "{refusal}");
    }
}
