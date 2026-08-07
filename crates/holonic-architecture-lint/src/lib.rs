//! Repository architecture ratchet for continuing holonic machinery.
//!
//! This is an observer and build tool, so it may use host collections internally.  Its output is
//! never machine standing.  Production modules are checked against a committed per-file census:
//! an inherited dependency may disappear, but no file may add another occurrence and a new file
//! begins with zero allowance.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

pub const BASELINE_PATH: &str = "HOLONIC_DSA_BASELINE.tsv";

const PROTECTED_ROOTS: &[&str] = &[
    "crates/holonic-engine/src",
    "crates/holonic-language/src",
    "src/soma/body/src",
    "src/soma/membrane/src",
    "src/soma/life/src",
];

// These files are explicitly classified as historical evidence or reference-only test material
// in the ownership ledger. They must be migrated or retired deliberately, but they are not a
// lawful source for new production code and therefore do not define the production ratchet.
const EXCLUDED_PREFIXES: &[&str] = &[
    "src/soma/life/src/staging/",
    "src/soma/body/src/manifold_tests.rs",
];

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
    let mut report = ArchitectureReport {
        protected_files: observed.len(),
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

fn census_repository(root: &Path) -> Result<BTreeMap<(String, String), usize>, String> {
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
}
