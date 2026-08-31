//! Repository architecture gate for continuing holonic machinery.
//!
//! This is an observer and build tool, so it may use cpu collections internally.  Its output is
//! never machine standing. Production owners are checked against a committed census: an inherited
//! dependency may disappear, but an owner may not add another occurrence. Splitting `owner.rs`
//! into `owner/*.rs` conserves one aggregate allowance across the whole subtree; a genuinely new
//! top-level owner begins with zero allowance.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// Committed census beside the other tracked ledgers.
pub const BASELINE_PATH: &str = "meta/HOLONIC_DSA_BASELINE.tsv";

/// Production roots whose ownership/materialization debt is ratcheted. Apparatus-only
/// `soma/{abi,surface,mount}` and `crates/relational-geometry` remain outside this policy.
const PROTECTED_ROOTS: &[&str] = &[
    "crates/holonic-engine/src",
    "crates/holonic-language/src",
    "crates/holonic-structure/src",
    "soma/body/src",
    "soma/membrane/src",
    "soma/life/src",
];

/// The mounted Athena product cone. A root here is a live product owner, not a historical label:
/// every local module it owns and every Rust module it reaches is inside the structural firewall.
/// Cold Phoenix/Soulkiller evidence remains lawful elsewhere in the repository while it has no
/// live dependency edge from this cone.
const ATHENA_HOT_ROOTS: &[&str] = &["soma/life/src/athena_native/source_neutral_rest.rs"];

/// Source-bearing names which may not cross into the productive Athena dependency closure.
///
/// These are deliberately named structural obstructions rather than a broad ban on words such
/// as `source` or `surface`: cold lineage and receiver prose may still be discussed outside the
/// hot cone.  The UAR0 boundary is narrower and exact.  A source-bearing codec, its persisted
/// surface atlas or occurrence identity, and the exterior participant/relation receiver charts
/// cannot be fields or dependencies of a serializable rest or public hot inference path.
const ATHENA_HOT_FORBIDDEN_SOURCE_BEARING_IDENTIFIERS: &[&str] = &[
    "NativeRelationalCodec",
    "surface_variants",
    "source_occurrence_identity_sha256",
    "ExteriorParticipantReceiverChart",
    "ExteriorRelationReceiverChart",
];

/// Rust crate roots visible to the bounded structural traversal. The lint follows source-level
/// module dependencies; it does not execute Cargo, load build artifacts, or infer a semantic edge
/// from mere co-membership in the workspace.
const PROTECTED_CRATES: &[(&str, &str)] = &[
    ("crates/holonic-engine/src", "holonic_engine"),
    ("crates/holonic-language/src", "holonic_language"),
    ("crates/holonic-structure/src", "holonic_structure"),
    ("soma/body/src", "body"),
    ("soma/membrane/src", "membrane"),
    ("soma/life/src", "life"),
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
    let observed_files = census_repository(root)?;
    let observed = aggregate_split_owners(&baseline, &observed_files);
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
    report
        .violations
        .extend(athena_hot_dependency_violations(root)?);
    Ok(report)
}

/// Charge a mechanically split module tree to its nearest committed owner.
///
/// Rust convention maps `a/b.rs` to descendants under `a/b/`. A child file may therefore spend
/// only the allowance already owned by `a/b.rs`; the parent and every child are summed before the
/// comparison. The deepest committed ancestor wins, so an already committed child owner retains
/// its own independent budget. Paths with no committed ancestor remain exact and start at zero.
fn aggregate_split_owners(
    baseline: &BTreeMap<(String, String), usize>,
    observed: &BTreeMap<(String, String), usize>,
) -> BTreeMap<(String, String), usize> {
    let inherited_paths = baseline
        .keys()
        .map(|(path, _)| path.clone())
        .collect::<BTreeSet<_>>();
    let mut aggregate = BTreeMap::<(String, String), usize>::new();
    for ((path, construct), count) in observed {
        let owner = nearest_inherited_owner(path, &inherited_paths).unwrap_or(path);
        *aggregate
            .entry((owner.to_owned(), construct.clone()))
            .or_default() += count;
    }
    aggregate
}

fn nearest_inherited_owner<'a>(
    path: &'a str,
    inherited_paths: &'a BTreeSet<String>,
) -> Option<&'a str> {
    if let Some(exact) = inherited_paths.get(path) {
        return Some(exact);
    }
    inherited_paths
        .iter()
        .filter(|candidate| {
            let file_module = candidate.strip_suffix(".rs").map(|stem| format!("{stem}/"));
            let directory_module = candidate
                .strip_suffix("/mod.rs")
                .map(|directory| format!("{directory}/"));
            file_module
                .iter()
                .chain(directory_module.iter())
                .any(|prefix| path.starts_with(prefix))
        })
        .max_by_key(|candidate| candidate.len())
        .map(String::as_str)
}

/// Return only the live Athena foreign-boundary violations. This focused receiver is used during
/// owner-local refactors before the one permitted release-time ownership-ledger regeneration; it
/// does not weaken or replace [`check_repository`].
pub fn check_athena_hot_boundary(root: &Path) -> Result<Vec<ArchitectureViolation>, String> {
    athena_hot_dependency_violations(root)
}

/// Focused K2 receiver for the one-way Soulkiller boundary. Soulkiller may own exterior
/// realization testimony, but it may not expose a foreign product runtime, an architecture-
/// specific operator/cache ontology, or a retired Phoenix route. Athena's transitive firewall is
/// composed into the same return.
pub fn check_soulkiller_boundary(root: &Path) -> Result<Vec<ArchitectureViolation>, String> {
    let mut violations = athena_hot_dependency_violations(root)?;
    let soulkiller_root = root.join("crates/holonic-engine/src/soulkiller");
    let expected = BTreeSet::from([
        "foreign_potential_rest.rs".to_owned(),
        "foreign_section_descent.rs".to_owned(),
        "mod.rs".to_owned(),
        "receiver_restricted_transport.rs".to_owned(),
        "scrapyard.rs".to_owned(),
    ]);
    let mut observed = BTreeSet::new();
    if soulkiller_root.is_dir() {
        for entry in fs::read_dir(&soulkiller_root)
            .map_err(|error| format!("read {}: {error}", soulkiller_root.display()))?
        {
            let entry = entry.map_err(|error| error.to_string())?;
            if entry
                .file_type()
                .map_err(|error| error.to_string())?
                .is_file()
            {
                observed.insert(entry.file_name().to_string_lossy().into_owned());
            }
        }
    }
    for unexpected in observed.difference(&expected) {
        violations.push(ArchitectureViolation {
            path: format!("crates/holonic-engine/src/soulkiller/{unexpected}"),
            construct: "soulkiller:unexpected-live-owner".to_owned(),
            allowed: 0,
            observed: 1,
        });
    }
    for missing in expected.difference(&observed) {
        violations.push(ArchitectureViolation {
            path: format!("crates/holonic-engine/src/soulkiller/{missing}"),
            construct: "soulkiller:missing-boundary-owner".to_owned(),
            allowed: 1,
            observed: 0,
        });
    }

    let forbidden_identifiers = BTreeSet::from([
        "ProductSession",
        "RuntimeReturn",
        "TowerReturn",
        "LayerFace",
        "ForeignInferenceOwner",
        "ForeignHotState",
        "InferenceCache",
    ]);
    let forbidden_literals = [
        "holonic-engine.phoenix",
        "crate::phoenix",
        "holonic_engine::phoenix",
        "foreign_inference_owner",
        "foreign_hot_state",
        "inference_cache",
        "gemma",
    ];
    for file in expected
        .iter()
        .filter(|file| observed.contains(file.as_str()))
    {
        let relative = format!("crates/holonic-engine/src/soulkiller/{file}");
        let source = fs::read_to_string(root.join(&relative))
            .map_err(|error| format!("read {relative}: {error}"))?;
        let tokens = firewall_tokens(&without_cfg_test_items(&source));
        let mut count = 0usize;
        for token in tokens {
            match token {
                FirewallToken::Identifier(identifier)
                    if forbidden_identifiers.contains(identifier.as_str()) =>
                {
                    count += 1;
                }
                FirewallToken::StringLiteral(value)
                    if forbidden_literals
                        .iter()
                        .any(|forbidden| value.to_ascii_lowercase().contains(forbidden)) =>
                {
                    count += 1;
                }
                _ => {}
            }
        }
        if count > 0 {
            violations.push(ArchitectureViolation {
                path: relative,
                construct: "soulkiller:architecture-or-cache-specific-positive-dependency"
                    .to_owned(),
                allowed: 0,
                observed: count,
            });
        }
    }

    for relative in [
        "crates/holonic-engine/src/lib.rs",
        "soma/life/src/lib.rs",
        "soma/life/src/bin/eros.rs",
    ] {
        let source = fs::read_to_string(root.join(relative))
            .map_err(|error| format!("read {relative}: {error}"))?;
        let live = without_cfg_test_items(&source).to_ascii_lowercase();
        for forbidden in [
            "pub mod phoenix",
            "holonic_engine::phoenix",
            "soulkiller_active_transport",
            "phoenix_returned_defect",
            "eros phoenix",
        ] {
            let count = live.matches(forbidden).count();
            if count > 0 {
                violations.push(ArchitectureViolation {
                    path: relative.to_owned(),
                    construct: format!("soulkiller:retired-live-route:{forbidden}"),
                    allowed: 0,
                    observed: count,
                });
            }
        }
    }
    violations
        .sort_by(|left, right| (&left.path, &left.construct).cmp(&(&right.path, &right.construct)));
    violations.dedup();
    Ok(violations)
}

fn athena_hot_dependency_violations(root: &Path) -> Result<Vec<ArchitectureViolation>, String> {
    let sources = firewall_sources(root)?;
    let by_path = sources
        .iter()
        .enumerate()
        .map(|(at, source)| (source.path.clone(), at))
        .collect::<BTreeMap<_, _>>();
    let by_module = sources
        .iter()
        .enumerate()
        .map(|(at, source)| ((source.crate_name.clone(), source.module.clone()), at))
        .collect::<BTreeMap<_, _>>();
    let mut direct = BTreeSet::new();
    for hot_root in ATHENA_HOT_ROOTS {
        let absolute = root.join(hot_root);
        if absolute.is_file() {
            if let Some(at) = by_path.get(*hot_root) {
                direct.insert(*at);
            }
        } else if absolute.is_dir() {
            let prefix = format!("{}/", hot_root.trim_end_matches('/'));
            direct.extend(
                sources
                    .iter()
                    .enumerate()
                    .filter(|(_, source)| source.path.starts_with(&prefix))
                    .map(|(at, _)| at),
            );
        }
    }
    let mut pending = direct.iter().copied().collect::<Vec<_>>();
    let mut reached = BTreeSet::new();
    let mut violations = Vec::new();
    while let Some(at) = pending.pop() {
        if !reached.insert(at) {
            continue;
        }
        let source = &sources[at];
        let disposition = if direct.contains(&at) {
            "direct"
        } else {
            "transitive"
        };
        let foreign = athena_hot_source_violations(&source.source, disposition);
        let foreign_owner = foreign_namespace_in_path(&source.path);
        for (construct, observed) in foreign {
            violations.push(ArchitectureViolation {
                path: source.path.clone(),
                construct,
                allowed: 0,
                observed,
            });
        }
        if let Some(namespace) = foreign_owner {
            violations.push(ArchitectureViolation {
                path: source.path.clone(),
                construct: format!("athena-hot:{disposition}:{namespace}-namespace-owner"),
                allowed: 0,
                observed: 1,
            });
        }

        // Crossing a foreign namespace already returns the shortest structural obstruction. Do
        // not turn the report into a census of the whole foreign realization behind that edge.
        if foreign_owner.is_some()
            || athena_hot_source_violations(&source.source, disposition)
                .iter()
                .any(|(construct, _)| construct.contains("-namespace"))
        {
            continue;
        }
        for dependency in source_dependencies(source, &by_module) {
            if !reached.contains(&dependency) {
                pending.push(dependency);
            }
        }
    }
    violations
        .sort_by(|left, right| (&left.path, &left.construct).cmp(&(&right.path, &right.construct)));
    violations.dedup();
    Ok(violations)
}

#[derive(Clone, Debug)]
struct FirewallSource {
    path: String,
    crate_name: String,
    module: Vec<String>,
    source: String,
}

fn athena_hot_source_violations(source: &str, disposition: &str) -> Vec<(String, usize)> {
    let source = without_cfg_test_items(source);
    let tokens = firewall_tokens(&source);
    let mut counts = BTreeMap::<String, usize>::new();
    for token in &tokens {
        if let FirewallToken::Identifier(identifier) = token {
            if ATHENA_HOT_FORBIDDEN_SOURCE_BEARING_IDENTIFIERS
                .iter()
                .any(|forbidden| *forbidden == identifier)
            {
                *counts
                    .entry(format!(
                        "athena-hot:{disposition}:forbidden-source-bearing:{identifier}"
                    ))
                    .or_default() += 1;
            }
            if let Some(namespace) = foreign_namespace(identifier) {
                *counts
                    .entry(format!("athena-hot:{disposition}:{namespace}-namespace"))
                    .or_default() += 1;
            }
        }
    }

    let mut schema_context = 0usize;
    for token in &tokens {
        match token {
            FirewallToken::Identifier(identifier)
                if identifier.to_ascii_lowercase().contains("schema")
                    || identifier.eq_ignore_ascii_case("serde") =>
            {
                schema_context = 16;
            }
            FirewallToken::StringLiteral(value) if schema_context > 0 => {
                if let Some(namespace) = foreign_namespace(value) {
                    *counts
                        .entry(format!("athena-hot:{disposition}:{namespace}-schema"))
                        .or_default() += 1;
                }
                schema_context = 0;
            }
            FirewallToken::Semi | FirewallToken::Comma => schema_context = 0,
            _ if schema_context > 0 => schema_context -= 1,
            _ => {}
        }
    }
    counts.into_iter().collect()
}

fn firewall_sources(root: &Path) -> Result<Vec<FirewallSource>, String> {
    let mut sources = Vec::new();
    for (crate_root, crate_name) in PROTECTED_CRATES {
        let absolute_root = root.join(crate_root);
        if !absolute_root.is_dir() {
            continue;
        }
        let mut files = Vec::new();
        collect_rust_files(&absolute_root, &mut files)?;
        files.sort();
        for file in files {
            if !is_live_rust_file(&file) {
                continue;
            }
            let module_relative = file.strip_prefix(&absolute_root).map_err(|_| {
                format!("{} is outside {}", file.display(), absolute_root.display())
            })?;
            let module = module_segments(module_relative)?;
            let path = file
                .strip_prefix(root)
                .map_err(|_| format!("{} is outside repository root", file.display()))?
                .to_string_lossy()
                .replace('\\', "/");
            let source = fs::read_to_string(&file)
                .map_err(|error| format!("failed to read {}: {error}", file.display()))?;
            sources.push(FirewallSource {
                path,
                crate_name: (*crate_name).to_owned(),
                module,
                source,
            });
        }
    }
    sources.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(sources)
}

fn is_live_rust_file(path: &Path) -> bool {
    let file = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    file != "tests.rs"
        && !file.ends_with("_tests.rs")
        && !path
            .components()
            .any(|component| component.as_os_str() == "tests")
}

fn module_segments(relative: &Path) -> Result<Vec<String>, String> {
    let mut components = relative
        .components()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    let file = components
        .pop()
        .ok_or_else(|| format!("{} has no Rust filename", relative.display()))?;
    if file == "lib.rs" || file == "main.rs" {
        return Ok(Vec::new());
    }
    if file != "mod.rs" {
        let stem = file
            .strip_suffix(".rs")
            .ok_or_else(|| format!("{} is not a Rust source", relative.display()))?;
        components.push(stem.to_owned());
    }
    Ok(components)
}

fn source_dependencies(
    source: &FirewallSource,
    modules: &BTreeMap<(String, Vec<String>), usize>,
) -> BTreeSet<usize> {
    let live = without_cfg_test_items(&source.source);
    let tokens = firewall_tokens(&live);
    let mut references = qualified_paths(&tokens);
    references.extend(use_paths(&tokens));
    references
        .into_iter()
        .filter_map(|reference| resolve_module(source, &reference, modules))
        .collect()
}

fn resolve_module(
    source: &FirewallSource,
    reference: &[String],
    modules: &BTreeMap<(String, Vec<String>), usize>,
) -> Option<usize> {
    if reference.is_empty() {
        return None;
    }
    let mut candidates = Vec::<(String, Vec<String>)>::new();
    match reference[0].as_str() {
        "crate" => candidates.push((source.crate_name.clone(), reference[1..].to_vec())),
        "self" => {
            let mut path = source.module.clone();
            path.extend_from_slice(&reference[1..]);
            candidates.push((source.crate_name.clone(), path));
        }
        "super" => {
            let mut path = source.module.clone();
            let mut at = 0usize;
            while reference.get(at).is_some_and(|segment| segment == "super") {
                path.pop();
                at += 1;
            }
            path.extend_from_slice(&reference[at..]);
            candidates.push((source.crate_name.clone(), path));
        }
        first
            if PROTECTED_CRATES
                .iter()
                .any(|(_, crate_name)| first == *crate_name) =>
        {
            candidates.push((first.to_owned(), reference[1..].to_vec()));
        }
        _ => {
            let mut relative = source.module.clone();
            relative.extend_from_slice(reference);
            candidates.push((source.crate_name.clone(), relative));
            candidates.push((source.crate_name.clone(), reference.to_vec()));
        }
    }
    for (crate_name, path) in candidates {
        for extent in (1..=path.len()).rev() {
            if let Some(module) = modules.get(&(crate_name.clone(), path[..extent].to_vec())) {
                return Some(*module);
            }
        }
    }
    None
}

fn qualified_paths(tokens: &[FirewallToken]) -> Vec<Vec<String>> {
    let mut paths = Vec::new();
    let mut at = 0usize;
    while at < tokens.len() {
        let FirewallToken::Identifier(first) = &tokens[at] else {
            at += 1;
            continue;
        };
        let mut path = vec![first.clone()];
        let mut until = at + 1;
        while matches!(tokens.get(until), Some(FirewallToken::PathSeparator)) {
            let Some(FirewallToken::Identifier(next)) = tokens.get(until + 1) else {
                break;
            };
            path.push(next.clone());
            until += 2;
        }
        if path.len() > 1 {
            paths.push(path);
            at = until;
        } else {
            at += 1;
        }
    }
    paths
}

fn use_paths(tokens: &[FirewallToken]) -> Vec<Vec<String>> {
    let mut paths = Vec::new();
    let mut at = 0usize;
    while at < tokens.len() {
        if !matches!(tokens.get(at), Some(FirewallToken::Identifier(identifier)) if identifier == "use")
        {
            at += 1;
            continue;
        }
        at += 1;
        parse_use_tree(tokens, &mut at, Vec::new(), &mut paths);
        while at < tokens.len() && !matches!(tokens[at], FirewallToken::Semi) {
            at += 1;
        }
    }
    paths
}

fn parse_use_tree(
    tokens: &[FirewallToken],
    at: &mut usize,
    prefix: Vec<String>,
    paths: &mut Vec<Vec<String>>,
) {
    let mut path = prefix;
    while *at < tokens.len() {
        match &tokens[*at] {
            FirewallToken::Identifier(identifier) if identifier == "as" => {
                *at += 1;
                if matches!(tokens.get(*at), Some(FirewallToken::Identifier(_))) {
                    *at += 1;
                }
                if !path.is_empty() {
                    paths.push(path);
                }
                return;
            }
            FirewallToken::Identifier(identifier) => {
                path.push(identifier.clone());
                *at += 1;
            }
            FirewallToken::PathSeparator => *at += 1,
            FirewallToken::OpenBrace => {
                *at += 1;
                while *at < tokens.len() && !matches!(tokens[*at], FirewallToken::CloseBrace) {
                    parse_use_tree(tokens, at, path.clone(), paths);
                    if matches!(tokens.get(*at), Some(FirewallToken::Comma)) {
                        *at += 1;
                    }
                }
                if matches!(tokens.get(*at), Some(FirewallToken::CloseBrace)) {
                    *at += 1;
                }
                return;
            }
            FirewallToken::Star => {
                if !path.is_empty() {
                    paths.push(path);
                }
                *at += 1;
                return;
            }
            FirewallToken::Comma | FirewallToken::CloseBrace | FirewallToken::Semi => {
                if !path.is_empty() {
                    paths.push(path);
                }
                return;
            }
            _ => *at += 1,
        }
    }
    if !path.is_empty() {
        paths.push(path);
    }
}

fn foreign_namespace(value: &str) -> Option<&'static str> {
    let value = value.to_ascii_lowercase();
    if value.contains("phoenix") {
        Some("phoenix")
    } else if value.contains("soulkiller") {
        Some("soulkiller")
    } else {
        None
    }
}

fn foreign_namespace_in_path(path: &str) -> Option<&'static str> {
    path.split('/').find_map(foreign_namespace)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum FirewallToken {
    Identifier(String),
    StringLiteral(String),
    PathSeparator,
    OpenBrace,
    CloseBrace,
    Comma,
    Semi,
    Star,
    Other,
}

fn firewall_tokens(source: &str) -> Vec<FirewallToken> {
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
                let start = at + 1;
                let end = skip_quoted(bytes, start, b'"');
                let content_end = end.saturating_sub(1).max(start);
                tokens.push(FirewallToken::StringLiteral(
                    source
                        .get(start..content_end)
                        .unwrap_or_default()
                        .to_owned(),
                ));
                at = end;
            }
            b'\'' if character_literal_starts(bytes, at) => {
                at = skip_quoted(bytes, at + 1, b'\'');
            }
            b':' if bytes.get(at + 1) == Some(&b':') => {
                tokens.push(FirewallToken::PathSeparator);
                at += 2;
            }
            b'{' => {
                tokens.push(FirewallToken::OpenBrace);
                at += 1;
            }
            b'}' => {
                tokens.push(FirewallToken::CloseBrace);
                at += 1;
            }
            b',' => {
                tokens.push(FirewallToken::Comma);
                at += 1;
            }
            b';' => {
                tokens.push(FirewallToken::Semi);
                at += 1;
            }
            b'*' => {
                tokens.push(FirewallToken::Star);
                at += 1;
            }
            byte if identifier_start(byte) => {
                let start = at;
                at += 1;
                while at < bytes.len() && identifier_continue(bytes[at]) {
                    at += 1;
                }
                tokens.push(FirewallToken::Identifier(source[start..at].to_owned()));
            }
            byte if byte.is_ascii_whitespace() => at += 1,
            _ => {
                tokens.push(FirewallToken::Other);
                at += 1;
            }
        }
    }
    tokens
}

/// Remove ordinary `#[cfg(test)]` items before dependency traversal. Test fixture files are also
/// excluded by path, so foreign matched controls do not become production reachability.
fn without_cfg_test_items(source: &str) -> String {
    const MARKER: &str = "#[cfg(test)]";
    let mut bytes = source.as_bytes().to_vec();
    let mut search = 0usize;
    while let Some(offset) = source[search..].find(MARKER) {
        let start = search + offset;
        let mut at = start + MARKER.len();
        while at < bytes.len() && bytes[at].is_ascii_whitespace() {
            at += 1;
        }
        let mut end = at;
        while end < bytes.len() && bytes[end] != b'{' && bytes[end] != b';' {
            end += 1;
        }
        if bytes.get(end) == Some(&b'{') {
            let mut depth = 1usize;
            end += 1;
            while end < bytes.len() && depth > 0 {
                match bytes[end] {
                    b'"' => end = skip_quoted(&bytes, end + 1, b'"'),
                    b'\'' if character_literal_starts(&bytes, end) => {
                        end = skip_quoted(&bytes, end + 1, b'\'')
                    }
                    b'{' => {
                        depth += 1;
                        end += 1;
                    }
                    b'}' => {
                        depth -= 1;
                        end += 1;
                    }
                    _ => end += 1,
                }
            }
        } else if bytes.get(end) == Some(&b';') {
            end += 1;
        }
        for byte in &mut bytes[start..end] {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
        search = end.max(start + MARKER.len());
    }
    String::from_utf8(bytes).expect("blanking complete Rust items preserves UTF-8")
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
    fn a_split_module_conserves_the_parent_owners_total_allowance() {
        let baseline = BTreeMap::from([
            (("soma/life/src/owner.rs".to_owned(), "Vec".to_owned()), 3),
            (
                (
                    "soma/life/src/owner/existing.rs".to_owned(),
                    ".clone()".to_owned(),
                ),
                2,
            ),
        ]);
        let observed = BTreeMap::from([
            (("soma/life/src/owner.rs".to_owned(), "Vec".to_owned()), 1),
            (
                ("soma/life/src/owner/moved.rs".to_owned(), "Vec".to_owned()),
                2,
            ),
            (
                (
                    "soma/life/src/owner/existing/deeper.rs".to_owned(),
                    ".clone()".to_owned(),
                ),
                2,
            ),
        ]);

        let aggregate = aggregate_split_owners(&baseline, &observed);
        assert_eq!(
            aggregate.get(&("soma/life/src/owner.rs".to_owned(), "Vec".to_owned())),
            Some(&3)
        );
        assert_eq!(
            aggregate.get(&(
                "soma/life/src/owner/existing.rs".to_owned(),
                ".clone()".to_owned()
            )),
            Some(&2)
        );
    }

    #[test]
    fn an_established_mod_file_owns_its_split_sibling_modules() {
        let baseline = BTreeMap::from([(
            (
                "soma/life/src/athena_native/mod.rs".to_owned(),
                "Vec".to_owned(),
            ),
            2,
        )]);
        let observed = BTreeMap::from([(
            (
                "soma/life/src/athena_native/new_owner.rs".to_owned(),
                "Vec".to_owned(),
            ),
            2,
        )]);

        let aggregate = aggregate_split_owners(&baseline, &observed);
        assert_eq!(
            aggregate.get(&(
                "soma/life/src/athena_native/mod.rs".to_owned(),
                "Vec".to_owned()
            )),
            Some(&2)
        );
    }

    #[test]
    fn a_new_top_level_owner_still_begins_with_zero_allowance() {
        let baseline =
            BTreeMap::from([(("soma/life/src/owner.rs".to_owned(), "Vec".to_owned()), 1)]);
        let observed =
            BTreeMap::from([(("soma/life/src/other.rs".to_owned(), "Vec".to_owned()), 1)]);

        let aggregate = aggregate_split_owners(&baseline, &observed);
        assert_eq!(
            aggregate.get(&("soma/life/src/other.rs".to_owned(), "Vec".to_owned())),
            Some(&1)
        );
        assert!(!baseline.contains_key(&("soma/life/src/other.rs".to_owned(), "Vec".to_owned())));
    }

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

    #[test]
    fn athena_hot_cone_refuses_foreign_execution_even_when_a_wrapper_calls_it_native() {
        let safe = "use crate::receiver_history_compression::ReceiverHistoryCompression;";
        assert!(athena_hot_source_violations(safe, "direct").is_empty());

        let contaminated = r#"
            use holonic_engine::phoenix::runtime::ProductSession;
            struct NativeWrapper(ProductSession);
        "#;
        let violations = athena_hot_source_violations(contaminated, "direct");
        assert!(
            violations
                .iter()
                .any(|(kind, _)| kind == "athena-hot:direct:phoenix-namespace")
        );
    }

    #[test]
    fn athena_hot_cone_refuses_foreign_schema_but_ignores_test_only_code() {
        let source = r#"
            const REST_SCHEMA: &str = "holonics.soulkiller.native-rest.v1";
            #[cfg(test)]
            mod tests {
                use holonic_engine::phoenix::runtime::ProductSession;
            }
        "#;
        let violations = athena_hot_source_violations(source, "direct");
        assert!(
            violations
                .iter()
                .any(|(kind, _)| kind == "athena-hot:direct:soulkiller-schema")
        );
        assert!(!violations.iter().any(|(kind, _)| kind.contains("phoenix")));
    }

    #[test]
    fn athena_hot_cone_refuses_each_uar0_source_bearing_name() {
        let source = r#"
            // These mentions are not source-bearing structure.
            const NOTE: &str = "NativeRelationalCodec surface_variants source_occurrence_identity_sha256";

            #[derive(Serialize)]
            pub struct ProductRest {
                codec: NativeRelationalCodec,
                surface_variants: Vec<String>,
                source_occurrence_identity_sha256: [u8; 32],
                participant: ExteriorParticipantReceiverChart,
                relation: ExteriorRelationReceiverChart,
            }

            pub fn infer(codec: NativeRelationalCodec) -> ProductRest {
                let _ = codec;
                unimplemented!()
            }

            #[cfg(test)]
            mod tests {
                use super::{NativeRelationalCodec, surface_variants};
            }
        "#;
        let violations = athena_hot_source_violations(source, "direct");
        for forbidden in ATHENA_HOT_FORBIDDEN_SOURCE_BEARING_IDENTIFIERS {
            let construct = format!("athena-hot:direct:forbidden-source-bearing:{forbidden}");
            assert_eq!(
                violations
                    .iter()
                    .find(|(kind, _)| kind == &construct)
                    .map(|(_, count)| *count),
                Some(if *forbidden == "NativeRelationalCodec" {
                    2
                } else {
                    1
                }),
                "missing exact UAR0 obstruction for {forbidden}"
            );
        }
        assert!(!violations.iter().any(|(kind, _)| kind.contains("NOTE")));
    }

    #[test]
    fn athena_hot_dependency_report_keeps_the_precise_source_path() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time advances")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "holonic-architecture-lint-uar0-{}-{nonce}",
            std::process::id()
        ));
        let hot = root.join("soma/life/src/athena_native");
        std::fs::create_dir_all(&hot).expect("hot fixture");
        std::fs::write(
            hot.join("source_neutral_rest.rs"),
            "pub struct Rest { codec: NativeRelationalCodec, surface_variants: Vec<u8> }",
        )
        .expect("hot source");

        let violations = athena_hot_dependency_violations(&root).expect("firewall traversal");
        assert!(violations.iter().any(|violation| {
            violation.path == "soma/life/src/athena_native/source_neutral_rest.rs"
                && violation.construct
                    == "athena-hot:direct:forbidden-source-bearing:NativeRelationalCodec"
        }));
        assert!(violations.iter().any(|violation| {
            violation.path == "soma/life/src/athena_native/source_neutral_rest.rs"
                && violation.construct
                    == "athena-hot:direct:forbidden-source-bearing:surface_variants"
        }));

        std::fs::remove_dir_all(&root).expect("remove exact UAR0 fixture");
    }

    #[test]
    fn athena_hot_roots_do_not_bless_foreign_namespace_owners() {
        assert!(
            ATHENA_HOT_ROOTS
                .iter()
                .all(|root| foreign_namespace_in_path(root).is_none())
        );
    }

    #[test]
    fn athena_hot_cone_follows_a_transitive_foreign_import_but_leaves_cold_evidence_alone() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time advances")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "holonic-architecture-lint-{}-{nonce}",
            std::process::id()
        ));
        let life = root.join("soma/life/src");
        let engine = root.join("crates/holonic-engine/src/phoenix");
        std::fs::create_dir_all(life.join("athena_native")).expect("athena fixture");
        std::fs::create_dir_all(&engine).expect("engine fixture");
        std::fs::write(
            life.join("athena_native/source_neutral_rest.rs"),
            "use crate::bridge::Native; pub struct Rest(Native);",
        )
        .expect("hot source");
        std::fs::write(
            life.join("bridge.rs"),
            "use holonic_engine::phoenix::runtime::ProductSession; pub struct Native(ProductSession);",
        )
        .expect("bridge source");
        std::fs::write(
            life.join("cold_exterior.rs"),
            "pub const WITNESS_SCHEMA: &str = \"holonics.phoenix.witness.v1\";",
        )
        .expect("cold evidence");
        std::fs::write(
            life.join("lib.rs"),
            "mod bridge; mod cold_exterior; pub mod athena_native;",
        )
        .expect("life root");
        std::fs::write(engine.join("mod.rs"), "pub mod runtime;").expect("phoenix root");
        std::fs::write(engine.join("runtime.rs"), "pub struct ProductSession;")
            .expect("phoenix runtime");
        std::fs::write(
            root.join("crates/holonic-engine/src/lib.rs"),
            "pub mod phoenix;",
        )
        .expect("engine root");

        let violations = athena_hot_dependency_violations(&root).expect("firewall traversal");
        assert!(violations.iter().any(|violation| {
            violation.path == "soma/life/src/bridge.rs"
                && violation.construct == "athena-hot:transitive:phoenix-namespace"
        }));
        assert!(
            !violations
                .iter()
                .any(|violation| violation.path.ends_with("cold_exterior.rs"))
        );

        std::fs::remove_dir_all(&root).expect("remove exact firewall fixture");
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
        // Do not bake `CARGO_MANIFEST_DIR` into the test binary: this workspace deliberately
        // shares a target directory with detached audit worktrees, and Cargo may lawfully reuse a
        // binary compiled in one of them. Resolve the executing workspace at runtime instead.
        let current = std::env::current_dir().expect("the test process has a current directory");
        let root = current
            .ancestors()
            .find(|candidate| {
                std::fs::read_to_string(candidate.join("Cargo.toml"))
                    .is_ok_and(|manifest| manifest.contains("[workspace]"))
            })
            .expect("the test runs below a Cargo workspace")
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
