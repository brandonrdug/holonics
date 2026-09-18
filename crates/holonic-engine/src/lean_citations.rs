//! **Library-level citation check: every Lean name a Rust owner cites is declared.**
//!
//! [definition] Each paired owner publishes a correspondence table in its module header, and each
//! owner's prose cites Lean declarations as `Foundation/<File>.lean::<Name>`. Both are claims
//! about a file this repository carries, and both go stale silently — a renamed theorem leaves a
//! citation that reads correctly and names nothing. This module turns the claim into a test: the
//! Lean owner is read, its declarations are collected, and every cited name is looked up. A stale
//! citation fails `cargo test` instead of waiting for a review.
//!
//! [definition] Two scans run:
//!
//! 1. **The correspondence tables.** For each paired owner below, every backticked name in the
//!    first column of a `//! | ...` row must be declared by that owner's Lean file.
//! 2. **The inline citations.** Anywhere in the tree's engine sources, a
//!    `Foundation/<File>.lean::<Name>` or `Transport/<File>.lean::<Name>` citation must name a
//!    declaration of that file — and the file must exist.
//!
//! [definition] A Lean declaration is found by its **final segment**: Lean writes a declaration
//! unqualified inside its `namespace`, so a correctly qualified citation `A.B.c` need not occur as
//! a literal substring of the file. The collected set therefore carries both the written name and
//! its leaf, and a citation matches either.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// The repository root, from this crate's manifest directory.
fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("the crate manifest sits two directories below the repository root")
}

fn lean_root() -> PathBuf {
    repository_root()
        .join("formal")
        .join("elementary-holonics")
        .join("ElementaryHolonics")
}

/// Tokens that may precede a declaration keyword.
const MODIFIERS: [&str; 8] = [
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "scoped",
    "local",
    "nonrec",
];

/// The declaration keywords this scan reads.
const KEYWORDS: [&str; 11] = [
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "instance",
    "axiom",
    "opaque",
    "macro",
];

/// Whether a token is a plain Lean identifier (possibly dotted).
fn is_identifier(token: &str) -> bool {
    !token.is_empty()
        && token
            .chars()
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && token.chars().all(|character| {
            character.is_alphanumeric()
                || character == '_'
                || character == '.'
                || character == '\''
                || character == '!'
                || character == '?'
        })
}

fn leaf(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// Every declaration name a Lean source declares: the written name and its final segment, plus
/// inductive constructors and structure fields, which are cited as `Type.field` and declared
/// unqualified.
fn declared_names(source: &str) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    // A declaration head may carry a universe annotation (`structure Tube.{us, ui}`) or run
    // straight into a binder, so the token is truncated at the first character an identifier
    // cannot carry and its trailing dot dropped.
    let mut record = |token: &str| {
        let head: String = token
            .chars()
            .take_while(|character| {
                character.is_alphanumeric()
                    || *character == '_'
                    || *character == '.'
                    || *character == '\''
                    || *character == '!'
                    || *character == '?'
            })
            .collect();
        let name = head.trim_end_matches('.');
        if is_identifier(name) {
            names.insert(name.to_owned());
            names.insert(leaf(name).to_owned());
        }
    };
    for line in source.lines() {
        let indented = line.starts_with(' ');
        let mut rest = line.trim_start();
        while rest.starts_with("@[") {
            match rest.find(']') {
                Some(at) => rest = rest[at + 1..].trim_start(),
                None => break,
            }
        }
        let mut tokens = rest.split_whitespace();
        let mut head = tokens.next();
        while head.is_some_and(|word| MODIFIERS.contains(&word)) {
            head = tokens.next();
        }
        let Some(head) = head else { continue };
        if KEYWORDS.contains(&head) {
            if let Some(name) = tokens.next() {
                record(name);
            }
            continue;
        }
        // An inductive constructor: `  | released : ...`.
        if head == "|" {
            if let Some(name) = tokens.next() {
                record(name);
            }
            continue;
        }
        // A structure field: `  crosses : ...`, indented and immediately followed by a colon.
        if indented && tokens.next() == Some(":") {
            record(head);
        }
    }
    names
}

fn declares(names: &BTreeSet<String>, cited: &str) -> bool {
    names.contains(cited) || names.contains(leaf(cited))
}

/// The Lean names the first column of a header correspondence table cites.
fn cited_in_table(header: &str) -> Vec<String> {
    let mut cited = Vec::new();
    for row in header.lines().filter(|line| line.starts_with("//! | `")) {
        let Some(cell) = row.split('|').nth(1) else {
            continue;
        };
        for name in cell.split('`').skip(1).step_by(2) {
            for piece in name.split(',') {
                let piece = piece.trim().trim_end_matches('.');
                if is_identifier(piece) {
                    cited.push(piece.to_owned());
                }
            }
        }
    }
    cited
}

/// Names a table may cite that Mathlib — not this formalization — declares. Listed explicitly so
/// that "it is Mathlib's" is a statement and not a hole in the check.
const MATHLIB_NAMES: [&str; 1] = ["Preorder"];

/// The paired owners. Each entry is `(Rust owner source, its name, the Lean owner's path under
/// `ElementaryHolonics/`)`. The Rust sources are `include_str!`ed, so a moved file is a compile
/// error rather than a skipped check.
#[allow(clippy::type_complexity)]
fn paired_owners() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        (
            include_str!("receiver_release.rs"),
            "receiver_release.rs",
            "Foundation/ReceiverRelease.lean",
        ),
        (
            include_str!("receiver_atlas.rs"),
            "receiver_atlas.rs",
            "Foundation/ReceiverAtlas.lean",
        ),
        (
            include_str!("acoustic_receiver.rs"),
            "acoustic_receiver.rs",
            "Foundation/AcousticReceiver.lean",
        ),
        (
            include_str!("topological_receiver.rs"),
            "topological_receiver.rs",
            "Foundation/TopologicalReceiver.lean",
        ),
        (
            include_str!("continuing_tube.rs"),
            "continuing_tube.rs",
            "Transport/ContinuingTube.lean",
        ),
        (
            include_str!("iwasawa_tower.rs"),
            "iwasawa_tower.rs",
            "Foundation/IwasawaTower.lean",
        ),
        (
            include_str!("physical_occurrence.rs"),
            "physical_occurrence.rs",
            "Foundation/PhysicalOccurrence.lean",
        ),
        (
            include_str!("physical_occurrence/passage.rs"),
            "physical_occurrence/passage.rs",
            "Foundation/PhysicalOccurrence.lean",
        ),
        (
            include_str!("physical_occurrence/plural_fibre.rs"),
            "physical_occurrence/plural_fibre.rs",
            "Foundation/PhysicalOccurrence.lean",
        ),
        (
            include_str!("presentation_cost.rs"),
            "presentation_cost.rs",
            "Foundation/PresentationCost.lean",
        ),
        (
            include_str!("bridge.rs"),
            "bridge.rs",
            "Foundation/Bridge.lean",
        ),
        (
            include_str!("continuing_tower.rs"),
            "continuing_tower.rs",
            "Foundation/ContinuingTower.lean",
        ),
        (
            include_str!("grain_tower.rs"),
            "grain_tower.rs",
            "Foundation/GrainRestriction.lean",
        ),
        (
            include_str!("physical_intake.rs"),
            "physical_intake.rs",
            "Foundation/ExteriorIntake.lean",
        ),
        // `physical_constraint_grading.rs`'s header table is written the other way round — the
        // Rust owner in the first column and the Lean name in the second — so it is not read by
        // this scan. Its inline `Foundation/…lean::Name` citations are covered by the second test.
        (
            include_str!("rigidity_receiver.rs"),
            "rigidity_receiver.rs",
            "Foundation/RigidityReceiver.lean",
        ),
        (
            include_str!("physical_constraint_complex.rs"),
            "physical_constraint_complex.rs",
            "Foundation/AperturedGradedComplex.lean",
        ),
    ]
}

/// Every declaration name the whole formalization declares. A citation the module's own owner does
/// not carry is looked up here before it is called stale.
fn every_declared_name() -> BTreeSet<String> {
    fn walk(directory: &Path, into: &mut BTreeSet<String>) {
        let Ok(entries) = std::fs::read_dir(directory) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, into);
            } else if path.extension().is_some_and(|extension| extension == "lean")
                && let Ok(source) = std::fs::read_to_string(&path)
            {
                into.extend(declared_names(&source));
            }
        }
    }
    let mut names = BTreeSet::new();
    walk(&lean_root(), &mut names);
    assert!(
        names.len() > 500,
        "the formalization scan read almost nothing under {}",
        lean_root().display()
    );
    names
}

fn read_lean(relative: &str) -> String {
    let path = lean_root().join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "the Lean owner {} is absent, so the citation check cannot be taken and this test \
             refuses to report success without taking it: {error}",
            path.display()
        )
    })
}

/// **Every Lean name a wave-4 owner's correspondence table cites is declared by that owner.**
///
/// A stale citation fails here rather than waiting for a review. The check is not vacuous: the
/// number of names actually looked up is asserted to be large, and the Lean owner is read from
/// disk with a failure naming the path if it is absent.
#[test]
fn every_correspondence_table_cites_a_declared_lean_name() {
    let everywhere = every_declared_name();
    let mut checked = 0usize;
    for (header, name, lean) in paired_owners() {
        let owner = read_lean(lean);
        let declared = declared_names(&owner);
        assert!(
            declared.len() > 4,
            "{lean} declares almost nothing; the scan did not read it"
        );
        let cited = cited_in_table(header);
        for citation in &cited {
            // A table row may cite a name another owner declares — `Transition.ofEquiv` lives in
            // `ContinuingTower.lean` and `ReceiverCodeCost.serial_boundary_balance` in its own
            // file — so a name the module's own owner does not declare is looked for across the
            // whole formalization before it is called stale.
            assert!(
                declares(&declared, citation)
                    || declares(&everywhere, citation)
                    || MATHLIB_NAMES.contains(&citation.as_str()),
                "{name} cites Lean declaration `{citation}`, which neither {lean} nor any other \
                 file of the formalization declares"
            );
        }
        checked += cited.len();
    }
    assert!(
        checked > 150,
        "only {checked} table citations were checked; the table scan is not reading the headers"
    );
}

/// **Every inline `Foundation/…lean::Name` citation in the engine's sources names a declaration.**
///
/// This is the scan that catches a citation outside a correspondence table — the form most of this
/// library's prose uses.
#[test]
fn every_inline_lean_citation_names_a_declared_lean_name() {
    let root = repository_root().join("crates/holonic-engine/src");
    let mut sources = Vec::new();
    collect_rust_sources(&root, &mut sources);
    assert!(
        sources.len() > 20,
        "only {} engine sources were found under {}",
        sources.len(),
        root.display()
    );

    let mut cache: std::collections::BTreeMap<String, Option<BTreeSet<String>>> =
        std::collections::BTreeMap::new();
    let mut checked = 0usize;
    let mut unresolved: Vec<String> = Vec::new();
    for path in &sources {
        // These directories belong to another session's in-flight work.
        let display = path.display().to_string();
        if display.contains("/native_ecology/")
            || display.contains("/resident_section/")
            || display.contains("/cuda_")
        {
            continue;
        }
        let source = std::fs::read_to_string(path).expect("an engine source reads");
        for (file, name) in inline_citations(&source) {
            let declared = cache.entry(file.clone()).or_insert_with(|| {
                std::fs::read_to_string(lean_root().join(&file))
                    .ok()
                    .map(|owner| declared_names(&owner))
            });
            let Some(declared) = declared.as_ref() else {
                unresolved.push(format!("{display} cites {file}, which this repository does not carry"));
                continue;
            };
            if !declares(declared, &name) {
                unresolved.push(format!("{display} cites `{file}::{name}`, which {file} does not declare"));
            }
            checked += 1;
        }
    }
    assert!(
        checked > 100,
        "only {checked} inline citations were checked; the scan is not reading the sources"
    );
    assert!(
        unresolved.is_empty(),
        "stale Lean citations:\n{}",
        unresolved.join("\n")
    );
}

fn collect_rust_sources(directory: &Path, into: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rust_sources(&path, into);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            into.push(path);
        }
    }
}

/// Every `Foundation/<File>.lean::<Name>` or `Transport/<File>.lean::<Name>` citation in a source.
fn inline_citations(source: &str) -> Vec<(String, String)> {
    let mut found = Vec::new();
    for prefix in ["Foundation/", "Transport/", "Physics/"] {
        let mut rest = source;
        while let Some(at) = rest.find(prefix) {
            let tail = &rest[at..];
            rest = &rest[at + prefix.len()..];
            let Some(marker) = tail.find(".lean::") else {
                continue;
            };
            let file = &tail[..marker + ".lean".len()];
            if file.contains(' ') || file.contains('`') || file.contains('\n') {
                continue;
            }
            let after = &tail[marker + ".lean::".len()..];
            let name: String = after
                .chars()
                .take_while(|character| {
                    character.is_alphanumeric()
                        || *character == '_'
                        || *character == '.'
                        || *character == '\''
                })
                .collect();
            let name = name.trim_end_matches('.').to_owned();
            if is_identifier(&name) {
                found.push((file.to_owned(), name));
            }
        }
    }
    found
}
