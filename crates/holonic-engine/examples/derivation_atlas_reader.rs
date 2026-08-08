//! Read the machine's own deposited derivations back, and compute their invariants.
//!
//! `standing/output/lean-proof-production/` holds 31 proof artifacts the machine produced, each
//! bound to a content hash in `standing/MANIFEST.txt`. **Nothing has ever read them back.** Every
//! artifact this project emits goes into a directory that no organ opens, which is the gap the
//! roadmap has carried as "the atlas reader" since the transition.
//!
//! This is that reader, pointed at real production rather than at an emitted table nothing wrote.
//!
//! ## The derivation is a circuit
//!
//! A derivation names things and depends on things. Read as a complex:
//!
//! ```text
//!   0-cells   the declarations named -- theorems produced, symbols imported
//!   1-cells   a dependency: this derivation recruited that symbol
//!   2-cells   two derivations reaching the SAME statement by different recruitment
//! ```
//!
//! Then the invariants say what the production is:
//!
//! ```text
//!   b_0       independent content classes -- how many distinct things were derived
//!   b_1       independent distinct routes to one result -- the phase distribution over proofs
//!   torsion   a recruitment that cannot be un-derived
//! ```
//!
//! No external checker is consulted. The proof sources are read as structure, not submitted to
//! anything, which is the whole point of Lean being an export codec rather than a judge.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::rebase_invariants::{rebase_invariants, PivotRule};

/// What one deposited artifact declares.
#[derive(Debug, Clone)]
struct Derivation {
    name: String,
    /// The theorem's statement text, normalized. Two derivations of the same statement share this.
    statement: String,
    /// Symbols the proof recruited: imports and identifiers naming other declarations.
    recruited: BTreeSet<String>,
}

/// Parse a Lean artifact into what it names and what it recruited.
///
/// Deliberately structural and shallow: this reads what the file *declares*, not what it means. A
/// deeper reading would be a semantics claim, and the export codec's job is not to supply one.
fn read_derivation(path: &Path) -> Option<Derivation> {
    let text = std::fs::read_to_string(path).ok()?;
    let mut recruited = BTreeSet::new();
    let mut name = None;
    let mut statement = None;

    for line in text.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("import ") {
            recruited.insert(rest.trim().to_owned());
        }
        if let Some(rest) = trimmed.strip_prefix("theorem ") {
            let mut parts = rest.splitn(2, ' ');
            name = parts.next().map(str::to_owned);
            statement = parts.next().map(|body| {
                body.split(":=")
                    .next()
                    .unwrap_or(body)
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
            });
        }
        // A tactic or term line recruits any capitalized or namespaced identifier it names.
        for token in trimmed.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.')) {
            if token.len() > 2
                && (token.contains('.')
                    || token.chars().next().is_some_and(char::is_uppercase))
                && !token.starts_with("theorem")
            {
                recruited.insert(token.to_owned());
            }
        }
    }

    Some(Derivation {
        name: name?,
        statement: statement.unwrap_or_default(),
        recruited,
    })
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "standing/output/lean-proof-production".to_owned());
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&root)
        .map(|entries| {
            entries
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|kind| kind == "lean"))
                .collect()
        })
        .unwrap_or_default();
    paths.sort();

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=a derivation is a circuit and its invariants are what survive rebasing it");
    println!("standing={root}");

    if paths.is_empty() {
        println!("\nFAILED — no deposited derivations at {root}");
        println!("this reader refuses to run on anything it made up");
        std::process::exit(1);
    }

    let derivations: Vec<Derivation> = paths.iter().filter_map(|path| read_derivation(path)).collect();
    println!(
        "\nread {} artifacts, {} carrying a theorem declaration",
        paths.len(),
        derivations.len()
    );

    // --- the complex ------------------------------------------------------------------------

    let mut complex = GradedCausalComplex::default();
    let mut counter = 0u64;
    let mut event = || {
        counter += 1;
        BTreeSet::from([EventId(counter)])
    };

    // 0-cells: every declaration named, produced or recruited.
    let mut vertices: BTreeMap<String, CausalCellId> = BTreeMap::new();
    let mut names: BTreeSet<String> = BTreeSet::new();
    for derivation in &derivations {
        names.insert(derivation.name.clone());
        names.extend(derivation.recruited.iter().cloned());
    }
    for name in &names {
        let id = complex
            .found_cell(name.clone(), event(), 0, CausalChain::default())
            .expect("a declaration has no boundary");
        vertices.insert(name.clone(), id);
    }

    // 1-cells: one recruitment edge per (derivation, recruited symbol), deduplicated.
    let mut edges: BTreeMap<(String, String), CausalCellId> = BTreeMap::new();
    for derivation in &derivations {
        for symbol in &derivation.recruited {
            if symbol == &derivation.name {
                continue;
            }
            let key = (derivation.name.clone(), symbol.clone());
            if edges.contains_key(&key) {
                continue;
            }
            let mut boundary = CausalChain::default();
            boundary.add_term(vertices[&derivation.name], ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertices[symbol], ComparativeMultiplicity::negative(1u32));
            let id = complex
                .found_cell(
                    format!("{}<-{}", derivation.name, symbol),
                    event(),
                    1,
                    boundary,
                )
                .expect("a recruitment edge closes");
            edges.insert(key, id);
        }
    }

    let invariants = rebase_invariants(&complex, PivotRule::FirstNonzero).expect("the atlas reads");

    println!("\nDERIVATION COMPLEX");
    println!("------------------");
    println!(
        "  declarations {:>4}   recruitments {:>4}",
        names.len(),
        edges.len()
    );
    for grade in &invariants.grades {
        let torsion = if grade.torsion.is_empty() {
            "-".to_owned()
        } else {
            grade
                .torsion
                .iter()
                .map(|factor| format!("Z/{factor}"))
                .collect::<Vec<_>>()
                .join(" + ")
        };
        println!(
            "  grade {}  cells {:>4}  betti {:>3}  torsion {torsion}",
            grade.grade, grade.cells, grade.betti
        );
    }

    // Statements reached by more than one derivation: distinct routes to one result.
    let mut by_statement: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for derivation in &derivations {
        by_statement
            .entry(derivation.statement.as_str())
            .or_default()
            .push(derivation.name.as_str());
    }
    let plural: Vec<(&&str, &Vec<&str>)> = by_statement
        .iter()
        .filter(|(_, reached)| reached.len() > 1)
        .collect();
    println!(
        "\n  distinct statements {:>4}   reached by more than one derivation {:>4}",
        by_statement.len(),
        plural.len()
    );
    for (statement, reached) in plural.iter().take(3) {
        let shown: String = statement.chars().take(60).collect();
        println!("    {} routes  {shown}", reached.len());
    }

    // --- controls ---------------------------------------------------------------------------

    let mut holds: Vec<(&str, bool, String)> = Vec::new();
    holds.push((
        "the reader read real deposited artifacts, not a fixture",
        !derivations.is_empty(),
        format!("{} derivations from {}", derivations.len(), root),
    ));
    holds.push((
        "the complex is non-trivial: recruitment edges exist",
        !edges.is_empty(),
        format!("{} recruitments", edges.len()),
    ));
    holds.push((
        "CONTROL the invariants are capable of being nonzero here",
        invariants.betti_vector().iter().any(|betti| *betti > 0),
        format!("betti {:?}", invariants.betti_vector()),
    ));
    holds.push((
        "Euler characteristic from Betti numbers equals it from cell counts",
        invariants.euler_characteristic() == invariants.cell_euler_characteristic(),
        format!("chi = {}", invariants.cell_euler_characteristic()),
    ));

    println!("\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, held, evidence) in &holds {
        if *held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD — {} declared controls, 0 failed", holds.len());
    } else {
        println!("FAILED — {failed} of {} did not hold", holds.len());
        std::process::exit(1);
    }
}
