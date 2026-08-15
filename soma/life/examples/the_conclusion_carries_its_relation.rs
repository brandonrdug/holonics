//! `v`, the denoted invariant — and the kernel adjudicates it.
//!
//! Second movement of `blueprint/THE_TYPED_TRANSPORT_ATLAS.md`. `H.0362` names `v` as a formulation
//! node's denoted invariant; until now `LeanDeclarationOrgan` carried none, and
//! `result_constructors` walked the conclusion at depth zero while matching exactly one character.
//! The emission therefore offered `rw [d]` for every recruited declaration whatever it concluded.
//!
//! `LeanDeclarationOrgan::conclusion_relation` is that component, and
//! `LeanDeclarationOrgan::rewritable` is the one decision it licenses: **`rw` demands an equality or
//! an iff**, which is what Lean says when it refuses.
//!
//! # The falsifier, and it is the kernel rather than an assertion
//!
//! A conclusion this reader calls an equality that the kernel then refuses to rewrite by is a
//! misread `v`. So every declaration of the declared corpus is submitted as an actual `rw [d]`, and
//! the reader's prediction is graded against what Lean says:
//!
//! ```text
//!   predicted rewritable   AND   kernel did not say "Invalid rewrite argument"   -> agrees
//!   predicted rewritable   AND   the kernel said exactly that                    -> MISREAD v
//!   predicted not          AND   the kernel said exactly that                    -> agrees
//!   predicted not          AND   the kernel did not                              -> MISSED an edge
//! ```
//!
//! Both disagreement arms are real and both are reported. `None` — a conclusion exposing no single
//! depth-zero relation — is **not rewritable**: a reader that cannot see what a declaration concludes
//! may not license a transport by it.
//!
//! ```text
//! cargo run --release -p life --example the_conclusion_carries_its_relation
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use life::lean_mathematics::{LeanMathematicsEcology, LeanSourceDocument};

const PROJECT: &str = "soma/formal/rh-source-transport";
const CORPUS: &str = "SomaRHSourceTransport/FiniteTransport.lean";
const LIBRARY: &str = "soma/formal/elementary-holonics/.lake/packages/mathlib/Mathlib";

/// The preamble a probe is posed in — the corpus's own section variables.
const PREAMBLE: &str = r#"import SomaRHSourceTransport.FiniteTransport
namespace Soma.RHSourceTransport
variable {Old New : Type*}
variable [Fintype Old] [Fintype New]
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop) [DecidableRel incident]"#;

struct Failures(Vec<String>);

impl Failures {
    fn require(&mut self, held: bool, claim: &str) {
        println!("  [{}] {claim}", if held { "holds" } else { "FAILS" });
        if !held {
            self.0.push(claim.to_owned());
        }
    }
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn lean_files(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(directory) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|kind| kind == "lean") {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

fn main() {
    let mut failures = Failures(Vec::new());
    let root = repository_root();
    let project = root.join(PROJECT);
    println!("THE CONCLUSION CARRIES ITS RELATION — v, and the kernel adjudicates it");

    // ---------------------------------------------------------------- the declared corpus
    let corpus_path = project.join(CORPUS);
    let Ok(text) = std::fs::read_to_string(&corpus_path) else {
        println!("  the corpus is absent: {}", corpus_path.display());
        std::process::exit(2);
    };
    let corpus = vec![LeanSourceDocument::new("FiniteTransport.lean", &text)];
    let ecology = LeanMathematicsEcology::condition(&corpus).expect("the corpus conditions");
    let organs: Vec<_> = ecology.declarations().cloned().collect();
    println!("\n=== what the reader now says each declaration concludes");
    for organ in &organs {
        println!(
            "  {:44} {:3}   rewritable {}",
            organ.name,
            organ.relation_label(),
            organ.rewritable()
        );
    }

    // ---------------------------------------------------------------- the kernel adjudicates
    println!("\n=== the kernel adjudicates every one, by being asked to rewrite by it");
    let scratch = root.join("output/the-conclusion-carries-its-relation");
    std::fs::create_dir_all(&scratch).expect("the scratch root is writable");
    let mut misread = Vec::new();
    let mut missed = Vec::new();
    if !project.join(".lake/packages/mathlib").exists() {
        println!("  mathlib is not materialised; the adjudication cannot run.");
        println!("  recover it with:  cd soma/formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }
    for organ in &organs {
        let source = format!(
            "{PREAMBLE}\n\ntheorem probe_{name} : True := by\n  rw [{name}]\n  trivial\n\nend Soma.RHSourceTransport\n",
            name = organ.name
        );
        let path = scratch.join(format!("rewrite-by-{}.lean", organ.name));
        std::fs::write(&path, &source).expect("the probe writes");
        let output = Command::new("lake")
            .arg("env")
            .arg("lean")
            .arg(&path)
            .current_dir(&project)
            .output()
            .expect("lake env lean runs");
        let mut said = String::from_utf8_lossy(&output.stdout).into_owned();
        said.push_str(&String::from_utf8_lossy(&output.stderr));
        // The kernel's own words for "this is not a rewritable relation".
        let refused_as_relation = said.contains("Expected an equality or iff proof");
        let agrees = organ.rewritable() != refused_as_relation;
        println!(
            "  {:44} predicted {:14}  kernel {:14}  {}",
            organ.name,
            if organ.rewritable() { "rewritable" } else { "not rewritable" },
            if refused_as_relation { "not rewritable" } else { "rewritable" },
            if agrees { "agrees" } else { "DISAGREES" }
        );
        if !agrees {
            if organ.rewritable() {
                misread.push(organ.name.clone());
            } else {
                missed.push(organ.name.clone());
            }
        }
    }
    failures.require(
        misread.is_empty(),
        "no conclusion this reader calls an equality is refused as a rewrite — v is not misread",
    );
    for name in &misread {
        println!("      MISREAD v: {name}");
    }
    if !missed.is_empty() {
        println!(
            "\n  MISSED EDGES — the kernel accepted a rewrite this reader would not have offered:"
        );
        for name in &missed {
            println!("      {name}");
        }
        println!(
            "  This is the other disagreement arm. It costs coverage rather than correctness, and it"
        );
        println!("  is reported rather than folded into the pass above.");
    }

    // ---------------------------------------------------------------- the library census
    println!("\n=== the census over the library — what `v` is, and how often it cannot be read");
    let library = root.join(LIBRARY);
    if !library.exists() {
        println!("  the library is absent; the census is skipped");
    } else {
        let paths = lean_files(&library);
        let mut documents = Vec::with_capacity(paths.len());
        for path in &paths {
            if let Ok(text) = std::fs::read_to_string(path) {
                let name = path
                    .strip_prefix(&library)
                    .unwrap_or(path)
                    .to_string_lossy()
                    .into_owned();
                documents.push(LeanSourceDocument::new(&name, &text));
            }
        }
        println!("  documents {}", documents.len());
        // **Conditioning the library whole returns a hard parse refusal**: one declaration the
        // reader cannot name aborts everything. That is a property of the emission's reader worth
        // measuring rather than routing around, so the census runs per document and the refused
        // population is counted and named.
        let mut census: BTreeMap<String, usize> = BTreeMap::new();
        let mut rewritable = 0usize;
        let mut total = 0usize;
        let mut refused: Vec<String> = Vec::new();
        for document in &documents {
            match LeanMathematicsEcology::condition(std::slice::from_ref(document)) {
                Ok(one) => {
                    for organ in one.declarations() {
                        total += 1;
                        *census
                            .entry(organ.relation_label().to_owned())
                            .or_insert(0) += 1;
                        if organ.rewritable() {
                            rewritable += 1;
                        }
                    }
                }
                Err(_) => refused.push(document.path.clone()),
            }
        }
        println!(
            "  documents the reader could open {}   REFUSED {}",
            documents.len() - refused.len(),
            refused.len()
        );
        for path in refused.iter().take(4) {
            println!("      refused {path}");
        }
        {
                let mut rows: Vec<(&String, &usize)> = census.iter().collect();
                rows.sort_by(|left, right| right.1.cmp(left.1));
                println!("  declarations opened {total}");
                for (relation, count) in rows {
                    let label = if relation == "?" {
                        "?  — no single depth-zero relation, UNCLASSIFIED"
                    } else {
                        relation.as_str()
                    };
                    println!("    {label:48} {count:>8}");
                }
                println!("\n  rewritable — the population `rw` may be offered for: {rewritable} of {total}");
                println!(
                    "  The UNCLASSIFIED population is the honest half of this reading: the reader"
                );
                println!(
                    "  does not guess a principal connective it cannot see, and it is counted rather"
                );
                println!("  than defaulted into either arm.");
            failures.require(
                total > 0 && census.contains_key("="),
                "the library census returns a population and an equality species within it",
            );
        }
    }

    println!();
    if failures.0.is_empty() {
        println!("  every declared control holds.");
    } else {
        println!("  FAILED CONTROLS:");
        for failure in &failures.0 {
            println!("    {failure}");
        }
        std::process::exit(1);
    }
}
