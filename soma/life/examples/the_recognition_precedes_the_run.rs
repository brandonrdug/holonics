//! Admissibility decided from `(D, v)` **before** the kernel runs, and graded by what it then says.
//!
//! Fourth movement of `blueprint/THE_TYPED_TRANSPORT_ATLAS.md`, and the plan's experiment. Two arms
//! on one corpus, one theorem, one kernel:
//!
//! - **the inherited arm** — every family offered to every organ, arguments by name intersection.
//!   Known: 213 paths, 105 rewrites by a non-equation, 42 application type mismatches, 4 admitted.
//! - **the typed arm** — `rw` offered only where `v` is an equality or an iff, and the application
//!   built in the recruited declaration's own frame, position by position, with `_` where the goal
//!   supplies no binder of that name.
//!
//! # The grading, which is `elementary_chart`'s and not a new one
//!
//! ```text
//!   OpenedAndFound     the types admitted the edge and the kernel proved it   -> AN ATLAS EDGE
//!   OpenedAndRefused   the types admitted it, the kernel refused on the MATHEMATICS
//!                                                                             -> a real obstruction
//!   Contradicted       the types admitted it and the kernel refused it STRUCTURALLY
//!                                                                             -> THE MODEL IS WRONG
//! ```
//!
//! **`Contradicted` must be empty**, and every member that is not names the component read wrong.
//! That is what makes the recognition falsifiable rather than decorative.
//!
//! A fourth outcome is reported separately and folded into neither: a typed application whose `_`
//! Lean could not synthesise. That is a consequence of the placeholder choice rather than of `(D,
//! v)`, and burying it in either arm would flatter the result.
//!
//! # The four predictions, declared before the run
//!
//! 1. The typed arm's structural refusals are **zero**.
//! 2. The typed arm admits **everything the inherited arm admitted**. Typing removes malformed
//!    paths; it may not remove a working one.
//! 3. The typed arm emits far fewer paths and admits at least as many. Reported as a pair.
//! 4. The typed arm's surviving refusals are **mathematical** — the atlas's genuine obstructions.
//!
//! **What refutes the design:** the typed arm admitting nothing the inherited arm did not, with
//! refusals of the same species. Then the typing changed nothing and the node model is decoration.
//!
//! ```text
//! cargo run --release -p life --example the_recognition_precedes_the_run
//! ```

use std::collections::BTreeSet;
use std::path::PathBuf;

use life::lean_mathematics::{
    EmissionGrain, LeanKernelWorld, LeanMathematicsEcology, LeanProofProblem, LeanSourceDocument,
};

const PROJECT: &str = "soma/formal/rh-source-transport";
const CORPUS: &str = "SomaRHSourceTransport/FiniteTransport.lean";

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "receiver_load_under_capacity".to_owned(),
        source_scope: BTreeSet::from(["FiniteTransport.lean".to_owned()]),
        prefix: r#"import SomaRHSourceTransport.FiniteTransport
namespace Soma.RHSourceTransport
variable {Old New : Type*}
variable [Fintype Old] [Fintype New]
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop) [DecidableRel incident]"#
            .to_owned(),
        theorem_header: r#"theorem receiver_load_under_capacity
    (hc : ∀ m, 0 ≤ capacity m) (hcong : ∀ m, congestion demand capacity incident m ≤ 1) (m : New) :
    (∑ n : Old, proportionalFlow demand capacity incident n m) ≤ capacity m"#
            .to_owned(),
        suffix: "end Soma.RHSourceTransport".to_owned(),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Outcome {
    Admitted,
    /// The kernel refused because the term was ill-formed: a rewrite by a non-relation, an
    /// application whose arguments do not fit. **This is `Contradicted` at the typed grain.**
    Structural,
    /// The kernel read the term and refused it on the mathematics.
    Mathematical,
    /// A typed application's `_` could not be synthesised. Reported apart from both.
    Placeholder,
}

fn outcome_of(admitted: bool, diagnostic: &str) -> Outcome {
    if admitted {
        return Outcome::Admitted;
    }
    if diagnostic.contains("don't know how to synthesize")
        || diagnostic.contains("Don't know how to synthesize")
    {
        return Outcome::Placeholder;
    }
    let structural = [
        "Invalid rewrite argument",
        "Application type mismatch",
        "function expected",
        "unknown identifier",
        "unknown constant",
        "unknown module prefix",
    ];
    if structural.iter().any(|marker| diagnostic.contains(marker)) {
        return Outcome::Structural;
    }
    Outcome::Mathematical
}

struct Edge {
    from: String,
    species: &'static str,
    proof: String,
}

/// `H.0362` names the edge species. The tactic that realises an edge decides which it is, and two
/// of the family are not edges at all: a closer reads an ordering or a normal form and carries no
/// node to another, which is a **face**.
fn edge_species(proof: &str) -> &'static str {
    let head = proof
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty() && *line != "by")
        .unwrap_or("");
    if head.starts_with("rw ") {
        "substitution (carries a Jacobian; demands v = or ↔)"
    } else if head.starts_with("simpa") {
        "substitution composed with an exterior normalisation"
    } else if head.starts_with("exact ") || head.starts_with("apply ") {
        "conjugacy — the node applied in its own frame"
    } else if head.starts_with("have ") {
        "deposit then close — an introduced fact, then a face"
    } else {
        "face — reads an ordering or a normal form, carries no node"
    }
}

struct Arm {
    emitted: usize,
    admitted: BTreeSet<String>,
    edges: Vec<Edge>,
    structural: usize,
    mathematical: usize,
    placeholder: usize,
    structural_examples: Vec<String>,
}

fn main() {
    let root = repository_root();
    let project = root.join(PROJECT);
    let scratch = root.join("output/the-recognition-precedes-the-run");
    println!("THE RECOGNITION PRECEDES THE RUN — two arms, one corpus, one kernel");
    if !project.join(".lake/packages/mathlib").exists() {
        println!("  mathlib is not materialised; the experiment cannot run.");
        println!("  recover it with:  cd soma/formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }
    let text = std::fs::read_to_string(project.join(CORPUS)).expect("the corpus reads");
    let corpus = vec![LeanSourceDocument::new("FiniteTransport.lean", &text)];
    let ecology = LeanMathematicsEcology::condition(&corpus).expect("the corpus conditions");
    println!("\n  what the node says of each recruited declaration:");
    for organ in ecology.declarations() {
        println!(
            "    {:42} v = {:3}  rewritable {:5}  positional domain {}",
            organ.name,
            organ.relation_label(),
            organ.rewritable(),
            organ
                .binders
                .iter()
                .filter(|binder| binder.kind.is_positional())
                .count()
        );
    }

    let posed = problem();
    let kernel = LeanKernelWorld::new(&project, &scratch, 8).expect("the kernel mounts");
    let mut arms = Vec::new();
    for (label, grain) in [
        ("inherited", EmissionGrain::Inherited),
        ("typed", EmissionGrain::Typed),
    ] {
        let (_, candidates) = ecology
            .generate_proof_candidates_at(&posed, grain)
            .expect("the corpus composes a path family");
        let returns = kernel
            .grade_all(&posed, &candidates)
            .expect("every path receives a verdict");
        let mut arm = Arm {
            emitted: candidates.len(),
            admitted: BTreeSet::new(),
            edges: Vec::new(),
            structural: 0,
            mathematical: 0,
            placeholder: 0,
            structural_examples: Vec::new(),
        };
        for returned in returns.members() {
            match outcome_of(returned.kernel_admitted(), returned.diagnostic()) {
                Outcome::Admitted => {
                    arm.admitted.insert(returned.candidate().proof.clone());
                    arm.edges.push(Edge {
                        from: returned
                            .candidate()
                            .declaration_lineage
                            .iter()
                            .map(|name| name.to_string())
                            .collect::<Vec<_>>()
                            .join(" + "),
                        species: edge_species(&returned.candidate().proof),
                        proof: returned.candidate().proof.replace('\n', " "),
                    });
                }
                Outcome::Structural => {
                    arm.structural += 1;
                    if arm.structural_examples.len() < 6 {
                        // **The proof text, not only the diagnostic head.** A `Contradicted` is
                        // complete only when it names the node component that was read wrong, and
                        // the head alone cannot: two paths refused identically may be refused for
                        // different reasons.
                        let head = returned
                            .diagnostic()
                            .lines()
                            .find(|line| line.contains("error:"))
                            .map(|line| {
                                let at = line.find("error:").unwrap_or(0);
                                line[at..].chars().take(64).collect::<String>()
                            })
                            .unwrap_or_default();
                        arm.structural_examples.push(format!(
                            "{}   <-   {head}",
                            returned.candidate().proof.replace('\n', " ")
                        ));
                    }
                }
                Outcome::Mathematical => arm.mathematical += 1,
                Outcome::Placeholder => arm.placeholder += 1,
            }
        }
        println!(
            "\n  {label:10} emitted {:4}   admitted {:3}   structural {:4}   mathematical {:4}   placeholder {:4}",
            arm.emitted,
            arm.admitted.len(),
            arm.structural,
            arm.mathematical,
            arm.placeholder
        );
        for example in &arm.structural_examples {
            println!("      structural: {example}");
        }
        arms.push(arm);
    }

    let inherited = &arms[0];
    let typed = &arms[1];
    println!("\n=== the four predictions, declared before the run");
    let mut failures: Vec<&str> = Vec::new();
    let require = |held: bool, claim: &'static str, failures: &mut Vec<&'static str>| {
        println!("  [{}] {claim}", if held { "holds" } else { "FAILS" });
        if !held {
            failures.push(claim);
        }
    };
    require(
        typed.structural == 0,
        "the typed arm's structural refusals are zero — Contradicted is empty",
        &mut failures,
    );
    let kept: Vec<&String> = inherited
        .admitted
        .iter()
        .filter(|proof| !typed.admitted.contains(*proof))
        .collect();
    require(
        kept.is_empty(),
        "the typed arm admits everything the inherited arm admitted",
        &mut failures,
    );
    for proof in kept.iter().take(3) {
        println!("      LOST: {}", proof.replace('\n', " "));
    }
    require(
        typed.emitted < inherited.emitted && typed.admitted.len() >= inherited.admitted.len(),
        "the typed arm emits fewer and admits at least as many",
        &mut failures,
    );
    println!(
        "      emitted {} -> {}   admitted {} -> {}",
        inherited.emitted,
        typed.emitted,
        inherited.admitted.len(),
        typed.admitted.len()
    );
    require(
        typed.mathematical > 0,
        "the typed arm's surviving refusals are mathematical — the atlas's obstructions",
        &mut failures,
    );

    println!("\n=== the refutation condition");
    let gained = typed
        .admitted
        .iter()
        .filter(|proof| !inherited.admitted.contains(*proof))
        .count();
    println!(
        "  the typed arm admits {gained} path(s) the inherited arm did not, and removed {} \
         structural refusal(s)",
        inherited.structural as i64 - typed.structural as i64
    );
    if gained == 0 && typed.structural == inherited.structural {
        println!("  REFUTED — the typing changed nothing and the node model is decoration.");
        std::process::exit(1);
    }
    println!(
        "  Not refuted: the typing moved the structural population, which is what `(D, v)` is for."
    );

    // ---------------------------------------------------------------- the atlas, as a graph
    println!("\n=== THE ADMITTED PATH IS AN EDGE — the atlas stops being a partition");
    println!(
        "  target node: `{}`   v = ≤   positional domain 6",
        posed.identity
    );
    println!("  every edge below is a KERNEL-PROVED transformation carrying a node to that node");
    println!("  while preserving its invariant, which is `H.0362`'s definition of an atlas edge.");
    for edge in &typed.edges {
        println!("\n    from   {}", if edge.from.is_empty() { "(none recruited)" } else { &edge.from });
        println!("    species {}", edge.species);
        println!("    proof   {}", edge.proof);
    }
    println!(
        "\n  {} edge(s). The species partition is retained as a coarsening over NODES and is no",
        typed.edges.len()
    );
    println!("  longer named as the atlas row — shared output does not supply an edge.");

    if failures.is_empty() {
        println!("\n  every declared prediction holds.");
    } else {
        println!("\n  FAILED PREDICTIONS:");
        for failure in &failures {
            println!("    {failure}");
        }
        std::process::exit(1);
    }
}
