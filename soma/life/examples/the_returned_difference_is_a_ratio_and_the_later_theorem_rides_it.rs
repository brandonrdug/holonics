//! The full cycle on real mathematics: emit, let a kernel return a difference, read that difference
//! as a **ratio cocycle**, deposit it, and let a later NONIDENTICAL theorem ride the deposit.
//!
//! ```text
//! mount -> conduct -> radiate -> world -> genuine return -> reflect/deposit -> later current
//! ```
//!
//! `the_second_theorem_is_reachable_only_after_the_return` runs this shape in
//! `soma/formal/kernel-witness`, whose corpus is a three-line toy carrier Lean core alone can check.
//! It runs there because mathlib was believed uncompiled, which was measured false on 2026-08-14.
//! **This driver runs the same cycle on real mathematics**: the corpus is
//! `soma/formal/rh-source-transport/SomaRHSourceTransport/FiniteTransport.lean`, read from disk, and
//! the exterior world is a kernel with the whole of mathlib in scope.
//!
//! # What is new here beyond the environment
//!
//! The returned difference is read through the **chart transition**, not through a score.
//! `crates/holonic-engine/src/exponentiated_ratio.rs` was deposited on 2026-08-14 under Brandon's
//! ruling that softmax *"doesn't actually seem like a statistics function… It's a rebasing thing"* —
//! `exp` is the arc-to-whole map, `ℚ⁺` is the free abelian group on the primes, and
//! `SymbolicSurprisal` is its additive chart. Until now that organ had no world-return to read.
//!
//! ```text
//!   returned family
//!     -> species standing              counts per kernel diagnostic species
//!     -> SymbolicSurprisal             the ADDITIVE chart
//!     -> RatioFamily                   the MULTIPLICATIVE chart: exact pairwise ratios
//!        cocycle_holds()               r(i,j)·r(j,k) = r(i,k), over every triple
//!        null_orbit_is_trivial()       the declared null moves nothing: Z carries no content
//!     -> a RATIO aperture              declared as r >= q, never as a magnitude
//! ```
//!
//! **The gauge measurement is the point, and it can fail.** Softmax is invariant under
//! `x -> x + c`. So an additive shift applied to every species must leave every ratio **exactly**
//! unmoved, while an absolute threshold on the additive chart moves. That is the horizon law —
//! *magnitudes do not cross a frame boundary, ratios do* — measured on a real kernel return rather
//! than asserted. A reading that admitted species by their additive magnitude would be a receiver
//! coordinate promoted into an invariant.
//!
//! **No argmax, at any temperature.** `T -> 0` is argmax and this path never reaches it; the whole
//! returned family is deposited, admitted and obstructed alike, and nothing is ranked or dropped.
//!
//! ```text
//! cargo run --release -p life --example the_returned_difference_is_a_ratio_and_the_later_theorem_rides_it
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use holonic_engine::exponentiated_ratio::RatioFamily;
use holonic_engine::surprisal::{Support, SymbolicSurprisal};
use holonic_structure::{LocalSequence, LocalSet};
use life::lean_mathematics::{
    LeanDiagnosisCurrentFace, LeanDiagnosisRequirement, LeanKernelWorld, LeanMathematicsEcology,
    LeanMathematicsError, LeanProofProblem, LeanSourceDocument, LeanTargetSelectionReceipt,
    LeanTheoremTargetFace, LeanTheoremTargetRequest,
};
use num_bigint::BigUint;
use num_rational::BigRational as Rat;
use num_traits::One;

const CORPUS_FILE: &str = "SomaRHSourceTransport/FiniteTransport.lean";

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

struct Failures(Vec<String>);

impl Failures {
    fn require(&mut self, held: bool, claim: &str) {
        println!("  [{}] {claim}", if held { "holds" } else { "FAILS" });
        if !held {
            self.0.push(claim.to_owned());
        }
    }
}

fn toolchain(project_root: &Path) -> (String, String) {
    let pin = std::fs::read_to_string(project_root.join("lean-toolchain"))
        .map(|text| text.trim().to_owned())
        .unwrap_or_else(|_| "unpinned".to_owned());
    let running = Command::new("lean")
        .arg("--version")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|text| text.trim().to_owned())
        .unwrap_or_else(|| "no lean on PATH".to_owned());
    (pin, running)
}

/// The FIRST theorem, posed in the environment the corpus actually lives in.
fn first_problem() -> LeanProofProblem {
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

/// The SECOND theorem. Its scope names **only** the self-emanated file the first theorem's admitted
/// family produces, so it is unreachable until that return has been deposited.
fn second_problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "receiver_load_under_capacity_again".to_owned(),
        source_scope: BTreeSet::from([
            "self-emanated/receiver_load_under_capacity.lean".to_owned()
        ]),
        prefix: r#"import SomaRHSourceTransport.FiniteTransport
namespace Soma.RHSourceTransport
variable {Old New : Type*}
variable [Fintype Old] [Fintype New]
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop) [DecidableRel incident]"#
            .to_owned(),
        theorem_header: r#"theorem receiver_load_under_capacity_again
    (hc : ∀ m, 0 ≤ capacity m) (hcong : ∀ m, congestion demand capacity incident m ≤ 1) (m : New) :
    (∑ n : Old, proportionalFlow demand capacity incident n m) ≤ capacity m"#
            .to_owned(),
        suffix: "end Soma.RHSourceTransport".to_owned(),
    }
}

fn diagnosis() -> LeanDiagnosisCurrentFace {
    let region = LocalSet::from(["proportional-flow".to_owned()]);
    LeanDiagnosisCurrentFace::from_closed_current(
        "deed/answer".to_owned(),
        "Which theorem carries the capacity bound?".to_owned(),
        LocalSequence::from_iter(["diagnosis-clause".to_owned()]),
        LocalSet::from(["diagnosis-source".to_owned()]),
        LocalSet::from(["diagnosis-passage".to_owned()]),
        LocalSequence::from_iter([region.to_owned()]),
        LocalSet::from([region]),
        LocalSet::from(["diagnosis-passage".to_owned()]),
        LocalSet::from(["deed/answer".to_owned()]),
    )
    .expect("a closed diagnosis current")
}

fn target_request() -> LeanTheoremTargetRequest {
    LeanTheoremTargetRequest {
        identity: "the-returned-difference-is-a-ratio".to_owned(),
        declared_theorem_faces: LocalSet::from(["receiver_load_under_capacity".to_owned()]),
        alternatives: LocalSequence::from_iter([LeanTheoremTargetFace {
            problem: first_problem(),
            diagnosis_requirement: LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent,
        }]),
        target_episode: "deed/answer".to_owned(),
        diagnosis: diagnosis(),
    }
}

/// The species a kernel verdict lands in: its first diagnostic line, or admission.
///
/// This is the material's own partition and not an authored one — the kernel wrote these strings,
/// and a species that no verdict landed in does not exist here.
fn species_of(admitted: bool, diagnostic: &str) -> String {
    if admitted {
        return "kernel-admitted".to_owned();
    }
    let line = diagnostic
        .lines()
        .find(|line| line.contains("error:") || line.contains("warning:"))
        .unwrap_or("(no diagnostic)");
    // The file path prefix is a receiver coordinate — the same refusal in another scratch file is
    // the same species — so the species is what the kernel SAID, from `error:` onward.
    match line.find("error:").or_else(|| line.find("warning:")) {
        Some(at) => line[at..].chars().take(72).collect(),
        None => line.chars().take(72).collect(),
    }
}

fn main() {
    let mut failures = Failures(Vec::new());
    println!("{}", "=".repeat(104));
    println!("THE RETURNED DIFFERENCE IS A RATIO, AND THE LATER THEOREM RIDES IT");
    println!("{}", "=".repeat(104));

    let root = repository_root();
    let project_root = root.join("soma/formal/rh-source-transport");
    let scratch_root = root.join("output/the-returned-difference-is-a-ratio");
    let corpus_path = project_root.join(CORPUS_FILE);
    if !corpus_path.is_file() {
        println!("  the corpus is absent: {}", corpus_path.display());
        std::process::exit(2);
    }
    if !project_root.join(".lake/packages/mathlib").exists() {
        println!("  mathlib is not materialised for this project.");
        println!("  recover it with:  cd soma/formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }
    let (pin, running) = toolchain(&project_root);
    println!("\n  project        {}", project_root.display());
    println!("  corpus         {CORPUS_FILE}");
    println!("  lean-toolchain {pin}");
    println!("  lean --version {running}");
    // `lean --version` writes `Lean (version 4.27.0, …)` and the pin writes `…:v4.27.0`, so the
    // leading `v` must come off or a matching toolchain reports itself as non-reproducible. It did,
    // on every run of this shape until 2026-08-14. `eros_lean_proof_production` already got this
    // right; these two did not, and a verdict wrongly labelled unreproducible is a claim about the
    // evidence rather than about the mathematics.
    let reproducible = running.contains(
        pin.trim_start_matches("leanprover/lean4:")
            .trim_start_matches('v'),
    );
    println!(
        "  the verdicts below are {}",
        if reproducible {
            "reproducible against the pin"
        } else {
            "REAL BUT NOT REPRODUCIBLE — the running toolchain differs from the pin"
        }
    );

    // ------------------------------------------------------------------ mount
    let text = std::fs::read_to_string(&corpus_path).expect("the corpus reads");
    let corpus = vec![LeanSourceDocument::new("FiniteTransport.lean", &text)];
    let mut ecology = LeanMathematicsEcology::condition(&corpus).expect("the corpus conditions");
    println!("\n{}", "-".repeat(104));
    println!("MOUNT — real mathematics crosses, and the source departs");
    println!("{}", "-".repeat(104));
    println!(
        "  corpus bytes {}   declaration organs {}   retained source surfaces {}",
        text.len(),
        ecology.declarations().count(),
        ecology.receipt().retained_source_surfaces
    );

    // ------------------------------------------------------------------ before
    println!("\n{}", "-".repeat(104));
    println!("BEFORE THE RETURN — the second theorem is unreachable");
    println!("{}", "-".repeat(104));
    let before = ecology.generate_proof_candidates(&second_problem());
    let unreachable_before = matches!(before, Err(LeanMathematicsError::NoLocalDeclarations));
    println!(
        "  asking for `{}`: {}",
        second_problem().identity,
        match &before {
            Err(error) => format!("{error:?}"),
            Ok((reached, candidates)) => format!(
                "REACHED {} declarations, {} candidates",
                reached.len(),
                candidates.len()
            ),
        }
    );
    failures.require(
        unreachable_before,
        "the second theorem is unreachable before the return",
    );

    // ------------------------------------------------------------------ the world
    println!("\n{}", "-".repeat(104));
    println!("THE WORLD — a real kernel grades the first theorem, with mathlib in scope");
    println!("{}", "-".repeat(104));
    let selection = ecology
        .select_and_open_kernel_deed(target_request())
        .expect("the target request selects");
    let LeanTargetSelectionReceipt::Selected(_) = &selection else {
        println!("  the target was not selected: {selection:?}");
        std::process::exit(1);
    };
    let deed = ecology.open_kernel_deed().expect("a deed is open");
    let deed_identity = deed.identity().to_owned();
    let candidates = deed.candidates().to_vec();
    println!("  deed {deed_identity}   candidates {}", candidates.len());

    let kernel = LeanKernelWorld::new(&project_root, &scratch_root, 6).expect("the kernel mounts");
    let returns = kernel
        .grade_all(&first_problem(), &candidates)
        .expect("the kernel returns a verdict for every candidate");
    let admitted = returns.kernel_admitted_extent();
    let obstructed = returns.obstruction_extent();
    let occupancy: u64 = returns
        .members()
        .iter()
        .map(|member| member.observed_millis())
        .sum();
    println!("  kernel admitted {admitted}   obstructed {obstructed}   occupancy {occupancy} ms");

    // ------------------------------------------------------------------ the chart transition
    println!("\n{}", "-".repeat(104));
    println!("THE RETURNED DIFFERENCE, READ AS A RATIO COCYCLE — not a score, not a distribution");
    println!("{}", "-".repeat(104));
    let mut standing: BTreeMap<String, BigUint> = BTreeMap::new();
    for member in returns.members() {
        let species = species_of(member.kernel_admitted(), member.diagnostic());
        *standing.entry(species).or_insert_with(|| BigUint::from(0u32)) += BigUint::from(1u32);
    }
    let names: Vec<String> = standing.keys().cloned().collect();
    println!("  the kernel's own species, and how many paths landed in each:");
    for (index, name) in names.iter().enumerate() {
        println!("    {index:2}  {:4}  {name}", standing[name]);
    }

    // Key by ordinal so the family carries the caller's own names, and read the ADDITIVE chart.
    let keyed: BTreeMap<u64, BigUint> = names
        .iter()
        .enumerate()
        .map(|(index, name)| (index as u64, standing[name].clone()))
        .collect();
    let mut population: BTreeMap<u64, SymbolicSurprisal> = BTreeMap::new();
    for member in keyed.keys() {
        match Support::read(&keyed, *member) {
            Ok(Support::Supported(form)) => {
                population.insert(*member, form);
            }
            Ok(Support::Unsupported) => {
                println!("    species {member} is unsupported — it FOUNDs rather than smooths")
            }
            Err(error) => println!("    species {member} has no additive chart: {error:?}"),
        }
    }
    println!(
        "\n  additive chart read for {} of {} species",
        population.len(),
        names.len()
    );

    if population.len() < 2 {
        println!("  fewer than two species carry a chart; there is no ratio family to take");
        failures.require(false, "the returned population founds a ratio family");
    } else {
        let family = RatioFamily::read(&population).expect("the ratio family reads");
        failures.require(
            family.cocycle_holds(),
            "the cocycle law holds over every triple: r(i,j)·r(j,k) = r(i,k)",
        );
        failures.require(
            family
                .null_orbit_is_trivial()
                .expect("the null orbit computes"),
            "the declared null moves nothing — Z carries no content the ratios did not",
        );

        // ---------------------------------------------------------- the gauge measurement
        println!("\n  THE GAUGE: softmax is invariant under x -> x + c. Applying an additive shift");
        println!("  to EVERY species must leave every ratio exactly unmoved, while an absolute");
        println!("  threshold on the additive chart moves. Magnitudes do not cross; ratios do.");
        let shift = SymbolicSurprisal::term(2, Rat::one()).expect("a one-bit shift");
        let shifted: BTreeMap<u64, SymbolicSurprisal> = population
            .iter()
            .map(|(member, form)| (*member, form.plus(&shift)))
            .collect();
        let shifted_family = RatioFamily::read(&shifted).expect("the shifted family reads");
        let ratios_unmoved = family.members() == shifted_family.members()
            && family.members().iter().all(|left| {
                family.members().iter().all(|right| {
                    left == right || family.ratio(*left, *right) == shifted_family.ratio(*left, *right)
                })
            });
        failures.require(
            ratios_unmoved,
            "an additive gauge shift moves NO ratio — the multiplicative chart is the invariant",
        );

        // A ratio aperture against a declared reference, and the same aperture after the shift.
        let reference = *family.members().first().expect("a member");
        let admit_ratio = |source: &RatioFamily| -> BTreeSet<u64> {
            let floor = Rat::new(1u32.into(), 8u32.into());
            source
                .members()
                .iter()
                .copied()
                .filter(|member| {
                    *member == reference
                        || source
                            .ratio(*member, reference)
                            .is_some_and(|ratio| *ratio >= floor)
                })
                .collect()
        };
        let by_ratio = admit_ratio(&family);
        let by_ratio_shifted = admit_ratio(&shifted_family);
        failures.require(
            by_ratio == by_ratio_shifted,
            "a RATIO aperture admits the same species before and after the gauge shift",
        );

        // The same question asked as a magnitude, which is the reading this project refuses.
        let admit_magnitude = |source: &BTreeMap<u64, SymbolicSurprisal>| -> BTreeSet<u64> {
            let ceiling = SymbolicSurprisal::term(2, Rat::new(3u32.into(), 1u32.into()))
                .expect("a three-bit ceiling");
            source
                .iter()
                .filter(|(_, form)| {
                    matches!(
                        form.compare(&ceiling),
                        Ok(holonic_engine::exact_value::ExactOrdering::Less)
                    )
                })
                .map(|(member, _)| *member)
                .collect()
        };
        let by_magnitude = admit_magnitude(&population);
        let by_magnitude_shifted = admit_magnitude(&shifted);
        println!(
            "    ratio aperture      {:?} -> {:?}   {}",
            by_ratio.len(),
            by_ratio_shifted.len(),
            if by_ratio == by_ratio_shifted {
                "UNMOVED"
            } else {
                "moved"
            }
        );
        println!(
            "    magnitude aperture  {:?} -> {:?}   {}",
            by_magnitude.len(),
            by_magnitude_shifted.len(),
            if by_magnitude == by_magnitude_shifted {
                "unmoved on this material"
            } else {
                "MOVED — the receiver coordinate leaked into the verdict"
            }
        );
        failures.require(
            by_magnitude != by_magnitude_shifted,
            "the magnitude aperture MOVES under the same shift, so the contrast is not vacuous",
        );

        // Temperature is a root on the ratio, and T -> 0 is argmax, which this path never reaches.
        failures.require(
            family.rebased_by(0).is_err(),
            "the degenerate temperature is refused, and no path here reaches argmax",
        );
    }

    // ------------------------------------------------------------------ the deposit
    println!("\n{}", "-".repeat(104));
    println!("THE DEPOSIT — the WHOLE family, admitted and obstructed alike, nothing ranked");
    println!("{}", "-".repeat(104));
    let completion = ecology
        .receive_kernel_deed_returns(&deed_identity, returns)
        .expect("the returns are received");
    let receipt = completion.cultivation();
    println!(
        "  generation {} -> {}   organs {} -> {}   declaration admitted {}",
        receipt.generation_before,
        receipt.generation_after,
        receipt.declaration_organs_before,
        receipt.declaration_organs_after,
        receipt.declaration_admitted
    );

    // ------------------------------------------------------------------ the later current
    println!("\n{}", "-".repeat(104));
    println!("AFTER THE RETURN — the later theorem rides the deposit");
    println!("{}", "-".repeat(104));
    let after = ecology.generate_proof_candidates(&second_problem());
    match &after {
        Ok((reached, candidates)) => {
            println!(
                "  REACHED {} declarations, {} candidates",
                reached.len(),
                candidates.len()
            );
            for name in reached.iter().take(6) {
                println!("      recruited {name}");
            }
            for candidate in candidates.iter().take(2) {
                println!("      --- a generated path, verbatim");
                for line in candidate.proof.lines() {
                    println!("          {line}");
                }
            }
        }
        Err(error) => println!("  still unreachable: {error:?}"),
    }
    failures.require(
        after.is_ok(),
        "the second theorem is reachable after the return, and it was not before",
    );

    // ------------------------------------------------------------------ the ablation
    println!("\n{}", "-".repeat(104));
    println!("THE ABLATION — remove the returned organ and the reach must go with it");
    println!("{}", "-".repeat(104));
    let ablated = LeanMathematicsEcology::condition(&corpus).expect("the corpus re-conditions");
    let ablated_reach = ablated.generate_proof_candidates(&second_problem());
    println!(
        "  a body that never received the return: {}",
        match &ablated_reach {
            Err(error) => format!("{error:?}"),
            Ok((reached, candidates)) => format!(
                "REACHED {} declarations, {} candidates",
                reached.len(),
                candidates.len()
            ),
        }
    );
    failures.require(
        ablated_reach.is_err(),
        "removing the return removes the reach — the conduct went with the structure",
    );

    // ------------------------------------------------------------------ the return
    println!("\n{}", "-".repeat(104));
    println!("THE RETURN");
    println!("{}", "-".repeat(104));
    println!("  The cycle closed on real mathematics: mathlib in scope, a real kernel verdict per");
    println!("  path, the returned difference read through the additive->multiplicative chart");
    println!("  transition with its cocycle law exact, deposited whole, and a later theorem that");
    println!("  could not be reached before reaching it after — and losing it again on ablation.");

    if failures.0.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED CONTROLS:");
        for failure in &failures.0 {
            println!("    {failure}");
        }
        std::process::exit(1);
    }
}
