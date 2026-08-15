//! Driver: `LeanMathematicsEcology` conditions on the repository's own formal corpus, generates
//! a plural proof-path family for a theorem it was never shown, and crosses every path against a
//! real exterior Lean kernel.
//!
//! `LeanMathematicsEcology` (`soma/life/src/lean_mathematics.rs`, `.../lean_mathematics/ecology.rs`)
//! is the proof-production owner: Lean source crosses as developmental material and departs, the
//! retained body is an incidence atlas of declaration organs and binder charts, and a later
//! theorem recruits its local declaration star and composes proof paths from the conditioned
//! organs. It had **33 references and zero drivers**. This is its driver.
//!
//! ## What conducts here
//!
//! ```text
//!   soma/formal/**.lean                    real repository Lean sources
//!     -> collect_lean_documents            the corpus reader the owner exposes
//!     -> LeanMathematicsEcology::condition source crosses, source departs
//!     -> materialize_kernel_problem        the declared source scope becomes the environment
//!     -> generate_proof_candidates         a PLURAL path family, never a ranked candidate
//!     -> LeanKernelWorld::grade_all        `lake env lean`, a real exterior verdict per path
//!     -> the rendered Lean source          the artifact, returned and printed in full
//! ```
//!
//! ## The declared controls
//!
//! A law that returns zero proves nothing about itself, and a receipt that could not have come
//! out otherwise carries no evidence (`CLAUDE.md` §8). Four controls make this driver's returns
//! mean something, and the driver exits non-zero if any of them does not hold:
//!
//! - **The law returns non-zero.** At least one kernel-admitted path must carry a *non-empty
//!   declaration lineage* — a path that recruited a conditioned declaration organ, not a bare
//!   closing tactic that would have closed the goal from nothing.
//! - **The kernel refuses.** At least one path must be obstructed. A kernel that admits every
//!   submitted term is not in the loop.
//! - **Total structural ablation.** A `mount()`-only body — the inherited proof-motion codecs and
//!   no developmental mathematics — must refuse the same problem with `NoLocalDeclarations`. It
//!   cannot emit a single candidate.
//! - **Partial structural ablation.** Delete one declaration from the corpus text and re-condition.
//!   Every generated path that recruited it must disappear, and the admitted family must lose
//!   exactly the admitted proofs that named it. The conduct is removed *by removing structure*,
//!   not by subtracting a constant from a counter.
//!
//! ## The corpus gap — CLOSED 2026-08-14, and the old text is carried
//!
//! Conditioning is text-level and reaches the whole tracked corpus. Kernel checking used not to.
//! This read: *"`elementary-holonics` and `rh-source-transport` both `require mathlib`, whose
//! package cache is not materialized under `soma/formal`, so no verdict is available for a theorem
//! posed in their environment."* It was true when written and is no longer: the packages are
//! vendored (7,516 mathlib modules at rev `a3a10db0`) and the library is built — 7,523 oleans
//! including `Mathlib.olean`, recovered from the library's own published cache by
//! `lake exe cache get` in two minutes with nothing downloaded.
//!
//! The kernel loop below still runs in `soma/formal/kernel-witness` because it is fast and offline,
//! which suits an ablation that runs many times. **That is now a declared cost choice and no
//! longer a constraint.** A deed wanting a verdict against real mathematics passes
//! `soma/formal/elementary-holonics` to `LeanKernelWorld::new`, which has always taken the project
//! root as a parameter, and declares the aperture: a file importing all of mathlib elaborates in
//! 10.2 s against `kernel-witness`'s sub-second.
//!
//! Run:
//!
//! ```text
//! cargo run -p life --example eros_lean_proof_production
//! ```

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
    process::Command,
};

use life::lean_mathematics::{
    collect_lean_documents, kernel_returns::LeanKernelReturnFamily, LeanKernelWorld,
    LeanMathematicsEcology, LeanMathematicsError, LeanProofCandidate, LeanProofProblem,
    LeanSourceDocument,
};

/// The one declaration this driver ablates out of the corpus.
const ABLATED_DECLARATION: &str = "formal_carry";

/// A proof body from the mathlib corpus. It must be present in the crossing source and absent
/// from native standing: the developmental surfaces depart, the declaration morphology remains.
const DEPARTING_PROOF_TEXT: &str = "nlinarith [hc m, hcong m]";

fn repository_root() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    root.canonicalize().unwrap_or(root)
}

/// Which aperture an obstruction is testimony about.
///
/// `CLAUDE.md` §8: an organ used past its declared aperture is a defect even when it appears to
/// return. The conditioned tactic species come from a corpus that imports Mathlib; the kernel
/// environment that can be checked offline is Lean core. A path refused because its closing tactic
/// does not exist in that environment says nothing about the mathematics, and counting it beside a
/// type mismatch would inflate the obstruction population with an environment fact.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ObstructionSpecies {
    /// The kernel environment does not carry the named tactic or constant.
    EnvironmentAperture,
    /// The kernel read the term and refused it.
    Mathematical,
}

fn obstruction_species(diagnostic: &str) -> ObstructionSpecies {
    if diagnostic.contains("unknown tactic")
        || diagnostic.contains("unknown identifier")
        || diagnostic.contains("unknown constant")
    {
        ObstructionSpecies::EnvironmentAperture
    } else {
        ObstructionSpecies::Mathematical
    }
}

/// Remove one whole `theorem`/`lemma` block from a Lean document by name. The block runs from its
/// header line to the next line that opens a new top-level form, which is the same chunking the
/// owner's own parser uses.
fn without_declaration(text: &str, name: &str) -> String {
    let opener = format!("theorem {name}");
    let alternate = format!("lemma {name}");
    let mut kept = Vec::new();
    let mut dropping = false;
    for line in text.lines() {
        if dropping {
            let top_level = line.len() == line.trim_start().len();
            let opens_new_form = top_level
                && (line.starts_with("theorem ")
                    || line.starts_with("lemma ")
                    || line.starts_with("def ")
                    || line.starts_with("noncomputable ")
                    || line.starts_with("abbrev ")
                    || line.starts_with("namespace ")
                    || line.starts_with("end ")
                    || line.starts_with("/--")
                    || line.starts_with("/-!"));
            if !opens_new_form {
                continue;
            }
            dropping = false;
        }
        if line.starts_with(&opener) || line.starts_with(&alternate) {
            dropping = true;
            continue;
        }
        kept.push(line);
    }
    let mut text = kept.join("\n");
    text.push('\n');
    text
}

fn ablate_corpus(corpus: &[LeanSourceDocument], name: &str) -> Vec<LeanSourceDocument> {
    corpus
        .iter()
        .map(|document| {
            LeanSourceDocument::new(
                document.path.clone(),
                without_declaration(&document.text, name),
            )
        })
        .collect()
}

fn toolchain_pin(project_root: &Path) -> String {
    std::fs::read_to_string(project_root.join("lean-toolchain"))
        .expect("the kernel project carries a lean-toolchain pin")
        .trim()
        .to_owned()
}

fn running_toolchain() -> String {
    let output = Command::new("lean")
        .arg("--version")
        .output()
        .expect("`lean` is on PATH; without it no kernel verdict is available at all");
    String::from_utf8_lossy(&output.stdout).trim().to_owned()
}

/// Build the kernel project's library so a submitted term may `import` it. Without this the
/// environment resolves nothing and every verdict is an import obstruction, which would be a
/// receipt that could not have come out otherwise.
fn build_kernel_project(project_root: &Path) -> bool {
    let output = Command::new("lake")
        .arg("build")
        .current_dir(project_root)
        .output()
        .expect("`lake` is on PATH");
    if !output.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&output.stderr));
    }
    output.status.success()
}

fn indent(text: &str, pad: &str) -> String {
    text.lines()
        .map(|line| format!("{pad}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn lineage(candidate: &LeanProofCandidate) -> Vec<String> {
    candidate
        .declaration_lineage
        .iter()
        .map(|declaration| declaration.to_string())
        .collect()
}

/// The theorem the ecology was never shown, posed in the environment Lean core alone can check.
fn core_problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "carrier-transport".to_owned(),
        source_scope: BTreeSet::from(["KernelWitness.lean".to_owned()]),
        prefix: "import KernelWitness\nnamespace Soma".to_owned(),
        theorem_header: "theorem carrier_transport (P : Prop) (h : P) : exactCarrier P".to_owned(),
        suffix: "end Soma".to_owned(),
    }
}

/// The laboratory's own held-out theorem, posed against the mathlib corpus. Its declaration star
/// is reachable and its proof paths are generated; only its kernel environment is missing.
fn mathlib_problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "proportional-flow-respects-capacity".to_owned(),
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

struct Failures(Vec<String>);

impl Failures {
    fn require(&mut self, held: bool, claim: &str) {
        println!("    [{}] {claim}", if held { "holds" } else { "FAILS" });
        if !held {
            self.0.push(claim.to_owned());
        }
    }
}

fn main() {
    let mut failures = Failures(Vec::new());
    let root = repository_root();
    let corpus_root = root.join("soma/formal");
    let project_root = root.join("soma/formal/kernel-witness");
    let scratch_root = root.join("output/lean-proof-production");

    // ---------------------------------------------------------------- the environment
    println!("=== the kernel environment, recorded beside every verdict");
    println!("    corpus root      {}", corpus_root.display());
    println!("    kernel project   {}", project_root.display());
    let pin = toolchain_pin(&project_root);
    let running = running_toolchain();
    println!("    lean-toolchain   {pin}");
    println!("    lean --version   {running}");
    let pinned = pin.rsplit(':').next().unwrap_or_default();
    let pin_holds = running.contains(pinned.trim_start_matches('v'));
    println!(
        "    pin holds        {}",
        if pin_holds {
            "yes"
        } else {
            "NO — the verdicts below are real but not reproducible evidence"
        }
    );
    let built = build_kernel_project(&project_root);
    println!(
        "    lake build       {}",
        if built { "ok" } else { "FAILED" }
    );
    failures.require(pin_holds, "the running kernel is the pinned toolchain");
    failures.require(built, "the kernel project's library builds");

    // ---------------------------------------------------------------- the corpus
    println!("\n=== the corpus that crossed");
    let corpus = collect_lean_documents(&corpus_root).expect("the formal corpus reads");
    let corpus_bytes: usize = corpus.iter().map(|document| document.text.len()).sum();
    println!("    {} Lean documents, {corpus_bytes} bytes", corpus.len());
    for document in &corpus {
        println!("      {}", document.path);
    }

    let ecology = LeanMathematicsEcology::condition(&corpus).expect("the corpus conditions");
    let receipt = ecology.receipt().clone();
    println!("\n    conditioning receipt");
    println!(
        "      source documents exposed  {}",
        receipt.source_documents_exposed
    );
    println!(
        "      source bytes exposed      {}",
        receipt.source_bytes_exposed
    );
    println!(
        "      retained source surfaces  {}",
        receipt.retained_source_surfaces
    );
    println!(
        "      declaration organs        {}",
        receipt.declaration_organs
    );
    println!("      binder charts             {}", receipt.binder_charts);
    println!(
        "      declaration relations     {}",
        receipt.declaration_relations
    );
    println!(
        "      mounted codecs            {:?}",
        receipt.mounted_codecs
    );
    println!(
        "      tactic species            {:?}",
        receipt.tactic_species
    );

    let native = ecology.to_native_bytes().expect("standing rests natively");
    let native_text = String::from_utf8_lossy(&native).into_owned();
    let crossed_the_source = corpus
        .iter()
        .any(|document| document.text.contains(DEPARTING_PROOF_TEXT));
    println!("\n    source departure, checked on one exact proof body");
    println!("      probe                     {DEPARTING_PROOF_TEXT:?}");
    println!("      present in crossed source {crossed_the_source}");
    println!(
        "      present in native standing {}",
        native_text.contains(DEPARTING_PROOF_TEXT)
    );
    failures.require(
        crossed_the_source && !native_text.contains(DEPARTING_PROOF_TEXT),
        "the developmental proof body crossed and did not enter native standing",
    );
    failures.require(
        receipt.retained_source_surfaces == 0 && receipt.declaration_organs > 0,
        "declaration morphology remains with zero retained source surfaces",
    );

    // ---------------------------------------------------------------- reach over real material
    println!("\n=== reach over the mathlib corpus, up to the missing environment");
    let mathlib = mathlib_problem();
    let mathlib_kernel_problem = ecology
        .materialize_kernel_problem(&mathlib)
        .expect("the mathlib problem materializes");
    match ecology.generate_proof_candidates(&mathlib_kernel_problem) {
        Ok((reached, candidates)) => {
            println!(
                "    theorem            {}",
                mathlib.theorem_header.lines().next().unwrap_or_default()
            );
            println!("    source scope       {:?}", mathlib.source_scope);
            println!(
                "    declaration star   {:?}",
                reached.iter().collect::<Vec<_>>()
            );
            println!("    proof paths        {}", candidates.len());
            println!("    two generated paths, verbatim:");
            for candidate in candidates
                .iter()
                .filter(|candidate| !candidate.declaration_lineage.is_empty())
                .take(2)
            {
                println!(
                    "      --- ordinal {} lineage {:?}",
                    candidate.ordinal,
                    lineage(candidate)
                );
                println!("{}", indent(&candidate.proof, "          "));
            }
            failures.require(
                !reached.is_empty() && candidates.len() > 1,
                "the mathlib corpus reaches a declaration star and composes a plural path family",
            );
        }
        Err(error) => {
            println!("    generation refused: {error}");
            failures.require(false, "the mathlib corpus composes a proof path family");
        }
    }
    println!(
        "    GAP: no verdict is available for this theorem. Its environment requires mathlib,\n         \
         whose package cache is not materialized under soma/formal. The kernel loop below runs\n         \
         in soma/formal/kernel-witness, which Lean core alone can check."
    );

    // ---------------------------------------------------------------- total ablation
    println!("\n=== control: total structural ablation");
    let mounted_only = LeanMathematicsEcology::mount();
    println!(
        "    a mount()-only body carries {} declaration organs and the inherited codecs {:?}",
        mounted_only.receipt().declaration_organs,
        mounted_only.receipt().mounted_codecs
    );
    let problem = core_problem();
    let mounted_refusal = mounted_only.generate_proof_candidates(&problem);
    match &mounted_refusal {
        Ok((_, candidates)) => println!("    it emitted {} candidates", candidates.len()),
        Err(error) => println!("    it refused: {error}"),
    }
    failures.require(
        matches!(
            mounted_refusal,
            Err(LeanMathematicsError::NoLocalDeclarations)
        ),
        "with no conditioned declaration organ the body emits no proof path at all",
    );

    // ---------------------------------------------------------------- the kernel loop
    let kernel = LeanKernelWorld::new(&project_root, &scratch_root, 4)
        .expect("the kernel world mounts with a nonzero worker aperture");
    let kernel_problem = ecology
        .materialize_kernel_problem(&problem)
        .expect("the core problem materializes");

    println!("\n=== the deed: a theorem the body was never shown");
    println!("    identity      {}", problem.identity);
    println!("    source scope  {:?}", problem.source_scope);
    println!("    theorem header");
    println!("{}", indent(&problem.theorem_header, "      "));
    println!(
        "    self-emanated declarations mounted into the environment: {}",
        usize::from(kernel_problem.prefix != problem.prefix)
    );

    let (reached, candidates) = ecology
        .generate_proof_candidates(&kernel_problem)
        .expect("the conditioned body composes a plural proof family");
    println!(
        "    declaration star  {:?}",
        reached.iter().collect::<Vec<_>>()
    );
    println!("    proof paths       {}", candidates.len());

    let returns = kernel
        .grade_all(&kernel_problem, &candidates)
        .expect("every candidate receives a kernel verdict");
    report_returns(&kernel_problem, &returns);

    let admitted_with_lineage = returns
        .kernel_admitted()
        .filter(|returned| !returned.candidate().declaration_lineage.is_empty())
        .count();
    let admitted_recruiting_nothing = returns.kernel_admitted_extent() - admitted_with_lineage;
    let environment_obstructions = returns
        .obstructions()
        .filter(|returned| {
            obstruction_species(returned.diagnostic()) == ObstructionSpecies::EnvironmentAperture
        })
        .count();
    let mathematical_obstructions = returns.obstruction_extent() - environment_obstructions;
    println!("\n    --- reading the obstruction population");
    println!(
        "      mathematical      {mathematical_obstructions}  the kernel read the term and refused it"
    );
    println!(
        "      environment       {environment_obstructions}  the closing tactic does not exist in this kernel\n\
         \x20                       environment. The tactic species were conditioned from a corpus\n\
         \x20                       that imports Mathlib; the offline-checkable environment is Lean\n\
         \x20                       core. These say nothing about the mathematics and are reported\n\
         \x20                       separately rather than folded into the refusal count."
    );
    println!(
        "      admitted recruiting nothing  {admitted_recruiting_nothing}  a bare closing tactic reached the goal\n\
         \x20                       without any conditioned organ. `exactCarrier P` is definitionally\n\
         \x20                       `P`, so `assumption` closes it from the hypothesis alone. This is\n\
         \x20                       why the control below requires a NON-EMPTY declaration lineage."
    );
    failures.require(
        admitted_with_lineage > 0,
        "the kernel admitted at least one path that recruited a conditioned declaration organ",
    );
    failures.require(
        mathematical_obstructions > 0,
        "the kernel read at least one term and refused it on the mathematics",
    );

    // ---------------------------------------------------------------- partial ablation
    println!(
        "\n=== control: partial structural ablation — one declaration removed from the corpus"
    );
    let ablated_corpus = ablate_corpus(&corpus, ABLATED_DECLARATION);
    let ablated =
        LeanMathematicsEcology::condition(&ablated_corpus).expect("the ablated corpus conditions");
    let present_before = ecology
        .declarations()
        .any(|organ| organ.name == ABLATED_DECLARATION);
    let present_after = ablated
        .declarations()
        .any(|organ| organ.name == ABLATED_DECLARATION);
    println!(
        "    declaration organs  {} -> {}",
        receipt.declaration_organs,
        ablated.receipt().declaration_organs
    );
    println!("    `{ABLATED_DECLARATION}` organ present: {present_before} -> {present_after}");
    failures.require(
        present_before && !present_after,
        "the ablation removed the declaration organ itself, not a counter",
    );

    let ablated_kernel_problem = ablated
        .materialize_kernel_problem(&problem)
        .expect("the ablated body materializes the same problem");
    let (ablated_reached, ablated_candidates) = ablated
        .generate_proof_candidates(&ablated_kernel_problem)
        .expect("the ablated body still composes a family");
    println!(
        "    declaration star    {:?} -> {:?}",
        reached.iter().collect::<Vec<_>>(),
        ablated_reached.iter().collect::<Vec<_>>()
    );
    println!(
        "    proof paths         {} -> {}",
        candidates.len(),
        ablated_candidates.len()
    );
    let names_ablated = ablated_candidates
        .iter()
        .filter(|candidate| candidate.proof.contains(ABLATED_DECLARATION))
        .count();
    println!("    paths still naming `{ABLATED_DECLARATION}`: {names_ablated}");
    failures.require(
        names_ablated == 0,
        "no generated path names the removed declaration",
    );

    let ablated_returns = kernel
        .grade_all(&ablated_kernel_problem, &ablated_candidates)
        .expect("every ablated candidate receives a kernel verdict");

    let admitted_before = returns
        .kernel_admitted()
        .map(|returned| returned.candidate().proof.clone())
        .collect::<BTreeSet<_>>();
    let admitted_after = ablated_returns
        .kernel_admitted()
        .map(|returned| returned.candidate().proof.clone())
        .collect::<BTreeSet<_>>();
    let lost = admitted_before
        .difference(&admitted_after)
        .cloned()
        .collect::<Vec<_>>();
    println!(
        "    kernel-admitted paths  {} -> {}",
        admitted_before.len(),
        admitted_after.len()
    );
    println!("    admitted proofs LOST by removing the organ:");
    for proof in &lost {
        println!("{}", indent(proof, "        "));
        println!("        ---");
    }
    let every_loss_named_it = lost.iter().all(|proof| proof.contains(ABLATED_DECLARATION));
    let survivors = admitted_after.len();
    failures.require(
        !lost.is_empty() && every_loss_named_it,
        "removing the organ removed exactly the admitted conduct that recruited it",
    );
    println!(
        "    surviving admitted paths: {survivors} — the plural fiber is not a single point, so\n    \
         the ablation removes one recruitment rather than the body's ability to prove."
    );

    // ---------------------------------------------------------------- source-detached remount
    println!("\n=== source-detached remount");
    let remounted = LeanMathematicsEcology::from_native_bytes(&native)
        .expect("native standing remounts without its sources");
    let remounted_kernel_problem = remounted
        .materialize_kernel_problem(&problem)
        .expect("the remounted body materializes the same problem");
    let (remounted_reached, remounted_candidates) = remounted
        .generate_proof_candidates(&remounted_kernel_problem)
        .expect("the remounted body composes a family");
    println!(
        "    native bytes {} — declaration star and path family reproduced after the corpus departed",
        native.len()
    );
    failures.require(
        remounted_reached == reached && remounted_candidates == candidates,
        "the source-detached body generates the identical proof family",
    );

    // ---------------------------------------------------------------- the return
    println!("\n=== the return");
    println!(
        "    conditioned declaration organs   {}",
        receipt.declaration_organs
    );
    println!("    proof paths generated            {}", candidates.len());
    println!(
        "    kernel-admitted                  {}",
        returns.kernel_admitted_extent()
    );
    println!(
        "    obstructed                       {} ({mathematical_obstructions} mathematical, {environment_obstructions} environment)",
        returns.obstruction_extent()
    );
    println!("    admitted with recruited organ    {admitted_with_lineage}");
    println!(
        "    scratch                          {}",
        scratch_root.display()
    );
    let kernel_millis: u64 = returns
        .members()
        .iter()
        .chain(ablated_returns.members())
        .map(|returned| returned.observed_millis())
        .sum();
    println!(
        "    exterior kernel wall time        {kernel_millis} ms over {} submissions (observer\n    \
         telemetry only; it never enters candidate selection or standing)",
        returns.members().len() + ablated_returns.members().len()
    );

    if failures.0.is_empty() {
        println!(
            "\nThe owner conducted: it conditioned on real Lean sources, let them depart, recruited a\n\
             declaration star for a theorem it was never shown, composed a plural proof family, and a\n\
             real exterior kernel admitted a path that recruited a conditioned organ and refused\n\
             others. Removing that organ removed exactly that admitted conduct."
        );
    } else {
        eprintln!(
            "\nFAILED — {} declared control(s) did not hold:",
            failures.0.len()
        );
        for claim in &failures.0 {
            eprintln!("  - {claim}");
        }
        std::process::exit(1);
    }
}

fn report_returns(problem: &LeanProofProblem, returns: &LeanKernelReturnFamily) {
    println!("\n    --- every kernel verdict, in candidate chronology");
    for returned in returns.members() {
        let candidate = returned.candidate();
        println!(
            "      [{:?}] ordinal {} lineage {:?}",
            returned.outcome(),
            candidate.ordinal,
            lineage(candidate)
        );
        println!("{}", indent(&candidate.proof, "          "));
        let diagnostic = returned.diagnostic().trim();
        if !diagnostic.is_empty() {
            println!("          kernel said:");
            println!("{}", indent(diagnostic, "            "));
        }
    }

    println!("\n    --- the artifact: every source the kernel ADMITTED, exactly as it read it");
    for returned in returns.kernel_admitted() {
        let source = problem
            .render(&returned.candidate().proof)
            .expect("an admitted path renders");
        println!(
            "      --- ordinal {} sha256 {}",
            returned.candidate().ordinal,
            returned.source_sha256()
        );
        println!("{}", indent(&source, "          "));
    }
}
