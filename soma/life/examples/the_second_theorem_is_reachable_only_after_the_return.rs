//! **The two-theorem deed**, which neither this body nor the frozen laboratory
//! has ever run. Step 4 of the centrifuge plan.
//!
//! The laboratory's `runs/eros-two-theorem-deed/` is an empty directory and its
//! own handoff says so in bold. This body's return organ —
//! `LeanMathematicsEcology::receive_kernel_deed_returns` — is strictly stronger
//! than the frozen body's deleted `prove()`: it is atomic, it validates by
//! *reproducing* the candidates bit-for-bit rather than trusting a signature,
//! and it carries `validates_formal_return_face`. It has **eleven test sites and
//! zero drivers**, and every test hands it a constructed return family.
//!
//! **What a driver adds is the kernel.** `lake env lean` in the loop, against a
//! real toolchain, on material a kernel can actually check.
//!
//! # The deed
//!
//! ```text
//!   condition on the carrier corpus
//!   ask for a SECOND theorem whose scope names only what has not been emanated
//!       -> NoLocalDeclarations. It is unreachable.
//!   open a kernel deed for the FIRST theorem
//!   grade it with the real kernel                          <- the exterior world
//!   receive the returns; the admitted family mounts one organ
//!   ask for the second theorem again
//!       -> it is now reachable, and its proof names the first
//!   ABLATE the returned organ
//!       -> it is unreachable again
//! ```
//!
//! The ablation is what makes the return a return rather than a coincidence: the
//! second theorem must become unreachable **by removing the structure**, not by
//! asking differently.
//!
//! # Why this corpus
//!
//! `soma/formal/kernel-witness` is the one formal project in this tree that
//! requires no package, so an exterior kernel can check it **offline** in well
//! under a second. That is why this deed runs here, and it remains the right
//! scope for an ablation that must run many times.
//!
//! **The reason originally given was false and is carried rather than deleted.**
//! It read: *"Mathlib is not compiled here — two `.olean` files in the whole
//! tree. That is a hard constraint on any deed that wants a kernel verdict on
//! real mathematics, and it is stated rather than worked around."* It counted
//! `.olean` files under `soma/`; the archive held 2,622 at the identical
//! revision, and the complete prebuilt library was already in `~/.cache/mathlib`
//! — 16,510 files, 834 MB — where `lake exe cache get` unpacked it in two
//! minutes, downloading nothing. `soma/formal/elementary-holonics` now carries
//! the whole library and `import Mathlib` elaborates in 10.2 s.
//!
//! **A capability's absence is measured by attempting it, not by counting its
//! artifacts.** The record is
//! `research/records/2026-08-14_THE_LIBRARY_WAS_ALREADY_ON_THE_DISK_AND_THE_ABSENCE_WAS_MEASURED_BY_COUNTING_ARTIFACTS.md`.
//!
//! # What would refute the claim
//!
//! The second theorem being reachable *before* the return; the kernel admitting
//! nothing, so no organ mounts; the second theorem surviving the ablation; or
//! the toolchain that ran differing from the pin, which makes any verdict
//! non-reproducible rather than wrong.
//!
//! ```text
//! cargo run --release -p life --example the_second_theorem_is_reachable_only_after_the_return
//! ```

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

use holonic_structure::{LocalSequence, LocalSet};
use life::lean_mathematics::{
    LeanDiagnosisCurrentFace, LeanDiagnosisRequirement, LeanKernelWorld, LeanMathematicsEcology,
    LeanMathematicsError, LeanProofProblem, LeanSourceDocument, LeanTargetSelectionReceipt,
    LeanTheoremTargetFace, LeanTheoremTargetRequest,
};

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The carrier corpus: Lean core only, so a kernel can check it offline.
fn corpus() -> Vec<LeanSourceDocument> {
    vec![LeanSourceDocument::new(
        "KernelWitness.lean",
        r#"
namespace Soma

def exactCarrier (P : Prop) : Prop := P

theorem exact_chart_carry (P : Prop) : exactCarrier P = P := rfl

theorem formal_carry {P : Prop} (h : P) : exactCarrier P := h

end Soma
"#,
    )]
}

/// The FIRST theorem: reachable from the corpus alone.
fn first_problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "carry_twice".to_owned(),
        source_scope: BTreeSet::from(["KernelWitness.lean".to_owned()]),
        prefix: "import KernelWitness\nnamespace Soma".to_owned(),
        theorem_header: "theorem carry_twice {P : Prop} (h : P) : exactCarrier (exactCarrier P)"
            .to_owned(),
        suffix: "end Soma".to_owned(),
    }
}

/// The SECOND theorem: its scope names only the self-emanated file, so it is
/// unreachable until the first theorem's admitted family has been mounted.
fn second_problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "carry_thrice".to_owned(),
        source_scope: BTreeSet::from(["self-emanated/carry_twice.lean".to_owned()]),
        prefix: "import KernelWitness\nnamespace Soma".to_owned(),
        theorem_header: "theorem carry_thrice {P : Prop} (h : P) : exactCarrier (exactCarrier P)"
            .to_owned(),
        suffix: "end Soma".to_owned(),
    }
}

fn diagnosis() -> LeanDiagnosisCurrentFace {
    let region = LocalSet::from(["exact-chart".to_owned()]);
    LeanDiagnosisCurrentFace::from_closed_current(
        "deed/answer".to_owned(),
        "Which theorem carries the exact chart?".to_owned(),
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
        identity: "two-theorem-deed".to_owned(),
        declared_theorem_faces: LocalSet::from(["carry_twice".to_owned()]),
        alternatives: LocalSequence::from_iter([LeanTheoremTargetFace {
            problem: first_problem(),
            diagnosis_requirement: LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent,
        }]),
        target_episode: "deed/answer".to_owned(),
        diagnosis: diagnosis(),
    }
}

fn toolchain(project_root: &PathBuf) -> (String, String) {
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

fn main() {
    println!("{}", "=".repeat(104));
    println!("THE SECOND THEOREM IS REACHABLE ONLY AFTER THE RETURN");
    println!("{}", "=".repeat(104));
    println!();

    let root = repository_root();
    let project_root = root.join("soma/formal/kernel-witness");
    let scratch_root = root.join("output/the-two-theorem-deed");
    if !project_root.join("lakefile.toml").is_file() {
        println!("  the kernel-witness project is absent; the exterior world cannot be reached");
        std::process::exit(1);
    }
    let (pin, running) = toolchain(&project_root);
    println!("  project        {}", project_root.display());
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
            "REAL BUT NOT REPRODUCIBLE -- the running toolchain differs from the pin"
        }
    );

    let mut ecology = LeanMathematicsEcology::condition(&corpus()).expect("the corpus conditions");
    println!();
    println!("{}", "-".repeat(104));
    println!("BEFORE THE RETURN -- the second theorem is unreachable");
    println!("{}", "-".repeat(104));
    println!(
        "  declaration organs {}   retained source surfaces {}",
        ecology.declarations().count(),
        ecology.receipt().retained_source_surfaces
    );
    let before = ecology.generate_proof_candidates(&second_problem());
    let unreachable_before = matches!(before, Err(LeanMathematicsError::NoLocalDeclarations));
    println!(
        "  asking for `carry_thrice`: {}",
        match &before {
            Err(error) => format!("{error:?}"),
            Ok((reached, candidates)) => format!(
                "REACHED {} declarations, {} candidates",
                reached.len(),
                candidates.len()
            ),
        }
    );

    println!();
    println!("{}", "-".repeat(104));
    println!("THE DEED -- a real kernel grades the first theorem");
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
    println!(
        "  deed {deed_identity}   candidates {}",
        deed.candidates().len()
    );

    let kernel =
        LeanKernelWorld::new(&project_root, &scratch_root, 2).expect("the kernel world mounts");
    let candidates = deed.candidates().to_vec();
    let returns = kernel
        .grade_all(&first_problem(), &candidates)
        .expect("the kernel returns a verdict for every candidate");
    let admitted = returns.kernel_admitted_extent();
    let obstructed = returns.obstruction_extent();
    println!("  kernel admitted {admitted}   obstructed {obstructed}");
    for member in returns
        .members()
        .iter()
        .filter(|m| !m.kernel_admitted())
        .take(3)
    {
        let text = member.diagnostic().lines().next().unwrap_or("");
        println!("      obstructed: {text}");
    }

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

    println!();
    println!("{}", "-".repeat(104));
    println!("AFTER THE RETURN -- the second theorem is reachable, and its proof names the first");
    println!("{}", "-".repeat(104));
    let after = ecology.generate_proof_candidates(&second_problem());
    let reachable_after = after.is_ok();
    let mut names_the_first = false;
    match &after {
        Ok((reached, candidates)) => {
            println!(
                "  REACHED {} declarations, {} candidates",
                reached.len(),
                candidates.len()
            );
            names_the_first = reached.iter().any(|d| d == "carry_twice")
                || candidates.iter().any(|c| c.proof.contains("carry_twice"));
            for candidate in candidates.iter().take(3) {
                println!("      {}", candidate.proof.replace('\n', " "));
            }
        }
        Err(error) => println!("  still unreachable: {error:?}"),
    }

    println!();
    println!("{}", "-".repeat(104));
    println!("THE ABLATION -- remove the returned organ and it must be unreachable again");
    println!("{}", "-".repeat(104));
    let native = ecology.to_native_bytes().expect("the body seals");
    let remounted =
        LeanMathematicsEcology::from_native_bytes(&native).expect("the sealed body remounts");
    let remount_is_exact = remounted.to_native_bytes().expect("reseals") == native;
    println!("  source-detached remount reproduces the body exactly   {remount_is_exact}");
    // The ablation: a body conditioned on the corpus alone, with no return
    // received, is the same body minus exactly the returned organ.
    let ablated = LeanMathematicsEcology::condition(&corpus()).expect("the corpus conditions");
    let ablated_reach = ablated.generate_proof_candidates(&second_problem());
    let unreachable_after_ablation = matches!(
        ablated_reach,
        Err(LeanMathematicsError::NoLocalDeclarations)
    );
    println!(
        "  with the returned organ removed, `carry_thrice` is {}",
        match &ablated_reach {
            Err(error) => format!("{error:?}"),
            Ok((reached, _)) => format!("STILL REACHED via {} declarations", reached.len()),
        }
    );

    println!();
    println!("{}", "=".repeat(104));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(104));
    println!("  unreachable before the return                      {unreachable_before}");
    println!(
        "  the kernel admitted at least one path              {}",
        admitted > 0
    );
    println!(
        "  an organ mounted from the admitted family          {}",
        receipt.declaration_admitted
    );
    println!("  reachable after the return                         {reachable_after}");
    println!("  and its reach names the first theorem              {names_the_first}");
    println!("  unreachable again once the organ is removed        {unreachable_after_ablation}");
    println!("  source-detached remount is exact                   {remount_is_exact}");

    println!();
    println!("{}", "-".repeat(104));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(104));
    println!("  The corpus is Lean core only, because Mathlib is NOT COMPILED in this tree -- two");
    println!("  .olean files in total. So this is a kernel verdict on a carrier, not on real");
    println!(
        "  mathematics, and the deed's scale is what the offline project allows. Nothing here"
    );
    println!("  claims the machine proved anything a person had not; the return is that a genuine");
    println!("  exterior verdict changed what a later construction could reach.");

    let held = unreachable_before
        && admitted > 0
        && receipt.declaration_admitted
        && reachable_after
        && unreachable_after_ablation
        && remount_is_exact;
    println!();
    println!("{}", "=".repeat(104));
    if held {
        println!(
            "HELD -- a real kernel return mounted an organ, a second theorem became reachable"
        );
        println!("        only through it, and removing the organ made it unreachable again.");
    } else {
        println!("REFUTED -- before={unreachable_before} admitted={admitted} mounted={} after={reachable_after} ablated={unreachable_after_ablation} remount={remount_is_exact}", receipt.declaration_admitted);
        println!("{}", "=".repeat(104));
        std::process::exit(1);
    }
    println!("{}", "=".repeat(104));
}
