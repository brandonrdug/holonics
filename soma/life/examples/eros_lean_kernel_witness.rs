//! Driver: an exterior Lean kernel is in the loop, and it refuses.
//!
//! `LeanKernelWorld` shells `lake env lean` against a caller-supplied project root. Until now no
//! project existed to supply, and no driver ever entered the owner. This driver supplies
//! `soma/formal/kernel-witness` — the one formal project in this tree that requires no package —
//! and submits three proof terms whose verdicts are known in advance:
//!
//! ```text
//!   carrier transport, correct term      -> KernelAdmitted   (the declared control)
//!   carrier transport, ill-typed term    -> Obstructed
//!   a FALSE statement, plausible term    -> Obstructed
//! ```
//!
//! The refusals alone prove nothing: a kernel that is absent, misconfigured, or pointed at a
//! project it cannot resolve refuses *everything*, and a receipt that could not have come out
//! otherwise carries no evidence. The admitted term is the declared control that makes the two
//! refusals mean something (`CLAUDE.md` §8). The driver fails if any of the three verdicts is not
//! the one named above.
//!
//! The toolchain is recorded beside the verdict. `soma/formal/kernel-witness/lean-toolchain` pins
//! `leanprover/lean4:v4.27.0`; the driver reads that pin, reads `lean --version` from the kernel
//! that actually ran, and prints both. A verdict from an unpinned toolchain is not reproducible
//! evidence, so a mismatch is reported in the receipt rather than swallowed.
//!
//! Run:
//!
//! ```text
//! cargo run -p life --example eros_lean_kernel_witness
//! ```

use std::{path::PathBuf, process::Command};

use holonic_structure::LocalSet;
use life::lean_mathematics::{
    kernel_returns::{LeanKernelOutcome, LeanKernelReturnFamily},
    LeanKernelWorld, LeanProofCandidate, LeanProofProblem,
};

/// One submitted term and the verdict it must receive.
struct SubmittedTerm {
    ordinal: u64,
    proof: &'static str,
    why: &'static str,
    expected: LeanKernelOutcome,
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn toolchain_pin(project_root: &PathBuf) -> String {
    std::fs::read_to_string(project_root.join("lean-toolchain"))
        .expect("kernel-witness carries a lean-toolchain pin")
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

fn candidates(terms: &[SubmittedTerm]) -> Vec<LeanProofCandidate> {
    terms
        .iter()
        .map(|term| LeanProofCandidate {
            ordinal: term.ordinal,
            proof: term.proof.to_owned(),
            motions: Vec::new(),
            declaration_lineage: LocalSet::new(),
        })
        .collect()
}

fn report(
    heading: &str,
    problem: &LeanProofProblem,
    terms: &[SubmittedTerm],
    returned: &LeanKernelReturnFamily,
) -> usize {
    let mut disagreements = 0usize;
    println!("\n=== {heading}");
    println!("--- theorem header");
    println!("{}", problem.theorem_header);
    for (term, member) in terms.iter().zip(returned.members()) {
        let source = problem
            .render(term.proof)
            .expect("every submitted term renders");
        println!("\n--- submitted term {} ({})", term.ordinal, term.why);
        println!("--- the artifact the kernel actually read:");
        for line in source.lines() {
            println!("    {line}");
        }
        println!("    source sha256 {}", member.source_sha256());
        println!("    expected  {:?}", term.expected);
        println!("    returned  {:?}", member.outcome());
        let diagnostic = member.diagnostic().trim();
        if diagnostic.is_empty() {
            println!("    kernel said nothing (clean elaboration)");
        } else {
            println!("    kernel said:");
            for line in diagnostic.lines() {
                println!("        {line}");
            }
        }
        if member.outcome() != term.expected {
            disagreements += 1;
            println!("    DISAGREEMENT: the kernel did not return the known verdict");
        }
    }
    disagreements
}

fn main() {
    let root = repository_root();
    let project_root = root.join("soma/formal/kernel-witness");
    assert!(
        project_root.join("lakefile.toml").is_file(),
        "the kernel-witness Lean project must be in the tree at {}",
        project_root.display()
    );
    let scratch_root = root.join("output/lean-kernel-witness");

    let pin = toolchain_pin(&project_root);
    let running = running_toolchain();
    println!("=== toolchain, recorded beside the verdict");
    println!("    project        {}", project_root.display());
    println!("    lean-toolchain {pin}");
    println!("    lean --version {running}");
    let pinned_version = pin.rsplit(':').next().unwrap_or_default();
    let pin_holds = running.contains(pinned_version.trim_start_matches('v'));
    println!(
        "    pin holds      {}",
        if pin_holds {
            "yes"
        } else {
            "NO — the verdict below is not reproducible evidence"
        }
    );

    let kernel = LeanKernelWorld::new(&project_root, &scratch_root, 2)
        .expect("the kernel world mounts with a nonzero worker aperture");

    // A true statement. One correct term, two wrong ones.
    let carrier_problem = LeanProofProblem {
        identity: "carrier_transport".to_owned(),
        source_scope: ["KernelWitness.lean".to_owned()].into(),
        prefix: "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)"
            .to_owned(),
        theorem_header: "theorem carrier_transport (h : P) : exactCarrier P".to_owned(),
        suffix: "end Soma".to_owned(),
    };
    let carrier_terms = [
        SubmittedTerm {
            ordinal: 0,
            proof: "h",
            why: "correct — the declared control",
            expected: LeanKernelOutcome::KernelAdmitted,
        },
        SubmittedTerm {
            ordinal: 1,
            proof: "Nat.zero",
            why: "known-wrong — a natural number is not a proof of P",
            expected: LeanKernelOutcome::Obstructed,
        },
        SubmittedTerm {
            ordinal: 2,
            proof: "fun x => x",
            why: "known-wrong — an identity function is not a proof of P",
            expected: LeanKernelOutcome::Obstructed,
        },
    ];

    // A FALSE statement. Any admitted term here would be an unsound kernel.
    let false_problem = LeanProofProblem {
        identity: "every_receiver_agrees".to_owned(),
        source_scope: ["KernelWitness.lean".to_owned()].into(),
        prefix: "namespace Soma".to_owned(),
        theorem_header: "theorem every_receiver_agrees (a b : Nat) : a = b".to_owned(),
        suffix: "end Soma".to_owned(),
    };
    let false_terms = [
        SubmittedTerm {
            ordinal: 0,
            proof: "rfl",
            why: "known-wrong — the statement itself is false",
            expected: LeanKernelOutcome::Obstructed,
        },
        SubmittedTerm {
            ordinal: 1,
            proof: "by omega",
            why: "known-wrong — a decision procedure cannot close a false goal",
            expected: LeanKernelOutcome::Obstructed,
        },
    ];

    let carrier_returns = kernel
        .grade_all(&carrier_problem, &candidates(&carrier_terms))
        .expect("every carrier candidate returns a kernel verdict");
    let false_returns = kernel
        .grade_all(&false_problem, &candidates(&false_terms))
        .expect("every false-statement candidate returns a kernel verdict");

    let mut disagreements = report(
        "a true statement: one correct term, two known-wrong terms",
        &carrier_problem,
        &carrier_terms,
        &carrier_returns,
    );
    disagreements += report(
        "a FALSE statement: every term must be refused",
        &false_problem,
        &false_terms,
        &false_returns,
    );

    let admitted =
        carrier_returns.kernel_admitted_extent() + false_returns.kernel_admitted_extent();
    let obstructed = carrier_returns.obstruction_extent() + false_returns.obstruction_extent();
    println!("\n=== the return");
    println!("    submitted   {}", admitted + obstructed);
    println!("    admitted    {admitted}");
    println!("    obstructed  {obstructed}");
    println!("    scratch     {}", scratch_root.display());

    if admitted == 0 {
        eprintln!(
            "\nFAILED: the kernel admitted nothing at all. A pipeline that refuses everything \
             has not demonstrated that a kernel is in the loop — it has demonstrated that \
             something upstream is broken."
        );
        std::process::exit(1);
    }
    if disagreements != 0 {
        eprintln!("\nFAILED: {disagreements} verdict(s) disagreed with the known outcome.");
        std::process::exit(1);
    }
    if !pin_holds {
        eprintln!(
            "\nFAILED: the running kernel is not the pinned toolchain; the verdicts above are \
             real but they are not reproducible evidence."
        );
        std::process::exit(1);
    }
    println!(
        "\nThe kernel is in the loop: it admitted the correct term and refused every known-wrong \
         one, including both terms offered for a false statement."
    );
}
