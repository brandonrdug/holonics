//! WRD4 — the kernel return deposits on the route it crossed, and later current rides it.
//!
//! The Lean kernel is the first world. Two arms cross it in one bounded process:
//!
//! * the repository's own `Foundation/` corpus, conditioned as the Lean material chart, founded
//!   as one carrier population, conducted from a target theorem's own premise crossing, rendered
//!   by the standing template render over the carriers the route crossed, graded by
//!   `lake env lean`, and returned through the junction; and
//! * a minimal Lean corpus the standing render can cross, so the deposit, the later probe, the
//!   withdrawal, and the replay are exercised against real kernel verdicts.
//!
//! The Foundation arm is reported as what it returns. When the standing render admits nothing on
//! it inside the bound, that is the named obstruction: the template projection is the emitter,
//! and the kernel reflects it. Nothing selects among candidates; every rendered candidate is
//! graded. Target order reads retained morphology only: declarations whose retained tactic
//! species lie inside the render's own vocabulary come first, then the rest, each by name.
//!
//! Declared apertures: the process is bounded by the repository's 180-second rule, so each arm
//! conducts targets until the first world return deposits or a declared elapsed budget passes,
//! and the later probe is the referrer whose own thread carries the fewest carriers (the smallest
//! family the standing render will pose); targets are ordered by that same referrer carrier
//! count after the vocabulary read, so the probe the bound can afford comes first; the kernel
//! worker count is an apparatus aperture. None of these is a semantic level, and none reads a
//! kernel outcome before it happened.
//!
//! What this driver does not claim: general theorem proving, that a target was unseen (its header
//! is supplied and its premise incidence remains as morphology while its proof text departed), or
//! any qualitative grade.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::native_ecology::holonic_intelligence::{
    NativeInferenceAddress, NativeInferenceRequest,
};
use holonic_engine::receiver_exact_compression::ReceiverId;
use holonic_engine::{BoundaryId, EventId};
use life::lean_mathematics::{
    collect_lean_documents, found_lean_lattice, generator_thread_address, EmissionGrain,
    LeanKernelWorld, LeanLatticeColdWitness, LeanMathematicsEcology, LeanProofProblem,
    LeanSourceDocument, LEAN_LATTICE_SPOOL_ADDRESS,
};
use life::native_intelligence::route_return::{
    derive_world_return, kernel_return_faces, KernelReturnFace, Termination,
    WorldReturnDisposition,
};
use life::native_intelligence::{
    ApparatusRealization, InferenceConfigurationAddress, MorphologyLineage,
    NativeCirculationBoundary, NativeCirculationConfiguration, NativeCirculationSession,
    NativeEcologyRest, NativeMorphologyPackage,
};
use serde::Serialize;

const RECEIVER: ReceiverId = ReceiverId(7);
const DECLARATION_FACE: BoundaryId = BoundaryId(0);
const KERNEL_WORKERS: usize = 10;
/// The standing render's own tactic vocabulary (closers and the application prefixes).
const RENDER_VOCABULARY: [&str; 9] = [
    "exact", "simpa", "rw", "have", "assumption", "nlinarith", "linarith", "ring", "aesop",
];
/// The minimal corpus the standing render can cross: `beta` restates `alpha` up to `simp`, and
/// `gamma` restates `beta` the same way. No import: the kernel's core suffices.
const MINIMAL_CORPUS: &str = "def f (n : Nat) : Nat := n + 1\n\n\
theorem alpha (n : Nat) : f n = n + 1 := rfl\n\n\
theorem beta (n : Nat) : f n = n + 1 ∧ True := by\n  exact ⟨alpha n, trivial⟩\n\n\
theorem gamma (n : Nat) : True ∧ f n = n + 1 := by\n  exact ⟨trivial, (beta n).1⟩\n";

#[derive(Serialize)]
struct TargetReceipt {
    target: String,
    premises: Vec<String>,
    route_organs: Vec<String>,
    candidates: usize,
    admitted: usize,
    obstructed: usize,
    disposition: String,
    junction: Option<(u64, u64, u128)>,
    termination: String,
    committed_generation: Option<u64>,
    cone: usize,
    elapsed_millis: u128,
}

#[derive(Clone, Serialize, PartialEq, Eq)]
struct Verdict {
    route_organs: Vec<String>,
    candidates: usize,
    admitted: usize,
}

#[derive(Serialize)]
struct ProbeReceipt {
    later_target: String,
    morphology: String,
    own_route: Verdict,
    deposit_route_reached: bool,
    deposit_route: Option<Verdict>,
}

#[derive(Serialize)]
struct ArmReceipt {
    arm: String,
    corpus_documents: usize,
    declaration_organs: u64,
    carriers: usize,
    threads: usize,
    targets_total: usize,
    targets: Vec<TargetReceipt>,
    deposit_target: Option<String>,
    probes: Vec<ProbeReceipt>,
    own_route_verdict_differs_current_vs_withdrawn: Option<bool>,
    deposit_route_verdict_differs_current_vs_withdrawn: Option<bool>,
    replay_equals_current: Option<bool>,
    obstruction: Option<String>,
    arm_matched_halts: (usize, usize),
    arm_unmatched_stays_open: (usize, usize),
    arm_both_species_present: bool,
    elapsed_millis: u128,
}

#[derive(Serialize)]
struct Receipt {
    schema: &'static str,
    arms: Vec<ArmReceipt>,
    elapsed_millis: u128,
}

fn theorem_problem(documents: &[LeanSourceDocument], target: &str) -> Option<LeanProofProblem> {
    for document in documents {
        let text = document.text.as_str();
        let mut offset = 0usize;
        for line in text.lines() {
            let trimmed = line.trim_start();
            let named = |keyword: &str| {
                trimmed
                    .strip_prefix(keyword)
                    .is_some_and(|rest| rest.split_whitespace().next() == Some(target))
            };
            if line.len() == trimmed.len() && (named("theorem ") || named("lemma ")) {
                let chunk = &text[offset..];
                let split = chunk.find(":=")?;
                let header = chunk[..split].trim();
                let header = header
                    .strip_prefix("lemma ")
                    .map(|rest| format!("theorem {rest}"))
                    .unwrap_or_else(|| header.to_owned());
                return Some(LeanProofProblem {
                    identity: target.to_owned(),
                    source_scope: BTreeSet::new(),
                    prefix: text[..offset].to_owned(),
                    theorem_header: header,
                    suffix: String::new(),
                });
            }
            offset += line.len() + 1;
        }
    }
    None
}

fn names_of(
    session: &NativeCirculationSession,
    witness: &LeanLatticeColdWitness,
    thread_address: &str,
    excluded: &str,
) -> BTreeSet<String> {
    session.package().hot().native().spools[0]
        .threads
        .iter()
        .find(|thread| thread.address == thread_address)
        .map(|thread| {
            thread
                .native_support
                .iter()
                .filter_map(|state| witness.declaration_of(*state))
                .filter(|name| *name != excluded)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

fn conduct(
    session: &NativeCirculationSession,
    thread: String,
    occurrence: EventId,
) -> Result<NativeCirculationBoundary, String> {
    session
        .conduct(NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: LEAN_LATTICE_SPOOL_ADDRESS.to_owned(),
                thread,
                occurrence,
            },
            receiver: RECEIVER,
        })
        .map_err(|error| format!("conduct refused: {error}"))
}

fn grade(
    world: &LeanKernelWorld,
    ecology: &LeanMathematicsEcology,
    problem: &LeanProofProblem,
    organs: &BTreeSet<String>,
) -> Result<(usize, Vec<KernelReturnFace>), String> {
    let (_, candidates) = ecology
        .generate_proof_candidates_for(problem, organs, EmissionGrain::Typed)
        .map_err(|error| format!("render refused: {error}"))?;
    let family = world
        .grade_all(problem, &candidates)
        .map_err(|error| format!("kernel refused: {error}"))?;
    Ok((candidates.len(), kernel_return_faces(&family)))
}

fn verdict(
    world: &LeanKernelWorld,
    ecology: &LeanMathematicsEcology,
    problem: &LeanProofProblem,
    organs: BTreeSet<String>,
) -> Verdict {
    let (candidates, faces) = grade(world, ecology, problem, &organs).unwrap_or((0, Vec::new()));
    Verdict {
        route_organs: organs.into_iter().collect(),
        candidates,
        admitted: faces.iter().filter(|face| face.admitted).count(),
    }
}

fn run_arm(
    arm: &str,
    documents: &[LeanSourceDocument],
    world: &LeanKernelWorld,
    budget_seconds: u64,
) -> ArmReceipt {
    let began = Instant::now();
    let ecology = LeanMathematicsEcology::condition(documents).expect("the corpus conditions");
    let receipt = ecology.receipt().clone();
    let lattice = found_lean_lattice(&ecology, RECEIVER).expect("the mouth founds the lattice");
    let witness = lattice.witness;
    let carriers = lattice.native.spools[0].native_population.len();
    let threads = lattice.native.spools[0].threads.len();
    println!(
        "\n=== arm {arm}: {} documents, {} organs -> {carriers} carriers, {threads} threads, {} references, {} unresolved",
        documents.len(),
        receipt.declaration_organs,
        witness.reference_by_occurrence.len(),
        witness.unresolved_references.len()
    );
    let max_occurrence = witness
        .reference_by_occurrence
        .keys()
        .max()
        .copied()
        .unwrap_or(0);

    let rest = NativeEcologyRest::found(lattice.native).expect("rest");
    let package = NativeMorphologyPackage::found(
        rest,
        MorphologyLineage::origin(),
        Vec::new(),
        vec![ApparatusRealization {
            apparatus_family: "wrd4-lean-kernel-world".to_owned(),
            realization_version: "v1".to_owned(),
        }],
        Vec::new(),
    )
    .expect("package");
    let configuration = NativeCirculationConfiguration::found(InferenceConfigurationAddress {
        ingress_aperture: "lean-declaration-lattice".to_owned(),
        occurrence: EventId(0),
        receiver: RECEIVER,
        continuation_receiver: "native-successor".to_owned(),
        world_return_law: "lean-kernel-junction".to_owned(),
        emission_codec: "route-organs-typed-render".to_owned(),
        apparatus: "resident-cuda".to_owned(),
        stochastic_current: None,
    })
    .expect("configuration");
    let mut session = NativeCirculationSession::mount(package, configuration).expect("mount");

    let referrers = |name: &str| -> Vec<String> {
        let mut found = witness
            .reference_by_occurrence
            .values()
            .filter(|reference| reference.referenced == name)
            .map(|reference| reference.referring.clone())
            .collect::<Vec<_>>();
        found.sort();
        found.dedup();
        found
    };
    let premises_of = |name: &str| -> Vec<String> {
        let mut found = witness
            .reference_by_occurrence
            .values()
            .filter(|reference| reference.referring == name)
            .map(|reference| reference.referenced.clone())
            .collect::<Vec<_>>();
        found.sort();
        found.dedup();
        found
    };
    let inside_vocabulary = |name: &str| -> bool {
        ecology.declarations().any(|organ| {
            organ.name == name
                && organ
                    .tactic_species
                    .iter()
                    .all(|species| RENDER_VOCABULARY.contains(&species.as_str()))
        })
    };
    let mut targets = witness
        .declaration_by_generator
        .values()
        .filter(|name| !premises_of(name).is_empty() && !referrers(name).is_empty())
        .cloned()
        .collect::<Vec<_>>();
    let smallest_referrer = targets
        .iter()
        .map(|name| {
            let smallest = referrers(name)
                .into_iter()
                .map(|later| {
                    let thread = generator_thread_address(
                        witness.generator_of(&later).expect("later generator"),
                    );
                    (names_of(&session, &witness, &thread, &later).len(), later)
                })
                .min()
                .expect("a referrer");
            (name.clone(), smallest)
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    targets.sort_by_key(|name| (!inside_vocabulary(name), smallest_referrer[name].0, name.clone()));
    println!(
        "    {} targets; {} with retained tactic species inside the render vocabulary",
        targets.len(),
        targets.iter().filter(|name| inside_vocabulary(name)).count()
    );

    let mut receipts = Vec::new();
    let mut deposit: Option<(String, EventId, String, EventId, EventId)> = None;
    let mut arms = (0usize, 0usize, 0usize, 0usize);
    let mut returned_occurrence = max_occurrence + 1;
    let mut stopped_at_budget = false;
    for target in &targets {
        if began.elapsed().as_secs() > budget_seconds {
            stopped_at_budget = true;
            println!("    target iteration stopped at the declared apparatus budget");
            break;
        }
        let target_began = Instant::now();
        let premises = premises_of(target);
        let Some(problem) = theorem_problem(documents, target) else {
            continue;
        };
        let generator = witness.generator_of(target).expect("generator");
        let thread = generator_thread_address(generator);
        let occurrence = witness
            .occurrence_of(&premises[0], target)
            .expect("premise crossing");
        let boundary = match conduct(&session, thread.clone(), occurrence) {
            Ok(boundary) => boundary,
            Err(error) => {
                println!("    {target}: {error}");
                continue;
            }
        };
        let organs = names_of(&session, &witness, &thread, target);
        let (candidates, faces) = match grade(world, &ecology, &problem, &organs) {
            Ok(graded) => graded,
            Err(error) => {
                println!("    {target}: {error}");
                continue;
            }
        };
        let admitted = faces.iter().filter(|face| face.admitted).count();
        returned_occurrence += 1;
        let disposition = match derive_world_return(
            &boundary,
            &witness,
            &faces,
            EventId(returned_occurrence),
            DECLARATION_FACE,
        ) {
            Ok(disposition) => disposition,
            Err(error) => {
                println!("    {target}: derivation refused: {error}");
                continue;
            }
        };
        let termination = disposition.termination();
        let (label, junction, cone) = match &disposition {
            WorldReturnDisposition::Matched {
                junction, returned, ..
            } => (
                "matched",
                Some((junction.incident, junction.transmitted, junction.service_rounds)),
                returned.contact_support.len(),
            ),
            WorldReturnDisposition::Reflected {
                junction, returned, ..
            } => (
                "reflected",
                Some((junction.incident, junction.transmitted, junction.service_rounds)),
                returned.contact_support.len(),
            ),
            WorldReturnDisposition::Terminus(_) => ("terminus", None, 0),
        };
        match (label, termination) {
            ("matched", Termination::Halt) => arms.0 += 1,
            ("matched", _) => arms.1 += 1,
            (_, Termination::Halt) => arms.3 += 1,
            (_, _) => arms.2 += 1,
        }
        println!(
            "    {target}: premises {premises:?} candidates {candidates} admitted {admitted} obstructed {} {label} {termination:?} in {} ms",
            faces.len() - admitted,
            target_began.elapsed().as_millis()
        );
        for face in faces.iter().filter(|face| face.admitted) {
            println!("        admitted emission carried {:?}", face.carried);
        }
        let mut committed_generation = None;
        if deposit.is_none() {
            if let Some(returned) = disposition.returned() {
                let candidate = session
                    .stage_return(&boundary, returned.clone())
                    .expect("stage");
                let (next, commit) = session.commit(candidate).expect("commit");
                session = next;
                committed_generation = Some(session.generation());
                let later = smallest_referrer[target].1.clone();
                let later_occurrence = witness.occurrence_of(target, &later).expect("later crossing");
                println!(
                    "        committed generation {} with cone {}, returned occurrence {}",
                    session.generation(),
                    commit.causal_cone.len(),
                    commit.returned_occurrence.0
                );
                deposit = Some((
                    target.clone(),
                    occurrence,
                    later,
                    later_occurrence,
                    commit.returned_occurrence,
                ));
            }
        }
        receipts.push(TargetReceipt {
            target: target.clone(),
            premises,
            route_organs: organs.into_iter().collect(),
            candidates,
            admitted,
            obstructed: faces.len() - admitted,
            disposition: label.to_owned(),
            junction,
            termination: format!("{termination:?}"),
            committed_generation,
            cone,
            elapsed_millis: target_began.elapsed().as_millis(),
        });
        if committed_generation.is_some() {
            println!("    target iteration stopped at the first deposit, as declared");
            break;
        }
    }

    // The later probe. The second target is conducted on its own route (as the blueprint says)
    // and, separately, later current enters at the crossing that deposited and continues through
    // the deposited thread when it is an actual successor. Both are posed to the kernel on the
    // current, withdrawn, and replayed morphology.
    let mut probes = Vec::new();
    let mut own_differs = None;
    let mut deposit_differs = None;
    let mut replay_equals_current = None;
    let mut obstruction = None;
    if let Some((target, occurrence, later, later_occurrence, returned_occurrence)) = &deposit {
        let thread = generator_thread_address(witness.generator_of(target).expect("generator"));
        let later_thread =
            generator_thread_address(witness.generator_of(later).expect("later generator"));
        let later_problem = theorem_problem(documents, later).expect("later problem");
        let probe = |session: &NativeCirculationSession, morphology: &str| -> ProbeReceipt {
            let own_boundary = conduct(session, later_thread.clone(), *later_occurrence).expect("conduct");
            let own_reaches_deposit = own_boundary
                .actual_successors
                .iter()
                .any(|successor| successor.address.occurrence == *returned_occurrence);
            let own_route = verdict(
                world,
                &ecology,
                &later_problem,
                names_of(session, &witness, &later_thread, later),
            );
            let boundary = conduct(session, thread.clone(), *occurrence).expect("conduct");
            let deposited = boundary
                .actual_successors
                .iter()
                .find(|successor| successor.address.occurrence == *returned_occurrence)
                .cloned();
            let deposit_route = deposited.map(|successor| {
                let next = session
                    .continue_from(&boundary, &successor.address)
                    .expect("continue through the deposit");
                verdict(
                    world,
                    &ecology,
                    &later_problem,
                    names_of(session, &witness, &next.request.address.thread, later),
                )
            });
            println!(
                "    probe {later} on {morphology}: own route organs {:?} admitted {}/{} (reaches deposit {own_reaches_deposit}); deposit route reached {} {}",
                own_route.route_organs,
                own_route.admitted,
                own_route.candidates,
                deposit_route.is_some(),
                deposit_route
                    .as_ref()
                    .map(|v| format!("organs {:?} admitted {}/{}", v.route_organs, v.admitted, v.candidates))
                    .unwrap_or_default()
            );
            ProbeReceipt {
                later_target: later.clone(),
                morphology: morphology.to_owned(),
                own_route,
                deposit_route_reached: deposit_route.is_some(),
                deposit_route,
            }
        };
        let current = probe(&session, "current");
        let (withdrawn_session, commit) = session.withdraw_last_commit().expect("withdraw");
        let withdrawn = probe(&withdrawn_session, "withdrawn");
        let replayed_session = withdrawn_session.replay_commit(commit).expect("replay");
        let replayed = probe(&replayed_session, "replayed");
        own_differs = Some(current.own_route != withdrawn.own_route);
        deposit_differs = Some(current.deposit_route != withdrawn.deposit_route);
        replay_equals_current = Some(
            replayed.own_route == current.own_route
                && replayed.deposit_route == current.deposit_route,
        );
        if !current.deposit_route_reached {
            obstruction = Some("later current entering at the deposit's own crossing did not reach the deposited thread".to_owned());
        } else if current.own_route == withdrawn.own_route {
            obstruction = Some(format!(
                "the second target's own route enters at {}, not at the crossing that deposited ({}), so it never lists the deposited occurrence among its actual successors; the deposited thread is reached only by re-entering at that crossing, and its cone is a subset of the crossed thread's support, so the standing render projects the same family from either",
                later_occurrence.0, occurrence.0
            ));
        }
        probes.extend([current, withdrawn, replayed]);
        session = replayed_session;
    } else if stopped_at_budget || !receipts.is_empty() {
        obstruction = Some(format!(
            "no kernel return deposited: the standing render's {} emissions over {} targets were all reflected by the kernel inside the declared budget",
            receipts.iter().map(|r| r.candidates).sum::<usize>(),
            receipts.len()
        ));
    }
    let _ = &session;

    ArmReceipt {
        arm: arm.to_owned(),
        corpus_documents: documents.len(),
        declaration_organs: receipt.declaration_organs,
        carriers,
        threads,
        targets_total: targets.len(),
        targets: receipts,
        deposit_target: deposit.as_ref().map(|(target, ..)| target.clone()),
        probes,
        own_route_verdict_differs_current_vs_withdrawn: own_differs,
        deposit_route_verdict_differs_current_vs_withdrawn: deposit_differs,
        replay_equals_current,
        obstruction,
        arm_matched_halts: (arms.0, arms.1),
        arm_unmatched_stays_open: (arms.2, arms.3),
        arm_both_species_present: arms.0 > 0 && arms.2 > 0,
        elapsed_millis: began.elapsed().as_millis(),
    }
}

fn main() {
    let began = Instant::now();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let project_root = root.join("soma/formal/elementary-holonics");
    let corpus_root = project_root.join("ElementaryHolonics/Foundation");
    let scratch = root.join("output/wrd4");
    fs::create_dir_all(&scratch).expect("scratch");
    let world = LeanKernelWorld::new(&project_root, &scratch, KERNEL_WORKERS).expect("world");

    let foundation = collect_lean_documents(&corpus_root).expect("the Foundation corpus reads");
    let minimal = vec![LeanSourceDocument::new("wrd4/Minimal.lean", MINIMAL_CORPUS)];
    let arms = vec![
        run_arm("foundation", &foundation, &world, 45),
        run_arm("minimal", &minimal, &world, 30),
    ];
    let receipt = Receipt {
        schema: "holonics.wrd4.kernel-return-deposit.v2",
        arms,
        elapsed_millis: began.elapsed().as_millis(),
    };
    let json = serde_json::to_string_pretty(&receipt).expect("receipt");
    fs::write(scratch.join("receipt.json"), &json).expect("write receipt");

    let deposited = receipt.arms.iter().any(|arm| arm.deposit_target.is_some());
    let arms_hold = receipt
        .arms
        .iter()
        .all(|arm| arm.arm_matched_halts.1 == 0 && arm.arm_unmatched_stays_open.1 == 0);
    let replay_holds = receipt
        .arms
        .iter()
        .all(|arm| arm.replay_equals_current != Some(false));
    let both_species = receipt.arms.iter().any(|arm| arm.arm_both_species_present);
    println!("\n=== receipt");
    for arm in &receipt.arms {
        println!(
            "    {}: deposit {:?}; own-route verdict differs {:?}; deposit-route verdict differs {:?}; replay equals current {:?}; matched halts {:?}; unmatched stays open {:?}",
            arm.arm,
            arm.deposit_target,
            arm.own_route_verdict_differs_current_vs_withdrawn,
            arm.deposit_route_verdict_differs_current_vs_withdrawn,
            arm.replay_equals_current,
            arm.arm_matched_halts,
            arm.arm_unmatched_stays_open
        );
        if let Some(obstruction) = &arm.obstruction {
            println!("        obstruction: {obstruction}");
        }
    }
    println!(
        "    elapsed {} ms; deposit {deposited}; arms hold {arms_hold}; replay holds {replay_holds}; both species present {both_species}",
        receipt.elapsed_millis
    );
    if !(deposited && arms_hold && replay_holds) {
        std::process::exit(1);
    }
}
