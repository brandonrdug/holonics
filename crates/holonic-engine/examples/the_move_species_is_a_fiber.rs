//! The species of a proof move, returned as a fiber, on real mathematics.
//!
//! This is the transposition of `crates/holonic-life/examples/the_token_reconstruction_remains_a_fiber.rs`
//! from tokens to moves. There the occurrence is a token and conduct is its stream neighbours; here
//! the occurrence is a [`ProofStep`](holonic_engine::lean_development::ProofStep) and conduct is the
//! body's own **arrival graph** — a step recruiting a name an earlier step founded.
//!
//! The atlas row is the fiber. The *phases between rows, causally linked* are the refinement: which
//! axis splits which class, and the shortest word that separates what it departed.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_move_species_is_a_fiber
//! ```
//!
//! # The declared controls, and which of them can fail
//!
//! - **The common exposed face collapses everything at horizon zero.** A split there would mean the
//!   reading is consuming something it was not handed. *Must hold.*
//! - **A refinement is a subset.** A member appearing under the richer family and absent under the
//!   coarse one is not a refinement of anything. *Must hold.*
//! - **Relabelling every founding tactic moves no block.** It cannot fail here and the module says
//!   why; it is run because the centrifuge failed exactly this control at 11 of 13 boundaries when
//!   its transport read bytes rather than identity. *Must hold.*
//! - **The causal panel is not the spelling panel.** If they agree, the causal axes added nothing
//!   and the species is the tactic's name in other clothes. *Can fail, and is the point.*
//! - **The crossing arm is reported and not graded.** Two subject-disjoint areas are read and their
//!   partition profiles compared. Agreement is **not** a defect here: an atlas of *invariant*
//!   transport patterns predicts that species recur across subjects. It is reported as a
//!   measurement so a later reading can use it, and graded by nothing.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::lean_development::{BinderGrain, DeclarationGrain, read_development_at};
use holonic_engine::move_species::{
    MoveAxis, MoveComplex, MoveDeclaration, MoveFamily, MoveOccurrence, MoveSpeciesFiber,
    MoveWorkCover, move_demand, refine_species, species_fiber,
};

/// Two areas of the library that share no subject. Both are read; the first carries the deed.
const AREAS: [(&str, &str); 2] = [
    ("geometry", "Mathlib/Geometry/Euclidean/Triangle.lean"),
    ("set theory", "Mathlib/SetTheory/Cardinal/Cofinality.lean"),
];

struct Failures(Vec<String>);

impl Failures {
    fn require(&mut self, held: bool, claim: &str) {
        println!("    [{}] {claim}", if held { "holds" } else { "FAILS" });
        if !held {
            self.0.push(claim.to_owned());
        }
    }
}

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the repository root")
        .to_path_buf()
}

fn material_root(root: &Path) -> PathBuf {
    root.join("formal/elementary-holonics/.lake/packages/mathlib")
}

fn found(root: &Path, relative: &str, binders: BinderGrain) -> Option<MoveComplex> {
    let text = fs::read_to_string(material_root(root).join(relative)).ok()?;
    let reading = read_development_at(&text, DeclarationGrain::EveryTopLevelDeclaration, binders);
    Some(MoveComplex::found(&reading.declarations))
}

/// Block sizes over the candidate roots, sorted — the strata, with no identity attached.
fn profile(fiber: &MoveSpeciesFiber) -> (usize, usize, usize) {
    (
        fiber.one_shot_blocks,
        fiber.conduct_blocks,
        fiber.memory_order,
    )
}

fn report(label: &str, fiber: &MoveSpeciesFiber) {
    println!(
        "    {label:11} {:38} species {:2} of {:2} · blocks one-shot {} conduct {} · order {}",
        fiber.family.label(),
        fiber.fiber.len(),
        fiber.demand.roots,
        fiber.one_shot_blocks,
        fiber.conduct_blocks,
        fiber.memory_order
    );
}

fn main() {
    let mut failures = Failures(Vec::new());
    let root = repository_root();

    println!("THE MOVE SPECIES IS A FIBER");
    println!("  material  {}", material_root(&root).display());
    if !material_root(&root).exists() {
        println!("  the library is not materialised here; nothing to read.");
        println!("  recover it with:  cd formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }

    // ---------------------------------------------------------------- the binder aperture's orbit
    println!("\n=== the binder aperture, and what it costs");
    println!(
        "    `BinderGrain` was declared 2026-08-14. It was an unconditional filter before, and"
    );
    println!("    a filter whose orbit is unmeasured is not an aperture. Both grains, same text:");
    for (subject, relative) in AREAS {
        let mut row = format!("    {subject:11} {relative:52}");
        for binders in [BinderGrain::MultiCharacter, BinderGrain::EveryBinder] {
            match found(&root, relative, binders) {
                Some(complex) => row.push_str(&format!(
                    "  {:?}: moves {:3} arrivals {:3} aperture {}",
                    binders,
                    complex.moves(),
                    complex.arrivals(),
                    complex.branch_aperture()
                )),
                None => row.push_str("  (absent)"),
            }
        }
        println!("{row}");
    }

    // ---------------------------------------------------------------- the deed
    let (subject, relative) = AREAS[0];
    let Some(complex) = found(&root, relative, BinderGrain::EveryBinder) else {
        println!("\n  the deed's area is absent: {relative}");
        std::process::exit(2);
    };
    println!("\n=== the material the deed runs on — {subject}, {relative}");
    println!(
        "    moves {} · arrivals {} · branch aperture {} · founding tactics {}",
        complex.moves(),
        complex.arrivals(),
        complex.branch_aperture(),
        complex.formers()
    );

    // The candidate population is **every move this area founds**, in canonical order. It is not
    // a hand-picked set: an authored population would make the fiber a restatement of the choosing.
    let candidates: Vec<MoveOccurrence> = complex.occurrences().collect();
    if candidates.len() < 2 {
        println!("    fewer than two moves; there is no fiber to take");
        std::process::exit(2);
    }
    let isolated = complex.isolated();
    let connected = complex.connected();
    let unconsumed = complex.unconsumed();
    println!(
        "    candidates {} · isolated {} · connected {} · UNCONSUMED {}",
        candidates.len(),
        isolated.len(),
        connected.len(),
        unconsumed.len()
    );
    println!(
        "    `isolated` means no later STEP arrives. `unconsumed` means nothing names it at all —"
    );
    println!(
        "    the closing term is not a step, so the two differ by {} moves the final tactic uses.",
        isolated.len() - unconsumed.len()
    );
    println!("    THE ISOLATED POPULATION IS ITSELF A ROW: the moves no later step arrives at.");
    println!(
        "    They present only the common exposed face, so no family can separate them and a focus"
    );
    println!(
        "    taken from them returns one block under every family. That is a property of the focus"
    );
    println!("    and not of the receiver, so the focus below is taken from the CONNECTED moves.");

    // Canonically the first move conduct can reach something from. Declared, not chosen: the rule
    // is stated and the material decides which occurrence satisfies it.
    let Some(&focus) = connected.first() else {
        println!("    no move in this area has an arrival; there is no conduct to read");
        std::process::exit(2);
    };
    let (down, up) = complex.reach(focus).unwrap_or((0, 0));
    println!(
        "    focus {focus:?} founded by `{}` · downstream {down} upstream {up}",
        complex.former_label(focus).unwrap_or("?")
    );

    let declare = |family: MoveFamily, horizon: usize| MoveDeclaration {
        candidates: candidates.clone(),
        family,
        horizon,
    };
    let demand = move_demand(&complex, &declare(MoveFamily::FULL, 1));
    println!(
        "    demand at horizon 1: roots {} · slots {} · items {} · pair chart {}",
        demand.roots, demand.slots, demand.items, demand.pair_chart
    );
    let cover = MoveWorkCover::exactly(&demand);

    // ---------------------------------------------------------------- the readings
    println!("\n=== the fiber, at four declared families");
    let mut readings = Vec::new();
    for family in [
        MoveFamily::of([MoveAxis::Ascribed]),
        MoveFamily::CAUSAL,
        MoveFamily::SPELLING,
        MoveFamily::FULL,
    ] {
        match species_fiber(&complex, focus, &declare(family, 1), &cover) {
            Ok(fiber) => {
                report(
                    match family {
                        f if f == MoveFamily::SPELLING => "spelling",
                        f if f == MoveFamily::CAUSAL => "causal",
                        f if f == MoveFamily::FULL => "full",
                        _ => "coarse",
                    },
                    &fiber,
                );
                readings.push((family, fiber));
            }
            Err(error) => println!("    {} refused: {error:?}", family.label()),
        }
    }

    // ---------------------------------------------------------------- the refinement
    println!("\n=== the refinement — what the causal axes departed, and its witness");
    match refine_species(
        &complex,
        focus,
        &declare(MoveFamily::of([MoveAxis::Ascribed]), 1),
        &declare(MoveFamily::CAUSAL, 1),
        &cover,
    ) {
        Ok(refinement) => {
            println!(
                "    coarse species {} -> richer species {} · departed {} · witnesses {}",
                refinement.coarse.fiber.len(),
                refinement.richer.fiber.len(),
                refinement.departed.len(),
                refinement.witnesses
            );
            for departed in refinement.departed.iter().take(8) {
                println!(
                    "      departed {:?} founded by `{}`",
                    departed,
                    complex.former_label(*departed).unwrap_or("?")
                );
            }
            if refinement.departed.len() > 8 {
                println!("      … and {} more", refinement.departed.len() - 8);
            }
            let subset = refinement
                .richer
                .fiber
                .iter()
                .all(|member| refinement.coarse.fiber.contains(member));
            failures.require(
                subset,
                "the richer family's species is a subset of the coarse one",
            );
            if !refinement.moved() {
                println!(
                    "    the causal axes departed nothing here, so on THIS material they see \
                     nothing the ascription axis did not"
                );
            }
        }
        Err(error) => {
            println!("    refused: {error:?}");
            failures.require(false, "the refinement returns");
        }
    }

    // ---------------------------------------------------------------- the controls
    println!("\n=== the declared controls");

    let horizon_zero = species_fiber(&complex, focus, &declare(MoveFamily::FULL, 0), &cover)
        .expect("horizon zero returns");
    failures.require(
        horizon_zero.fiber.len() == candidates.len() && horizon_zero.conduct_blocks == 1,
        "the common exposed face collapses every candidate at horizon zero",
    );

    let renamed = complex.with_renamed_formers(|former| format!("zzz-{former}"));
    let before = species_fiber(&complex, focus, &declare(MoveFamily::FULL, 1), &cover)
        .expect("before returns");
    let after = species_fiber(&renamed, focus, &declare(MoveFamily::FULL, 1), &cover)
        .expect("after returns");
    failures.require(
        before.fiber == after.fiber && before.conduct_blocks == after.conduct_blocks,
        "relabelling every founding tactic moves no block",
    );

    // **The panels are compared as PARTITIONS, not as one focus's fiber.**
    // Until 2026-08-14 this compared `fiber` against `fiber`, and on a repaired reader the focus's
    // fiber is a singleton under both panels — so the comparison returned "equal" and the control
    // failed while the partitions plainly differed. A comparison whose material cannot vary the
    // property under test is the defect this project convicts, and a fiber of one cannot vary it.
    let panel = |wanted: MoveFamily| {
        readings
            .iter()
            .find(|(family, _)| *family == wanted)
            .map(|(_, fiber)| (fiber.root_partition.clone(), fiber.fiber.clone()))
    };
    match (panel(MoveFamily::SPELLING), panel(MoveFamily::CAUSAL)) {
        (Some((spelling, spelling_fiber)), Some((cause, cause_fiber))) => {
            println!(
                "    partitions: spelling {} blocks · causal {} blocks",
                spelling.len(),
                cause.len()
            );
            failures.require(
                spelling != cause,
                "the causal panel is not the spelling panel, compared as PARTITIONS",
            );
            if spelling_fiber.len() == 1 && cause_fiber.len() == 1 {
                println!(
                    "    the focus's own fiber is a singleton under both panels, so it is \
                     UNDETERMINED there and is reported rather than graded"
                );
            } else {
                println!(
                    "    the focus's fiber: spelling {} · causal {} · {}",
                    spelling_fiber.len(),
                    cause_fiber.len(),
                    if spelling_fiber == cause_fiber {
                        "AGREE"
                    } else {
                        "differ"
                    }
                );
            }
        }
        _ => failures.require(false, "both panels returned"),
    }

    // ---------------------------------------------------------------- the crossing arm
    println!("\n=== the crossing arm — reported, graded by nothing");
    println!("    An atlas of INVARIANT transport patterns predicts that species recur across");
    println!("    subjects, so agreement here is evidence for the atlas and not against it. The");
    println!("    profile is (one-shot blocks, conduct blocks, memory order) over each area's own");
    println!("    candidate population.");
    let mut profiles = Vec::new();
    for (subject, relative) in AREAS {
        let Some(area) = found(&root, relative, BinderGrain::EveryBinder) else {
            continue;
        };
        let area_candidates: Vec<MoveOccurrence> = area.occurrences().collect();
        if area_candidates.len() < 2 {
            continue;
        }
        let area_declaration = MoveDeclaration {
            candidates: area_candidates.clone(),
            family: MoveFamily::CAUSAL,
            horizon: 1,
        };
        let area_cover = MoveWorkCover::exactly(&move_demand(&area, &area_declaration));
        match species_fiber(&area, area_candidates[0], &area_declaration, &area_cover) {
            Ok(fiber) => {
                println!(
                    "    {subject:11} candidates {:3} · profile {:?} · species of its first move {}",
                    area_candidates.len(),
                    profile(&fiber),
                    fiber.fiber.len()
                );
                profiles.push((subject, profile(&fiber)));
            }
            Err(error) => println!("    {subject:11} refused: {error:?}"),
        }
    }
    if let [(first, left), (second, right)] = profiles.as_slice() {
        println!(
            "    {first} and {second} profiles {}",
            if left == right {
                "AGREE — the same strata on disjoint subjects"
            } else {
                "DIFFER"
            }
        );
    }

    // ---------------------------------------------------------------- the return
    println!("\n=== the return");
    let distinct: BTreeSet<usize> = readings
        .iter()
        .map(|(_, fiber)| fiber.conduct_blocks)
        .collect();
    println!(
        "    four families returned {} distinct block counts over one population",
        distinct.len()
    );
    println!(
        "    the species is the block, and its identity is its population plus the family that \
         could not separate it"
    );

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
