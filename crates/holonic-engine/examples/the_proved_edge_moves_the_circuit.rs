//! The kernel-proved edge deposited into the **standing** circuit, and what it moves there.
//!
//! `the_recognition_precedes_the_run` returned four kernel-proved edges as a printed list. That was
//! a new organ beside an existing owner: [`crate::derivation_atlas`] already reads deposited
//! derivations as a circuit — a `GradedCausalComplex` with vertices, recruitment and reach 1-cells,
//! spanning forest, routes and cycle agreement — and already carries `invariant_movement` and
//! `route_movement` for reading one circuit against another.
//!
//! **A proved edge is a derivation.** So the honest return is not a list; it is the circuit before
//! the proof and the circuit after it, and the movement between them measured by the owner that
//! exists for the purpose.
//!
//! ```text
//!   before   the corpus's own declarations, read as a circuit
//!   after    the same, plus the theorem the kernel admitted, recruiting the node it applied
//!   moved    invariant_movement + route_movement
//! ```
//!
//! # Why this is not the same as counting edges
//!
//! A route is a composition of 1-cells, and a cycle is a route that closes. Adding one proved edge
//! can open a route that did not exist, close a cycle, or move an integer invariant of the complex —
//! and none of those is visible in a list of four proofs. What the atlas is *for* is the routes.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_proved_edge_moves_the_circuit
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{
    CircuitAperture, Derivation, DerivationCircuit, DerivationIdentity, ReachOrientation,
    RecruitmentCoefficient, StatementIncidence, found_circuit, invariant_movement, route_movement,
};
use holonic_engine::lean_development::{
    BinderGrain, ConductGrain, DeclarationGrain, read_development_at,
};
use holonic_engine::rebase_invariants::PivotRule;

const PROJECT: &str = "soma/formal/rh-source-transport";
const CORPUS: &str = "SomaRHSourceTransport/FiniteTransport.lean";

/// The theorem the kernel admitted, and the node its proof applied. Both are returns of
/// `the_recognition_precedes_the_run`, not choices made here.
const PROVED: &str = "receiver_load_under_capacity";
const APPLIED: &str = "proportionalFlow_respects_capacity";

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the repository root")
        .to_path_buf()
}

fn report(label: &str, circuit: &DerivationCircuit) {
    println!(
        "  {label:8} vertices {:3}   recruitment 1-cells {:3}   reach 1-cells {:3}   routes {:3}",
        circuit.vertices().len(),
        circuit.recruitments().len(),
        circuit.reaches().len(),
        circuit.routes().len()
    );
}

fn main() {
    let root = repository_root();
    let corpus = root.join(PROJECT).join(CORPUS);
    println!("THE PROVED EDGE MOVES THE CIRCUIT");
    let Ok(text) = std::fs::read_to_string(&corpus) else {
        println!("  the corpus is absent: {}", corpus.display());
        std::process::exit(2);
    };
    let reading = read_development_at(
        &text,
        DeclarationGrain::EveryTopLevelDeclaration,
        BinderGrain::EveryBinder,
    );
    let before_derivations = reading.derivations(ConductGrain::TermsOnly);
    println!(
        "\n  the corpus reads {} declarations",
        before_derivations.len()
    );

    // The proved edge, as a derivation: the theorem the kernel admitted, recruiting the node its
    // proof applied. Nothing here is invented — both names are returns of the recognition run.
    let mut recruited = BTreeMap::new();
    recruited.insert(APPLIED.to_owned(), 1u32);
    let proved = Derivation {
        name: PROVED.to_owned(),
        statement: format!(
            "(∑ n : Old, proportionalFlow demand capacity incident n m) ≤ capacity m"
        ),
        recruited,
    };
    let mut after_derivations = before_derivations.clone();
    after_derivations.push(proved);

    // Both orientations, because the reach axis was recovered on 2026-08-14 and a reading taken at
    // one orientation is a reading at one frame.
    for reach in [
        ReachOrientation::IntoDerivation,
        ReachOrientation::OutOfDerivation,
    ] {
        let aperture = CircuitAperture {
            identity: DerivationIdentity::ByDeclaration,
            coefficient: RecruitmentCoefficient::Incidence,
            reach,
            statements: StatementIncidence::Founded,
        };
        println!("\n=== reach {reach:?}");
        let before = match found_circuit(&before_derivations, aperture) {
            Ok(circuit) => circuit,
            Err(refusal) => {
                println!("  the circuit refused before: {refusal:?}");
                continue;
            }
        };
        let after = match found_circuit(&after_derivations, aperture) {
            Ok(circuit) => circuit,
            Err(refusal) => {
                println!("  the circuit refused after: {refusal:?}");
                continue;
            }
        };
        report("before", &before);
        report("after", &after);

        // The invariants are the circuit's own — Betti numbers and torsion of the graded complex,
        // computed by `rebase_invariants` under a declared pivot rule.
        let routes = route_movement(&before, &after);
        match (
            before.invariants(PivotRule::FirstNonzero),
            after.invariants(PivotRule::FirstNonzero),
        ) {
            (Ok(before_invariants), Ok(after_invariants)) => {
                let moved = invariant_movement(&before_invariants, &after_invariants);
                println!("\n  what the proved edge moved:");
                println!("    invariants still  {}", moved.is_still());
                println!("    fields moved      {:?}", moved.fields_moved());
            }
            (before_result, after_result) => {
                println!("\n  the invariants refused: {before_result:?} / {after_result:?}");
            }
        }
        println!("    routes            {routes:?}");
    }

    println!("\n  A route is a composition of 1-cells and a cycle is a route that closes. This is");
    println!("  what an atlas is FOR, and none of it is visible in a list of four proofs.");
}
