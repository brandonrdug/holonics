//! THE TOWER CLIMBS — a rung composes, the ladder ascends, and what survives is measured.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_tower_climbs
//! ```
//!
//! ## What this closes
//!
//! `contact_gluing.rs` carried eleven organs of the hypergeometry tower and **two were driven**.
//! `Corner`, `ContactTriangle`, `EuclideanRealization`, `contact_triangles`, `coarse_grain`,
//! `CoarseTurn`, `contact_graph`, `ride_circuit` and `Circuit` returned zero hits across every
//! `examples/` directory, and the figures their doc comments cite lived only in `#[cfg(test)]`.
//!
//! Worse, the rung could not compose. `Corner::sine` was `Option<Rat>`, and only a Pythagorean
//! corner has a rational sine — the equilateral corner already needs `√3/2` — so `coarse_grain`
//! returned `Open` on essentially every real triangle, **including the tower's own headline case**.
//! `CoarseTurn::Open`'s doc named the missing carrier and said it was one quadratic extension. It is
//! not: three corners contribute three roots, so the field is `ℚ(√d₁,√d₂,√d₃)` — *multiquadratic*,
//! degree up to `2³`. `crate::multiquadratic` supplies it as the twisted group algebra of `(ℤ/2)ⁿ`.
//!
//! ## The receiver question
//!
//! **Does the tower climb, and what survives a rung?**
//!
//! The second half is the part that matters. `CLAUDE.md` §8: a gauge must exhibit its own orbit, and
//! a wave of construction reporting no movement anywhere has done bookkeeping. So this driver does
//! **not** assume that any quantity is preserved by coarse graining. It climbs, then compares the
//! ranks and reports which quantities moved and which did not — including the ones that moved
//! against expectation.
//!
//! ## The apertures, declared
//!
//! ```text
//!   generators     12 distinct squarefree kernels per composed turn. The multiquadratic basis is
//!                  2^n wide, so this bounds a real resource; exceeding it is refused by name.
//!   kernel bound   `multiquadratic::DECLARED_KERNEL_BOUND`, the trial-division bound for
//!                  squarefree extraction. Beyond it a kernel is refused, never guessed.
//!   material       the atmosphere below, declared inline. Small and stated, so every figure here
//!                  is reproducible by reading this file.
//! ```

use std::collections::BTreeSet;

use holonic_engine::conditioned_derivation::{Exposure, FoundedMorphology, expose};
use holonic_engine::contact_gluing::{
    CoarseTurn, ContactTriangle, EuclideanRealization, climb, coarse_grain, contact_graph,
    contact_triangles, corners_from_weights, realization_of,
};
use holonic_engine::multiquadratic::Multiquadratic;
use num_bigint::BigInt;
use num_traits::Zero;

/// APERTURE — distinct squarefree generators one composed turn may carry. Declared by this caller.
const GENERATOR_APERTURE: usize = 12;

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn render(value: &Multiquadratic) -> String {
    if let Some(rational) = value.as_rational() {
        return format!("{rational}");
    }
    let generators = value.generators();
    let mut terms = Vec::new();
    for (mask, coefficient) in value.coefficients().iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let mut roots = Vec::new();
        for (bit, generator) in generators.iter().enumerate() {
            if mask & (1usize << bit) != 0 {
                roots.push(format!("√{generator}"));
            }
        }
        if roots.is_empty() {
            terms.push(format!("{coefficient}"));
        } else {
            terms.push(format!("{coefficient}·{}", roots.join("·")));
        }
    }
    terms.join(" + ")
}

/// The declared material.
///
/// **Chosen so the law can fail.** The first corpus tried here produced exactly one triangle, and
/// it was equilateral — every corner `cos = 1/2`, every composed turn rational — so the
/// multiquadratic field was never exercised and the ladder had one rank-1 vertex, which cannot form
/// a rank-2 triangle. Two declared controls failed on it and they were right to.
///
/// This corpus is built to make scalene triangles: word families sharing stems of *different*
/// lengths. A 7-7-8 triangle has apex cosine `(49+49−64)/98 = 17/49`, hence
/// `sin = √(2112)/49 = 8√33/49` — irrational, generator 33. That is the case the field exists for.
fn atmosphere() -> Vec<(String, String)> {
    [
        (
            "carriage",
            "the carriage carries the charge and the carrier carries the carriage",
        ),
        (
            "carrier",
            "the carrier carries the charge the carriage carried",
        ),
        (
            "carries",
            "the carries of the carriage carry the charge the carrier carries",
        ),
        (
            "charges",
            "the charges charge the carriage and the charges charge the carrier",
        ),
        (
            "charged",
            "the charged carriage charged the charged carrier with charges",
        ),
        (
            "charger",
            "the charger charges the charged carrier and the charger charges",
        ),
        (
            "discharge",
            "the discharge discharges the charged carriage and the charger",
        ),
        (
            "recharge",
            "the recharge recharges the charger and the charged carrier",
        ),
        (
            "conductor",
            "the conductor conducts the charge the carriage carried",
        ),
        (
            "conducted",
            "the conducted charge conducted the conductor and the carrier",
        ),
        (
            "conduction",
            "the conduction of the conducted charge conducts the conductor",
        ),
        (
            "transport",
            "the transport transports the charge the conductor conducted",
        ),
        (
            "transporter",
            "the transporter transports the transported charge and the transport",
        ),
        (
            "transported",
            "the transported charge transports the transporter and the conductor",
        ),
        (
            "transpose",
            "the transpose transposes the transported charge and the transport",
        ),
        (
            "transposed",
            "the transposed transpose transposed the transporter and the transport",
        ),
        (
            "port",
            "the port ports the charge and the transport ports the carrier",
        ),
        (
            "ported",
            "the ported charge ported the port and the transporter ported",
        ),
        (
            "porter",
            "the porter ports the ported charge and the transporter ports",
        ),
        (
            "charter",
            "the charter charters the charge and the charger charters the porter",
        ),
        (
            "chartered",
            "the chartered charter chartered the charger and the ported charge",
        ),
    ]
    .into_iter()
    .map(|(identity, text)| (identity.to_owned(), text.to_owned()))
    .collect()
}

fn main() {
    let mut failures: Vec<String> = Vec::new();
    // A falsifier that is DECLARED to fail while a defect stands is reported and does not gate.
    // A control that fails says the reading is untrustworthy; a declared falsifier that fails says
    // the defect it names is still there. The same separation the iron-tokens driver makes between
    // controls and predictions.
    let mut open_falsifiers: Vec<(String, String)> = Vec::new();
    let mut hold = |claim: &str, held: bool, evidence: String| {
        if held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            println!("  [FAILS] {claim}\n            {evidence}");
            failures.push(claim.to_owned());
        }
    };

    rule("THE MATERIAL — declared inline, so every figure below is reproducible");

    let material = atmosphere();
    let exposures: Vec<Exposure> = material
        .iter()
        .map(|(identity, text)| expose(identity, text))
        .collect();
    let morphology = FoundedMorphology::condition(&exposures);
    let population: Vec<String> = material
        .iter()
        .map(|(identity, _)| identity.clone())
        .collect();
    println!("  words          {}", population.len());
    println!("  stems founded  {}", morphology.founded().len());
    println!("  stems committed{:>3}", morphology.committed_stems().len());

    // ---------------------------------------------------------------------------------------------

    rule("RANK 0 — the contact graph, where the cycles actually are");

    let graph = match contact_graph(&morphology, &population) {
        Ok(graph) => graph,
        Err(refusal) => {
            println!("  the contact graph refused: {refusal:?}");
            std::process::exit(1);
        }
    };
    println!("  vertices (identifiers) {}", graph.identifiers.len());
    println!("  arcs (shared stems)    {}", graph.arcs.len());

    let triangles = contact_triangles(&graph);
    let realized: Vec<&ContactTriangle> = triangles
        .iter()
        .filter(|t| t.euclidean == EuclideanRealization::Realized)
        .collect();
    println!(
        "  triangles              {} ({} realizable)",
        triangles.len(),
        realized.len()
    );
    let mut weight_shapes: BTreeSet<Vec<BigInt>> = BTreeSet::new();
    for triangle in &realized {
        let mut sides = triangle.weights.clone().to_vec();
        sides.sort();
        weight_shapes.insert(sides);
    }
    println!("  distinct weight shapes {:?}", weight_shapes);

    hold(
        "the material closes triangles at all — a tower over an acyclic graph would be vacuous",
        !realized.is_empty(),
        format!(
            "{} realizable triangles over {} identifiers",
            realized.len(),
            graph.identifiers.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE RUNG — and the finding, which is that composing THREE corners is vacuous");

    let mut exact = 0usize;
    let mut refused = 0usize;
    let mut composed_shapes: BTreeSet<String> = BTreeSet::new();
    let mut corner_generators: BTreeSet<BigInt> = BTreeSet::new();
    let mut irrational_corners = 0usize;
    let mut sample: Vec<String> = Vec::new();

    for triangle in &realized {
        // The CORNERS are where the field lives.
        for corner in &triangle.corners {
            match &corner.sine {
                Ok(sine) => {
                    if sine.as_rational().is_none() {
                        irrational_corners += 1;
                        for generator in sine.generators() {
                            corner_generators.insert(generator.clone());
                        }
                        if sample.len() < 4 {
                            let mut sides = triangle.weights.clone().to_vec();
                            sides.sort();
                            sample.push(format!(
                                "  {:<28} sides {:?}  cos = {:<10} sin = {}",
                                triangle.identifiers.join("+"),
                                sides,
                                corner.cosine,
                                render(sine)
                            ));
                        }
                    }
                }
                Err(refusal) => println!("  corner at {} REFUSED {refusal:?}", corner.at),
            }
        }
        match coarse_grain(triangle) {
            CoarseTurn::Exact { cosine, sine } => {
                exact += 1;
                composed_shapes.insert(format!("({}, {})", render(&cosine), render(&sine)));
            }
            CoarseTurn::Refused { refusals } => {
                refused += 1;
                println!(
                    "  {:<28} REFUSED {refusals:?}",
                    triangle.identifiers.join("+")
                );
            }
            CoarseTurn::NotRealizable { .. } => {}
        }
    }

    println!("  corners carrying a generator: {irrational_corners}");
    println!("  generators the corners found: {corner_generators:?}");
    for line in &sample {
        println!("{line}");
    }

    hold(
        "the FIELD is exercised: some corner's sine is irrational and names its generator",
        irrational_corners > 0 && !corner_generators.is_empty(),
        format!(
            "{irrational_corners} irrational corners over generators {corner_generators:?}; \
             before 2026-08-10 every one of these was `None` and the rung could not compose"
        ),
    );
    hold(
        "every realizable triangle composes exactly, with no refusal",
        refused == 0 && exact == realized.len(),
        format!(
            "{exact} exact, {refused} refused, of {} realizable",
            realized.len()
        ),
    );

    println!();
    println!(
        "  distinct composed turns over all {exact} realizable triangles: {composed_shapes:?}"
    );
    println!();
    println!(
        "  **THE FINDING.** Every realizable triangle composes to the SAME turn, and it must:"
    );
    println!("  a planar triangle's angles sum to π, so the product of its three corner turns is");
    println!(
        "  e^{{iπ}} = (−1, 0) identically. `coarse_grain` composes all three corners, so as a"
    );
    println!(
        "  rung it returns a constant — `CLAUDE.md` §8's receipt that could not have come out"
    );
    println!(
        "  otherwise. The angle-sum identity is real mathematics and the rung is real code, and"
    );
    println!("  the defect is that the rung was specified to compute the one product that is a");
    println!("  theorem rather than a reading of the material.");
    println!();
    println!("  Brandon's own statement of the object says what the rung should be: *the tower is");
    println!(
        "  the INTERACTION, a Feynman vertex A,B→C, C relative to the {{A,B}} frame*. A vertex"
    );
    println!("  is TWO in and ONE out. Composing two corners and returning the third relative to");
    println!("  them is the Law of Cosines' actual content and is not constant. That is a theory");
    println!("  decision, not a patch, and it is left open here rather than guessed at.");

    hold(
        "the vacuity is exhibited rather than hidden: the composed turn takes exactly one value",
        composed_shapes.len() == 1,
        format!(
            "{} distinct composed turn(s) over {exact} triangles with {} distinct weight shapes — \
             a rung whose output cannot vary with its input is carrying nothing",
            composed_shapes.len(),
            weight_shapes.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE LADDER — climbing, and what the climb does to the material");

    let rank_one = climb(1, &triangles, GENERATOR_APERTURE);
    println!(
        "  rank 1: {} vertices, {} arcs, {} unrealizable retained, generators {:?}",
        rank_one.vertices.len(),
        rank_one.arcs.len(),
        rank_one.unrealizable.len(),
        rank_one.generators
    );

    // A rank is itself a graph, so the next rung is read by the SAME law: `corners_from_weights`
    // and `realization_of` are the rank-0 reading, reused verbatim. A tower whose upper ranks read
    // corners differently would not be a tower.
    let names: Vec<String> = rank_one
        .vertices
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let mut rank_two_triangles: Vec<ContactTriangle> = Vec::new();
    for (i, a) in names.iter().enumerate() {
        for (j, b) in names.iter().enumerate().skip(i + 1) {
            for c in names.iter().skip(j + 1) {
                let edge = |x: &String, y: &String| {
                    rank_one
                        .arcs
                        .iter()
                        .find(|(l, r, _, _)| (l == x && r == y) || (l == y && r == x))
                        .map(|(_, _, stem, weight)| (stem.clone(), weight.clone()))
                };
                let (Some(ab), Some(bc), Some(ca)) = (edge(a, b), edge(b, c), edge(c, a)) else {
                    continue;
                };
                let weights = [&ab.1, &bc.1, &ca.1];
                rank_two_triangles.push(ContactTriangle {
                    euclidean: realization_of(weights),
                    identifiers: [a.clone(), b.clone(), c.clone()],
                    stems: [ab.0.clone(), bc.0.clone(), ca.0.clone()],
                    corners: corners_from_weights(
                        [a.as_str(), b.as_str(), c.as_str()],
                        [ab.0.as_str(), bc.0.as_str(), ca.0.as_str()],
                        weights,
                    ),
                    weights: [ab.1.clone(), bc.1.clone(), ca.1.clone()],
                    composes_exactly: false,
                });
            }
        }
    }
    let rank_two = climb(2, &rank_two_triangles, GENERATOR_APERTURE);
    println!(
        "  rank 2: {} candidate triangles -> {} vertices, {} arcs, generators {:?}",
        rank_two_triangles.len(),
        rank_two.vertices.len(),
        rank_two.arcs.len(),
        rank_two.generators
    );

    hold(
        "the ladder climbs at least two rungs — one rung is a rule, two is a tower",
        !rank_one.vertices.is_empty() && !rank_two_triangles.is_empty(),
        format!(
            "rank 1 has {} vertices; rank 2 read {} candidate triangles over them",
            rank_one.vertices.len(),
            rank_two_triangles.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHAT SURVIVES — measured, not assumed");

    let rank_zero_generators: BTreeSet<BigInt> = realized
        .iter()
        .filter_map(|t| match coarse_grain(t) {
            CoarseTurn::Exact { cosine, sine } => Some(
                cosine
                    .generators()
                    .iter()
                    .chain(sine.generators())
                    .cloned()
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();
    let rank_one_generators: BTreeSet<BigInt> = rank_one.generators.iter().cloned().collect();

    println!("  rank 0 generator population {:?}", rank_zero_generators);
    println!("  rank 1 generator population {:?}", rank_one_generators);

    println!();
    println!("  Both populations are EMPTY, and that is the same finding one level up: the rung's");
    println!("  output is always (−1, 0), which is rational, so no generator ever reaches a rank");
    println!(
        "  above rank 0. The corners carry {} generators between them and the climb carries",
        corner_generators.len()
    );
    println!("  none of them. A control asserting `rank 1 retains rank 0's generators` would hold");
    println!("  on two empty sets and prove nothing, so it is not asserted.");

    println!();
    println!(
        "  ANSWERED 2026-08-10, and not by a new carrier. A planar triangle's angles sum to π,"
    );
    println!("  so composing ONE simplex's own three corners is constant BY HYPOTHESIS — that is");
    println!("  Regge calculus' founding assumption, every simplex flat and all curvature");
    println!("  concentrated on the codimension-two hinges BETWEEN them. Under CLAUDE.md §8 the");
    println!("  (−1,0) receipt is `definition`-grade: it could not have come out otherwise.");
    println!("  The object that carries curvature is the HINGE: one corner from each incident");
    println!(
        "  triangle, deficit = 2π − Σθ. Measured by `the_hinge_carries_the_curvature` on this"
    );
    println!("  same material: 5 distinct hinge turns over 11 hinges against 1 over 25 triangles,");
    println!("  generators {{3, 7, 1463}} reached, and 6 of 11 hinges moving under a non-similar");
    println!("  metric while 0 move under a similarity.");
    println!("  See canon/TABLET_THE_TURN.md §11.5 and the 2026-08-10 manifold record.");

    open_falsifiers.push((
        "the climb carries the corners' generators upward".to_owned(),
        format!(
            "rank 0 corners found {corner_generators:?}; rank 1 carries {rank_one_generators:?}. \
             Still empty, and now EXPLAINED rather than open: the per-simplex rung is constant by \
             Regge's flatness hypothesis, so no generator can survive it. This line is retained as \
             provenance. The live falsifier moved to the hinge and is driven by \
             `the_hinge_carries_the_curvature`."
        ),
    ));

    let accumulated = rank_one.accumulated_turn(GENERATOR_APERTURE);
    match &accumulated {
        Some((cosine, sine)) => println!(
            "  rank 1 accumulated turn      cos = {}   sin = {}",
            render(cosine),
            render(sine)
        ),
        None => println!("  rank 1 accumulated turn      OPEN — a vertex did not compose"),
    }
    hold(
        "the rank composes an accumulated turn at all, so there is something for a climb to move",
        accumulated.is_some(),
        format!(
            "{} of {} rank-1 vertices exact",
            rank_one.exact_vertices(),
            rank_one.vertices.len()
        ),
    );

    rule("BOUNDS");
    println!("  - The rank-1 graph is built from shared stems and NOTHING is declared: the arcs'");
    println!("    weights are the shared stems' own weights, so no new level enters at any rank.");
    println!("  - **No invariance across ranks is claimed.** This driver reports the generator");
    println!(
        "    populations and the accumulated turn per rank; whether any quantity is PRESERVED"
    );
    println!("    by a climb is a further measurement and is not made here.");
    println!(
        "  - The declared generator aperture is {GENERATOR_APERTURE}; the basis is 2^n wide and"
    );
    println!("    exceeding it is refused by name rather than held.");
    println!(
        "  - One material, small and stated. A tower over other material may refuse where this"
    );
    println!("    one composes, and that would be a real return about the material.");

    println!();
    println!("DECLARED FALSIFIERS — reported, never gating");
    println!("---------------------------------------------");
    for (claim, evidence) in &open_falsifiers {
        let met = !rank_one_generators.is_empty();
        println!(
            "  [{}] {claim}\n            {evidence}",
            if met { "MET  " } else { "OPEN " }
        );
    }

    println!();
    if failures.is_empty() {
        println!("HELD — every declared control");
    } else {
        println!("FAILED — {} control(s): {failures:?}", failures.len());
        std::process::exit(1);
    }
}
