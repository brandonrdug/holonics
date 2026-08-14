//! THE SEAM FOUNDS AND THE FLOW DISSIPATES — the three necessities of the ratified hinge law.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_seam_founds_and_the_flow_dissipates
//! ```
//!
//! ## What this closes
//!
//! `research/records/2026-07-20_THE_HINGE_CARRIES_THE_FRAME_THE_SUCCESSOR_REPLACES_THE_STANDING_STAR.md`
//! and `research/records/2026-07-19_THE_RICCI_TRACE_CHANGES_THE_RECEIVER_THE_SINGULAR_NECK_REBASES_THE_BODY.md`
//! are Brandon-ratified, live in this repository since extraction, and were cited by nothing here
//! until 2026-08-10. Between them they specify three things the tower did not have:
//!
//! 1. **The hinge residual is a four-branch law**, not an angle. §III: `delta_e = a_R|e −
//!    G_(L→R)(a_L|e)`, and *"`0/0` is dark; matching occupied sides with opposed induced hands form
//!    an internal seam and cancel; `1/0` or `0/1` leaves an exposed oriented residual; and matching
//!    occupied sides with the same hand reinforce or expose a branching/singular gluing rather than
//!    an ordinary manifold interior."*
//! 2. **Which cell is the hinge is receiver-relative.** §V: *"The same triangle may thus be a whole
//!    two-cell at one grain, a boundary face at another, and a curvature hinge from a
//!    four-dimensional receiver."* That is the tower's upward map.
//! 3. **A curvature feedback is a flow only if it dissipates.** *"Ricci flow feeds that receiver
//!    quotient back into the metric by which later continuations are compared."* `discrete_curvature`
//!    had the shape and the wrong law: `Σ K' = −Σ K`, an involution.
//!
//! ## The receiver question
//!
//! **Does the machine's own hinge law separate a seam from a founding, and does its curvature
//! feedback converge?**
//!
//! ## What is deliberately NOT claimed
//!
//! The coefficient is the caller's declaration and this driver declares several, reporting what each
//! does. `Σ K' = (1−2c) Σ K` is a theorem and is used as an exact check, never as evidence about the
//! material. The pointwise amplitude is **reported and not asserted** — the total is what the
//! theorem governs and the amplitude is not.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::conditioned_derivation::{Exposure, FoundedMorphology, expose};
use holonic_engine::contact_gluing::{
    ContactTriangle, EuclideanRealization, HingeGluing, climb, contact_graph, contact_triangles,
    grain_roles, hinge_deficits, hinge_residuals, triangles_at_rank,
};
use holonic_engine::discrete_curvature::{
    CoefficientSpecies, DiscreteCurvatureConfiguration, coefficient_species,
    dissipative_annihilator, total_multiplier,
};
use holonic_engine::{HingeId, VertexId};
use num_bigint::BigInt;
use relational_geometry::Rat;

/// APERTURE — generators one composed turn may carry while climbing. Declared by this caller; the
/// hinge organ reads its own off the material.
const CLIMB_APERTURE: usize = 12;
/// APERTURE — how many flow steps to exhibit. Declared by this caller; the law is exact at every
/// step and nothing here depends on where it stops.
const FLOW_STEPS: usize = 6;

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn gluing_name(gluing: &HingeGluing) -> String {
    match gluing {
        HingeGluing::Dark => "dark".to_owned(),
        HingeGluing::Exposed { hand } => format!("EXPOSED (leader, hand {hand:+})"),
        HingeGluing::Seam => "seam (interior)".to_owned(),
        HingeGluing::Reversing => "REVERSING (non-orientable)".to_owned(),
        HingeGluing::Branching { sides } => format!("BRANCHING ({sides} sides)"),
    }
}

fn species_name(species: CoefficientSpecies) -> &'static str {
    match species {
        CoefficientSpecies::Inert => "inert",
        CoefficientSpecies::Dissipative => "DISSIPATIVE",
        CoefficientSpecies::Annihilating => "ANNIHILATING",
        CoefficientSpecies::Reflective => "REFLECTIVE",
        CoefficientSpecies::Expanding => "expanding",
    }
}

/// The declared material, identical to `the_tower_climbs` and `the_hinge_carries_the_curvature`.
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
            "the ported charge ported the port and the transporter ports",
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

/// Build a curvature configuration on the contact complex's own 1-skeleton.
///
/// The response starts at unit, which is what `at_unit_response` is for: the metric refinement is a
/// separate declared question that `TABLET_THE_TURN` §11.4 refuses on this carrier, and fabricating
/// a per-edge angle here would be exactly that refusal ignored. What is measured below is the
/// **law**, and the incidence is what the law runs on.
fn curvature_configuration(
    triangles: &[ContactTriangle],
) -> Option<(DiscreteCurvatureConfiguration, BTreeMap<VertexId, String>)> {
    let mut identifiers: BTreeSet<&str> = BTreeSet::new();
    let mut edges: BTreeSet<(&str, &str)> = BTreeSet::new();
    for triangle in triangles {
        if triangle.euclidean != EuclideanRealization::Realized {
            continue;
        }
        let [a, b, c] = &triangle.identifiers;
        for name in [a, b, c] {
            identifiers.insert(name.as_str());
        }
        for (left, right) in [(a, b), (b, c), (a, c)] {
            let pair = if left <= right {
                (left.as_str(), right.as_str())
            } else {
                (right.as_str(), left.as_str())
            };
            edges.insert(pair);
        }
    }
    let index: BTreeMap<&str, VertexId> = identifiers
        .iter()
        .enumerate()
        .map(|(ordinal, name)| (*name, VertexId(ordinal as u64 + 1)))
        .collect();
    let named: BTreeMap<VertexId, String> = index
        .iter()
        .map(|(name, id)| (*id, (*name).to_owned()))
        .collect();
    let hinges: Vec<(HingeId, [VertexId; 2])> = edges
        .iter()
        .enumerate()
        .map(|(ordinal, (left, right))| (HingeId(ordinal as u64 + 1), [index[left], index[right]]))
        .collect();
    DiscreteCurvatureConfiguration::at_unit_response(hinges)
        .ok()
        .map(|configuration| (configuration, named))
}

fn main() {
    let mut failures: Vec<String> = Vec::new();
    let mut hold = |claim: &str, held: bool, evidence: String| {
        if held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            println!("  [FAILS] {claim}\n            {evidence}");
            failures.push(claim.to_owned());
        }
    };

    rule("THE MATERIAL — declared inline, identical to the two sibling drivers");

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
    let graph = match contact_graph(&morphology, &population) {
        Ok(graph) => graph,
        Err(refusal) => {
            println!("  the contact graph refused: {refusal:?}");
            std::process::exit(1);
        }
    };
    let triangles = contact_triangles(&graph);
    let realized: Vec<&ContactTriangle> = triangles
        .iter()
        .filter(|t| t.euclidean == EuclideanRealization::Realized)
        .collect();
    println!(
        "  words {}   vertices {}   arcs {}   triangles {} ({} realizable)",
        population.len(),
        graph.identifiers.len(),
        graph.arcs.len(),
        triangles.len(),
        realized.len()
    );

    // ---------------------------------------------------------------------------------------------

    rule("NECESSITY 1 — the event-site hinge: four branches, and the orientation they need");

    let (orientation, residuals) = hinge_residuals(&triangles);
    println!("  faces                  {}", residuals.len());
    println!("  dual components        {}", orientation.components);
    println!("  seams (interior)       {}", orientation.seams.len());
    println!("  exposed (leaders)      {}", orientation.exposed.len());
    println!("  branching              {}", orientation.branching.len());
    println!("  reversing              {}", orientation.reversing.len());
    println!("  coherently orientable  {}", orientation.coherent);

    let solved: BTreeSet<i8> = orientation.signs.values().copied().collect();
    hold(
        "the orientation solve is a real assignment, not the canonical order wearing a name",
        solved.len() > 1 || orientation.signs.len() <= 1,
        format!(
            "{} triangles carry {} distinct signs {:?}",
            orientation.signs.len(),
            solved.len(),
            solved
        ),
    );

    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    for residual in &residuals {
        *census.entry(gluing_name(&residual.gluing)).or_default() += 1;
    }
    println!("\n  gluing census:");
    for (species, count) in &census {
        println!("    {species:<32} {count:>3}");
    }
    let founding: Vec<&str> = residuals
        .iter()
        .filter(|residual| residual.founds())
        .map(|residual| residual.edge.0.as_str())
        .collect();
    hold(
        "the law separates seams from foundings rather than reporting one species",
        census.len() > 1,
        format!(
            "{} species over {} faces; {} faces found",
            census.len(),
            residuals.len(),
            founding.len()
        ),
    );

    println!("\n  every branching face, named — these are the FOUND seams §V speaks of:");
    for residual in residuals
        .iter()
        .filter(|r| matches!(r.gluing, HingeGluing::Branching { .. }))
    {
        println!(
            "    {:<28} {} sides  hands {:?}  {:?}",
            format!("{}—{}", residual.edge.0, residual.edge.1),
            residual.cofaces.len(),
            residual.oriented_hands,
            residual
                .cofaces
                .iter()
                .map(|c| c.join("|"))
                .collect::<Vec<_>>()
        );
    }

    // The join to the deficit organ: a singular link should contain a founding face.
    let deficits = hinge_deficits(&triangles);
    let singular: Vec<&str> = deficits
        .iter()
        .filter(|hinge| !hinge.link.is_regular_interior())
        .map(|hinge| hinge.at.as_str())
        .collect();
    let founding_faces: BTreeSet<&str> = residuals
        .iter()
        .filter(|residual| residual.founds())
        .flat_map(|residual| [residual.edge.0.as_str(), residual.edge.1.as_str()])
        .collect();
    let explained = singular
        .iter()
        .filter(|at| founding_faces.contains(*at))
        .count();
    hold(
        "every singular link is explained by a founding face at that vertex",
        explained == singular.len(),
        format!(
            "{explained} of {} singular links carry a founding face",
            singular.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("NECESSITY 2 — the grain: the same object is a two-cell below and a hinge above");

    let rank_one = climb(1, &triangles, CLIMB_APERTURE);
    let above = triangles_at_rank(&rank_one);
    let realized_above = above
        .iter()
        .filter(|t| t.euclidean == EuclideanRealization::Realized)
        .count();
    println!("  rank 1 vertices        {}", rank_one.vertices.len());
    println!("  rank 1 arcs            {}", rank_one.arcs.len());
    println!(
        "  rank 1 triangles       {} ({} realizable)",
        above.len(),
        realized_above
    );

    let roles = grain_roles(&triangles, &above);
    let promoted = roles
        .iter()
        .filter(|role| role.hinge_cofaces_above.unwrap_or(0) > 0)
        .count();
    println!(
        "\n  two-cells below that are curvature hinges above: {promoted} of {}",
        roles.len()
    );
    for role in roles.iter().take(8) {
        println!(
            "    {:<28} 2-cell {:?}   hinge cofaces above {:?}",
            role.name, role.two_cell_at_rank, role.hinge_cofaces_above
        );
    }
    hold(
        "THE GRAIN IS RELATIVE — a rank-0 two-cell is a rank-1 curvature hinge",
        promoted > 0,
        format!(
            "{promoted} of {} two-cells carry cofaces one grain up",
            roles.len()
        ),
    );

    let deficits_above = hinge_deficits(&above);
    let interior_above = deficits_above
        .iter()
        .filter(|hinge| hinge.link.is_regular_interior())
        .count();
    println!(
        "\n  rank 1 hinges {} · regular interior {} — the same reading, one grain up",
        deficits_above.len(),
        interior_above
    );

    // ---------------------------------------------------------------------------------------------

    rule("NECESSITY 3 — the flow: Σ K' = (1 − 2c) Σ K, and c = 1 is the reflection");

    let Some((configuration, _named)) = curvature_configuration(&triangles) else {
        println!("  the curvature configuration refused on this incidence");
        std::process::exit(1);
    };
    println!(
        "  vertices {}   hinges {}",
        configuration.vertices().count(),
        configuration.hinges().count()
    );
    println!(
        "  total deficit at unit response  {}",
        configuration.total_deficit()
    );
    println!(
        "  deficit amplitude               {}",
        configuration.deficit_amplitude()
    );

    let coefficients = [
        Rat::new(BigInt::from(0), BigInt::from(1)),
        Rat::new(BigInt::from(1), BigInt::from(4)),
        dissipative_annihilator(),
        Rat::new(BigInt::from(3), BigInt::from(4)),
        Rat::new(BigInt::from(1), BigInt::from(1)),
        Rat::new(BigInt::from(2), BigInt::from(1)),
    ];

    println!(
        "\n  {:<8} {:<12} {:<14} {}",
        "c", "1 − 2c", "species", "|Σ K| over the steps"
    );
    let mut law_holds = true;
    let mut dissipated = false;
    let mut reflected = false;
    for coefficient in &coefficients {
        let mut carried = configuration.clone();
        let multiplier = total_multiplier(coefficient);
        let species = coefficient_species(coefficient);
        let mut expected = carried.total_deficit();
        let mut trace = Vec::new();
        for _ in 0..FLOW_STEPS {
            let step = carried.step_at(coefficient);
            expected = &multiplier * &expected;
            if step.total_deficit_after != expected {
                law_holds = false;
            }
            trace.push(format!("{}", step.total_deficit_after));
        }
        if species == CoefficientSpecies::Dissipative || species == CoefficientSpecies::Annihilating
        {
            dissipated = true;
        }
        if species == CoefficientSpecies::Reflective {
            reflected = true;
            // The reflection's magnitude is constant; the sign alternates.
            let start = configuration.total_deficit();
            let magnitude_held =
                carried.total_deficit() == start || carried.total_deficit() == -start.clone();
            if !magnitude_held {
                law_holds = false;
            }
        }
        println!(
            "  {:<8} {:<12} {:<14} {}",
            format!("{coefficient}"),
            format!("{multiplier}"),
            species_name(species),
            trace.join("  ")
        );
    }
    hold(
        "Σ K' = (1 − 2c) Σ K holds exactly at every declared coefficient, over every step",
        law_holds,
        format!(
            "{} coefficients × {FLOW_STEPS} steps, exact rationals",
            coefficients.len()
        ),
    );
    hold(
        "the module's own derived c = 1 is the REFLECTION, and a dissipative c exists",
        reflected && dissipated,
        format!(
            "c = 1 → multiplier {}, c = 1/2 → multiplier {}",
            total_multiplier(&Rat::new(BigInt::from(1), BigInt::from(1))),
            total_multiplier(&dissipative_annihilator())
        ),
    );

    // The amplitude, reported and not asserted — the theorem governs the total, not this.
    println!("\n  amplitude after {FLOW_STEPS} steps, REPORTED not asserted:");
    for coefficient in &coefficients {
        let mut carried = configuration.clone();
        for _ in 0..FLOW_STEPS {
            carried.step_at(coefficient);
        }
        println!(
            "    c = {:<6} amplitude {:<24} total {}",
            format!("{coefficient}"),
            format!("{}", carried.deficit_amplitude()),
            carried.total_deficit()
        );
    }
    // How many steps each coefficient needs to reach EXACT flatness, if it ever does. This is the
    // payoff the total alone cannot state: a flat configuration is a fixed point of the law on any
    // incidence, so reaching it is convergence in the strong sense and not an asymptote.
    println!(
        "\n  steps to EXACT flatness (every K(v) = 0), within {} steps:",
        FLOW_STEPS * 4
    );
    for coefficient in &coefficients {
        let mut carried = configuration.clone();
        let mut reached = None;
        for step in 1..=FLOW_STEPS * 4 {
            carried.step_at(coefficient);
            if carried.is_flat() {
                reached = Some(step);
                break;
            }
        }
        println!(
            "    c = {:<6} {}",
            format!("{coefficient}"),
            match reached {
                Some(step) => format!("FLAT after {step} step(s)"),
                None => "not flat within the declared window".to_owned(),
            }
        );
    }

    // And the one-step result is a property of the INCIDENCE, not of the coefficient. State it, or
    // a reader takes it for a discovery about the flow.
    let degrees: BTreeSet<usize> = configuration
        .vertices()
        .filter_map(|vertex| configuration.link_size(vertex).ok())
        .collect();
    println!(
        "\n  link sizes present: {degrees:?}. At unit response K(v) = 6 − n_v, so on a d-REGULAR\n\
         \x20 component K is constant and Σ_(w~v) K(w)/n_w = K(v) identically, whence c = 1/2 gives\n\
         \x20 K' = 0 everywhere in one step BY ARITHMETIC. The one-step flatness above is therefore\n\
         \x20 a property of this material's component regularity, not a discovery about the\n\
         \x20 coefficient — CLAUDE.md §8. The irregular control is in the module's own tests."
    );

    println!(
        "\n  The total and the amplitude are independent. Σ K is ONE linear functional and a\n\
         \x20 configuration whose total is zero can carry arbitrarily large opposing deficits. On a\n\
         \x20 bipartite incidence the alternating mode is an eigenvector with eigenvalue 1 at EVERY\n\
         \x20 coefficient, so no c dissipates it — two-colourability is the obstruction, which is\n\
         \x20 the hand. Asserting an amplitude direction here would be a claim not derived."
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHAT THIS RETURNED");

    println!(
        "  1. The event-site hinge law is built with all four branches and the orientation solve\n\
         \x20    they require. {} faces over {} species; {} founding faces named individually.\n\
         \x20    The raw canonical hands are a CHART and the organ refuses to read them as an\n\
         \x20    invariant — a control requires the solved signs to be genuinely non-constant.\n\
         \x20 2. The grain is relative and it is the tower's upward map: {promoted} of {} rank-0\n\
         \x20    two-cells are rank-1 curvature hinges, corners read by the identical law.\n\
         \x20 3. Σ K' = (1 − 2c) Σ K, exact at six coefficients over {FLOW_STEPS} steps. c = 1 —\n\
         \x20    the module's own derived law — is the multiplier −1, a REFLECTION. c = 1/2 is the\n\
         \x20    unique annihilator. The live law overshoots the dissipative one by exactly two,\n\
         \x20    which is I − 2P against I − P: the reflection and the projection it doubles.",
        residuals.len(),
        census.len(),
        founding.len(),
        roles.len()
    );

    if failures.is_empty() {
        println!("\n  ALL CONTROLS HELD.");
    } else {
        println!("\n  FAILURES: {failures:?}");
        std::process::exit(1);
    }
}
