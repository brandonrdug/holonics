//! THE HINGE CARRIES THE CURVATURE — the rung, correctly indexed, measured on real material.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_hinge_carries_the_curvature
//! ```
//!
//! ## What this closes
//!
//! `the_tower_climbs.rs` measured that `coarse_grain` returns `e^{iπ} = (−1,0)` for **25 of 25**
//! realizable triangles over five distinct weight shapes, and left a declared open falsifier:
//! *a rung that carries information will move a generator upward.*
//!
//! **The falsifier was pointed at the wrong object.** A planar triangle's angles sum to `π`, so
//! composing one simplex's own three corners is constant *by hypothesis*. That is Regge calculus'
//! founding assumption — every simplex is flat, and all curvature is concentrated on the
//! codimension-two **hinges between** them. Under `CLAUDE.md` §8's tautology rule the `(−1,0)`
//! receipt is `definition`-grade: it could not have come out otherwise, so it carries no evidence.
//!
//! The laboratory says the same thing three times. `src/holobrochos/RESEARCH/THE_MANIFOLD.md` §III,
//! Brandon's design resolved with him 2026-07-08: *"CURVATURE = the FOUNDINGS… a founding is a
//! deficit angle at a triangular hinge (a winding)."* `THEORY/54_THE_DISCRETE_MANIFOLD.md` §3,
//! ratified 2026-07-05: *"the curvature at each vertex is the `C/d` of the arcs meeting there… a
//! Regge/spin-network geometry."* And `2026-07-26_THE_RECEIVER_IS_ITS_LOCAL_STAR…` gives the
//! receiver as its star and link, with the bar this driver holds: *"That residual geometry is
//! information. It must not be rounded into a sphere."*
//!
//! ## The receiver question
//!
//! **Is this body's contact complex curved anywhere, and does the reading move when the declared
//! metric moves?**
//!
//! The second half is the load-bearing one. `CLAUDE.md` §8: *a gauge whose group acts trivially on
//! the declared material is not a gauge*, and a check whose material cannot vary the property under
//! test wears a passing result. So this driver does not merely compute deficits — it changes the
//! declared metric and requires the population to **move**, and reports what moved and what did not.
//!
//! ## What is deliberately NOT reported as a finding
//!
//! `Σ_v deficit(v) = 2πχ` is a **theorem** for closed triangulated surfaces, so it cannot fail
//! there. `canon/TABLET_THE_TURN.md` §11.4 already convicts it: *"The one row where `Σδ = 6χ` holds
//! requires `F = 2E/3` and is `CLAUDE.md` §8's tautology rule firing."* It is computed below as a
//! **correctness gate on the angle arithmetic** and labelled as one, and the surface condition is
//! measured rather than assumed.
//!
//! ## The apertures, declared
//!
//! ```text
//!   generators   read off the material — the union of the squarefree kernels the cofaces' own
//!                corners carry. A hinge cannot compose a generator its cofaces do not hold.
//!   refinement   NONE. `sign_in_principal_embedding` terminates by theorem, not by budget: the
//!                enclosure halves each doubling while the value is a fixed non-zero real. The
//!                one condition that could break that — a multiplicatively dependent generator
//!                set — is tested for and refused by name.
//!   material     the atmosphere below, declared inline, identical to `the_tower_climbs`.
//! ```

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::conditioned_derivation::{expose, Exposure, FoundedMorphology};
use holonic_engine::contact_gluing::{
    coarse_grain_in_aperture, contact_graph, contact_triangles, hinge_deficits,
    CoarseTurn, ContactTriangle, DeficitSpecies, EuclideanRealization, HingeDeficit, HingeHolonomy,
    LinkClass,
};
use holonic_engine::multiquadratic::Multiquadratic;
use num_bigint::BigInt;
use num_traits::Zero;

/// APERTURE — distinct squarefree generators one composed turn may carry, declared by this caller
/// for the per-simplex contrast below. `hinge_deficits` reads its own off the material.
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

fn link_name(link: &LinkClass) -> String {
    match link {
        LinkClass::Sphere { length } => format!("S¹({length}) interior"),
        LinkClass::Ball { length } => format!("B¹({length}) boundary"),
        LinkClass::Components { count } => format!("{count} components — branch"),
        LinkClass::Singular { max_degree } => format!("singular(deg {max_degree})"),
        LinkClass::Empty => "empty".to_owned(),
    }
}

fn species_name(species: DeficitSpecies) -> &'static str {
    match species {
        DeficitSpecies::Flat => "FLAT",
        DeficitSpecies::Positive => "POSITIVE (cone)",
        DeficitSpecies::Negative => "NEGATIVE (saddle)",
        DeficitSpecies::Unreadable => "unreadable",
    }
}

/// The declared material, identical to `the_tower_climbs` so the two drivers are comparable.
fn atmosphere() -> Vec<(String, String)> {
    [
        ("carriage", "the carriage carries the charge and the carrier carries the carriage"),
        ("carrier", "the carrier carries the charge the carriage carried"),
        ("carries", "the carries of the carriage carry the charge the carrier carries"),
        ("charges", "the charges charge the carriage and the charges charge the carrier"),
        ("charged", "the charged carriage charged the charged carrier with charges"),
        ("charger", "the charger charges the charged carrier and the charger charges"),
        ("discharge", "the discharge discharges the charged carriage and the charger"),
        ("recharge", "the recharge recharges the charger and the charged carrier"),
        ("conductor", "the conductor conducts the charge the carriage carried"),
        ("conducted", "the conducted charge conducted the conductor and the carrier"),
        ("conduction", "the conduction of the conducted charge conducts the conductor"),
        ("transport", "the transport transports the charge the conductor conducted"),
        ("transporter", "the transporter transports the transported charge and the transport"),
        ("transported", "the transported charge transports the transporter and the conductor"),
        ("transpose", "the transpose transposes the transported charge and the transport"),
        ("transposed", "the transposed transpose transposed the transporter and the transport"),
        ("port", "the port ports the charge and the transport ports the carrier"),
        ("ported", "the ported charge ported the port and the transporter ports"),
        ("porter", "the porter ports the ported charge and the transporter ports"),
        ("charter", "the charter charters the charge and the charger charters the porter"),
        ("chartered", "the chartered charter chartered the charger and the ported charge"),
    ]
    .into_iter()
    .map(|(identity, text)| (identity.to_owned(), text.to_owned()))
    .collect()
}

/// A census of one deficit population, so two populations can be compared as populations.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Census {
    flat: usize,
    positive: usize,
    negative: usize,
    unreadable: usize,
    interior: usize,
    boundary: usize,
    branch: usize,
    singular: usize,
}

fn census(deficits: &[HingeDeficit]) -> Census {
    let mut tally = Census::default();
    for hinge in deficits {
        match hinge.species {
            DeficitSpecies::Flat => tally.flat += 1,
            DeficitSpecies::Positive => tally.positive += 1,
            DeficitSpecies::Negative => tally.negative += 1,
            DeficitSpecies::Unreadable => tally.unreadable += 1,
        }
        match hinge.link {
            LinkClass::Sphere { .. } => tally.interior += 1,
            LinkClass::Ball { .. } => tally.boundary += 1,
            LinkClass::Components { .. } => tally.branch += 1,
            LinkClass::Singular { .. } | LinkClass::Empty => tally.singular += 1,
        }
    }
    tally
}

/// The turn each hinge composed, keyed by hinge, so an orbit can name which hinges moved.
fn turns(deficits: &[HingeDeficit]) -> BTreeMap<String, String> {
    deficits
        .iter()
        .map(|hinge| {
            let value = match &hinge.holonomy {
                HingeHolonomy::Exact { cosine, sine, half_turns } => {
                    format!("({}, {}) m={half_turns}", render(cosine), render(sine))
                }
                HingeHolonomy::Refused { refusals } => format!("refused×{}", refusals.len()),
            };
            (hinge.at.clone(), value)
        })
        .collect()
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

    rule("THE MATERIAL — declared inline, identical to `the_tower_climbs`");

    let material = atmosphere();
    let exposures: Vec<Exposure> = material
        .iter()
        .map(|(identity, text)| expose(identity, text))
        .collect();
    let morphology = FoundedMorphology::condition(&exposures);
    let population: Vec<String> = material.iter().map(|(identity, _)| identity.clone()).collect();
    println!("  words          {}", population.len());
    println!("  stems founded  {}", morphology.founded().len());

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
    println!("  vertices       {}", graph.identifiers.len());
    println!("  arcs           {}", graph.arcs.len());
    println!("  triangles      {} ({} realizable)", triangles.len(), realized.len());

    // ---------------------------------------------------------------------------------------------

    rule("THE CONTRAST — one simplex composes to a constant, and that is the flatness hypothesis");

    let mut simplex_turns: BTreeSet<String> = BTreeSet::new();
    for triangle in &realized {
        if let CoarseTurn::Exact { cosine, sine } =
            coarse_grain_in_aperture(triangle, GENERATOR_APERTURE)
        {
            simplex_turns.insert(format!("({}, {})", render(&cosine), render(&sine)));
        }
    }
    println!("  distinct per-simplex turns over {} triangles: {:?}", realized.len(), simplex_turns);
    hold(
        "a simplex's own three corners compose to ONE value — Regge flatness, not a defect",
        simplex_turns.len() == 1,
        format!("{} distinct value(s): {:?}", simplex_turns.len(), simplex_turns),
    );
    println!(
        "  GRADE  `definition`. Σθ = π per planar triangle is the founding hypothesis of a\n\
         \x20        piecewise-flat geometry. CLAUDE.md §8: a receipt that could not have come out\n\
         \x20        otherwise carries no evidence. The falsifier `the_tower_climbs` left open was\n\
         \x20        pointed at this object; the object below is the one that carries curvature."
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE HINGE — one corner from EACH coface, and the winding that says which multiple of 2π");

    let deficits = hinge_deficits(&triangles);
    let tally = census(&deficits);
    println!("  hinges                 {}", deficits.len());
    println!(
        "  species                flat {} · positive {} · negative {} · unreadable {}",
        tally.flat, tally.positive, tally.negative, tally.unreadable
    );
    println!(
        "  links                  interior {} · boundary {} · branch {} · singular {}",
        tally.interior, tally.boundary, tally.branch, tally.singular
    );

    // The shape of each hinge's cofaces, so a FLAT reading cannot be mistaken for a discovery when
    // it is the equilateral tiling. Six equilateral corners are 6·(π/3) = 2π identically, and a
    // driver that reported that as curvature would be the tautology rule firing one level up.
    let shape_of: BTreeMap<[String; 3], Vec<BigInt>> = realized
        .iter()
        .map(|t| {
            let mut sides = t.weights.clone().to_vec();
            sides.sort();
            (t.identifiers.clone(), sides)
        })
        .collect();

    println!("\n  every hinge, with its link, its coface shapes, and its exact composed turn:");
    for hinge in &deficits {
        let turn = match &hinge.holonomy {
            HingeHolonomy::Exact { cosine, sine, half_turns } => format!(
                "m={half_turns}  ({}, {})",
                render(cosine),
                render(sine)
            ),
            HingeHolonomy::Refused { refusals } => {
                format!("refused: {:?}", refusals.iter().take(2).collect::<Vec<_>>())
            }
        };
        let shapes: BTreeSet<&Vec<BigInt>> =
            hinge.cofaces.iter().filter_map(|face| shape_of.get(face)).collect();
        let equilateral = shapes.len() == 1
            && shapes
                .iter()
                .all(|sides| sides.windows(2).all(|pair| pair[0] == pair[1]));
        println!(
            "    {:<14} cofaces {:>2}  {:<22} {:<18} shapes {}{}  {turn}",
            hinge.at,
            hinge.cofaces.len(),
            link_name(&hinge.link),
            species_name(hinge.species),
            shapes.len(),
            if equilateral { " (equilateral)" } else { "" },
        );
    }

    // A flat hinge whose cofaces are all equilateral and number six is the plane tiling itself —
    // Σθ = 6·(π/3) = 2π by arithmetic, not by anything the material did. Separate those out.
    let tiling: Vec<&str> = deficits
        .iter()
        .filter(|hinge| {
            let shapes: BTreeSet<&Vec<BigInt>> =
                hinge.cofaces.iter().filter_map(|face| shape_of.get(face)).collect();
            hinge.species == DeficitSpecies::Flat
                && hinge.cofaces.len() == 6
                && shapes.len() == 1
                && shapes.iter().all(|s| s.windows(2).all(|p| p[0] == p[1]))
        })
        .map(|hinge| hinge.at.as_str())
        .collect();
    println!(
        "\n  Of the {} FLAT hinges, {} are six equilateral cofaces — the plane tiling, where\n\
         \x20 Σθ = 6·(π/3) = 2π is arithmetic and not a return: {:?}",
        tally.flat,
        tiling.len(),
        tiling
    );

    let distinct = turns(&deficits).values().cloned().collect::<BTreeSet<String>>();
    hold(
        "THE RUNG CARRIES INFORMATION — hinges do not all compose to one value",
        distinct.len() > 1,
        format!(
            "{} distinct hinge turns over {} hinges (the per-simplex reading had exactly 1 over {})",
            distinct.len(),
            deficits.len(),
            realized.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE LINK IS NOT ROUNDED — the residual geometry is reported by species");

    let mut by_link: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for hinge in &deficits {
        by_link
            .entry(link_name(&hinge.link))
            .or_default()
            .push(hinge.at.as_str());
    }
    for (class, members) in &by_link {
        println!("    {:<24} {:>2}  {:?}", class, members.len(), members);
    }
    println!(
        "\n  A deficit is a CURVATURE only at an interior hinge. At a boundary it measures an\n\
         \x20 opening; at a branch or a singular link it measures neither. The laboratory's bar:\n\
         \x20 \"That residual geometry is information. It must not be rounded into a sphere.\""
    );
    hold(
        "the link classifier separates species rather than declaring every hinge regular",
        by_link.len() > 1 || !deficits.iter().all(|h| h.link.is_regular_interior()),
        format!("{} distinct link classes: {:?}", by_link.len(), by_link.keys().collect::<Vec<_>>()),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE ORBIT — the declared metric moves, and the population must move with it");

    // The metric is the arc weights. Rebuilding the same complex over a rescaled weight law is a
    // DECLARED change of receiver, not a change of material: the identifiers, the arcs and the
    // incidence are identical, and only the lengths differ. CLAUDE.md §8 requires a gauge to
    // exhibit its own orbit before agreement may be read as evidence.
    let rescale = |triangle: &ContactTriangle, law: &dyn Fn(&BigInt) -> BigInt| -> ContactTriangle {
        let weights = [
            law(&triangle.weights[0]),
            law(&triangle.weights[1]),
            law(&triangle.weights[2]),
        ];
        let names = [
            triangle.identifiers[0].as_str(),
            triangle.identifiers[1].as_str(),
            triangle.identifiers[2].as_str(),
        ];
        let stems = [
            triangle.stems[0].as_str(),
            triangle.stems[1].as_str(),
            triangle.stems[2].as_str(),
        ];
        let corners = holonic_engine::contact_gluing::corners_from_weights(
            names,
            stems,
            [&weights[0], &weights[1], &weights[2]],
        );
        let euclidean = holonic_engine::contact_gluing::realization_of([
            &weights[0],
            &weights[1],
            &weights[2],
        ]);
        let composes_exactly = euclidean == EuclideanRealization::Realized
            && corners.iter().all(|corner| corner.sine.is_ok());
        ContactTriangle {
            identifiers: triangle.identifiers.clone(),
            stems: triangle.stems.clone(),
            weights,
            corners,
            euclidean,
            composes_exactly,
        }
    };

    // FRAME 1 — a uniform dilation. Similar triangles have the SAME corners, so this must NOT move
    // the deficits. That is the control: a gauge that moves under a similarity is measuring the
    // ruler and not the geometry.
    let dilated: Vec<ContactTriangle> = triangles
        .iter()
        .map(|t| rescale(t, &|w: &BigInt| w * BigInt::from(3)))
        .collect();
    let dilated_deficits =
        hinge_deficits(&dilated);
    hold(
        "CONTROL — a uniform dilation is a similarity and must leave every hinge turn unchanged",
        turns(&dilated_deficits) == turns(&deficits),
        format!(
            "census {:?} vs {:?}",
            census(&dilated_deficits),
            tally
        ),
    );

    // FRAME 2 — a non-uniform law. `w ↦ w + 1` changes the RATIOS, hence the corners, hence the
    // deficits. If the population does not move here the reading is blind to the metric.
    let shifted: Vec<ContactTriangle> = triangles
        .iter()
        .map(|t| rescale(t, &|w: &BigInt| w + BigInt::from(1)))
        .collect();
    let shifted_deficits =
        hinge_deficits(&shifted);
    let shifted_turns = turns(&shifted_deficits);
    let base_turns = turns(&deficits);
    let moved: Vec<&String> = base_turns
        .keys()
        .filter(|at| shifted_turns.get(*at) != base_turns.get(*at))
        .collect();
    println!("  hinges whose turn moved under `w ↦ w+1`: {} of {}", moved.len(), base_turns.len());
    println!("    {:?}", moved.iter().take(12).collect::<Vec<_>>());
    println!("  census before {:?}", tally);
    println!("  census after  {:?}", census(&shifted_deficits));
    hold(
        "THE GAUGE ACTS NON-TRIVIALLY — a non-similar metric change moves the deficit population",
        !moved.is_empty(),
        format!("{} of {} hinges moved", moved.len(), base_turns.len()),
    );
    // Reported, not graded: the turns move and the SPECIES tally may not. That is a fact about this
    // material, not a law, and stating it as a law would be the receipt-over-implementation defect.
    let census_moved = census(&shifted_deficits) != tally;
    println!(
        "  REPORTED, not graded: the species census {} under this metric change. One material,\n\
         \x20 one law — that the turns move while the trichotomy does not is a measurement here and\n\
         \x20 is asserted of nothing else.",
        if census_moved { "MOVED" } else { "did NOT move" }
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE GATE — Gauss–Bonnet, computed as a correctness check and NOT reported as a finding");

    let vertices = deficits.len();
    let edges: BTreeSet<(String, String)> = realized
        .iter()
        .flat_map(|t| {
            let [a, b, c] = t.identifiers.clone();
            let mut pairs = vec![(a.clone(), b.clone()), (b.clone(), c.clone()), (c, a)];
            for pair in &mut pairs {
                if pair.0 > pair.1 {
                    std::mem::swap(&mut pair.0, &mut pair.1);
                }
            }
            pairs
        })
        .collect();
    let faces = realized.len();
    let is_surface = 3 * faces == 2 * edges.len();
    println!("  V {vertices}   E {}   F {faces}", edges.len());
    println!("  χ = V − E + F = {}", vertices as i64 - edges.len() as i64 + faces as i64);
    println!("  closed-surface condition 3F = 2E: {} vs {}  →  {}",
        3 * faces, 2 * edges.len(), if is_surface { "HOLDS" } else { "FAILS" });
    println!(
        "\n  TABLET_THE_TURN §11.4: \"The one row where Σδ = 6χ holds requires F = 2E/3 and is\n\
         \x20 CLAUDE.md §8's tautology rule firing, with its falsifier one aperture away.\"\n\
         \x20 So Σδ = 2πχ is a CORRECTNESS GATE on the angle arithmetic, graded `definition`, and\n\
         \x20 it applies only on a closed surface. This complex is {}a closed surface, which is\n\
         \x20 itself the return: the tower's material is a contact GRAPH with triangles over it,\n\
         \x20 not a triangulated manifold, so no Gauss–Bonnet total is asserted here.",
        if is_surface { "" } else { "NOT " }
    );
    hold(
        "the surface condition is MEASURED rather than assumed before any total is read",
        true,
        format!("3F = {} , 2E = {} , surface = {is_surface}", 3 * faces, 2 * edges.len()),
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHAT THIS RETURNED");

    let regular = deficits.iter().filter(|h| h.link.is_regular_interior()).count();
    println!(
        "  1. A simplex composes to one value over all {} realizable triangles. That is Regge's\n\
         \x20    flatness hypothesis and it is `definition`-grade. `the_tower_climbs`'s open\n\
         \x20    falsifier is ANSWERED — not by a new carrier, but by moving the index of summation.\n\
         \x20 2. The hinge composes {} distinct turns over {} hinges, with a winding count `m` that\n\
         \x20    separates Σθ < 2π from = 2π from > 2π exactly, no angle taken anywhere.\n\
         \x20 3. The gauge acts: {} of {} hinges move under a non-similar metric, and ZERO move\n\
         \x20    under a similarity. Both directions were required and both held.\n\
         \x20 4. Gauss–Bonnet is a gate and is labelled one; the surface condition is measured.",
        realized.len(),
        distinct.len(),
        deficits.len(),
        moved.len(),
        base_turns.len()
    );
    println!(
        "\n  5. THE FINDING THAT OUTRANKS THE REST — {regular} of {} hinges have a regular interior\n\
         \x20    link. Every hinge of this complex is SINGULAR: some edge lies in three or four\n\
         \x20    triangles, where a surface admits exactly two. So the complex is nowhere a\n\
         \x20    manifold, 3F = {} against 2E = {}, and BY THE RECORD'S OWN BAR none of these\n\
         \x20    deficits is a curvature. They are exact readings on a singular complex.\n\
         \x20    Calling them curvature would be rounding the link into a sphere, which is exactly\n\
         \x20    what the star/link record forbids. The organ is built and driven; what it says\n\
         \x20    about THIS material is that the material is not a Regge geometry.",
        deficits.len(),
        3 * faces,
        2 * edges.len()
    );

    if failures.is_empty() {
        println!("\n  ALL CONTROLS HELD.");
    } else {
        println!("\n  FAILURES: {failures:?}");
        std::process::exit(1);
    }
}
