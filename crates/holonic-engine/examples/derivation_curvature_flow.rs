//! Read a conditioned body's production as a layout, take its curvature, run the flow, and spend
//! the returned curvature back into the geometry that produced it.
//!
//! ```text
//! cargo run --release --example derivation_curvature_flow -- \
//!     standing/output \
//!     reference/pureholonics-seed/src/pureholonics \
//!     reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! The three paths are the mathematical deposit and two frames of linguistic material, exactly as
//! `conditioned_derivation_body` takes them: this driver conditions the same body on the same
//! corpora, asks it the same question, and then reads the circuit that production presents as a
//! **hinge incidence with curvature**.
//!
//! ## What this driver is for
//!
//! One reading and one loop.
//!
//! > **A passage recruiting widely sits at a vertex of high coordination and carries a large
//! > negative deficit; one recruiting narrowly carries a positive one. The flow moves those
//! > deficits, the lift carries the movement back onto the line the layout already held, and
//! > `local_star`'s own event law then returns different positions. Every deficit, every revision
//! > and every refusal is named by the passages that founded the cell it sits on.**
//!
//! Nothing here grades the combinatorial charge. The charge is `6 - n_v` and moves only when the
//! circuit changes, so a run that graded it would watch a flow step move nothing and conclude
//! wrongly. Both are printed side by side so the difference is legible.
//!
//! Two declared layouts stand beside the real material because the real material cannot exhibit
//! them: a four-cycle at response three, which is flat and stays exactly fixed, and a star at
//! response four, which is **bipartite with unequal parts and sits fixed at nonzero deficit
//! forever**. The second is the falsifier of "the flow drives every deficit to zero", which is
//! false, and it is exhibited rather than asserted.
//!
//! The run exits nonzero when any declared control fails.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    ConditionedBody, ConditionedCircuit, DerivationQuery, Exposure, expose,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::derivation_curvature::{
    DerivationCurvatureBody, DerivationLayout, NamedDeficit, NamedFlowStep, SiteKind,
};
use holonic_engine::discrete_curvature::CurvatureFixedPoint;
use num_traits::Zero;
use relational_geometry::{Rat, RatVec3, integer};

// -------------------------------------------------------------------------------------------------
// Material
// -------------------------------------------------------------------------------------------------

fn material(root: &Path, extension: &str) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(material(&path, extension));
        } else if path.extension().is_some_and(|carried| carried == extension) {
            found.push(path);
        }
    }
    found
}

fn read_deposit(root: &Path) -> Vec<(String, String)> {
    material(root, "lean")
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect()
}

fn read_corpus(root: &Path) -> Vec<Exposure> {
    material(root, "md")
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| expose(&path.display().to_string(), &text))
        })
        .collect()
}

// -------------------------------------------------------------------------------------------------
// Printing
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(94));
    println!("{title}");
    println!("{}", "=".repeat(94));
}

struct Controls {
    failed: Vec<String>,
}

impl Controls {
    fn new() -> Self {
        Self { failed: Vec::new() }
    }

    fn check(&mut self, name: &str, holds: bool, saying: &str) {
        println!(
            "  [{}] {name}\n        {saying}",
            if holds { "holds" } else { "FAILS" }
        );
        if !holds {
            self.failed.push(name.to_owned());
        }
    }
}

/// A passage population, whole when short and by its ends when long. Never a bare number.
///
/// One name may appear twice: the population is of **passages**, and two deposited artifacts of one
/// declaration are two passages that founded the same cell. That repetition is the route lineage,
/// not a duplicate.
fn passages(names: &[String]) -> String {
    match names.len() {
        0 => "(no passage -- an anonymous cell, which is a defect)".to_owned(),
        1..=3 => names.join(", "),
        _ => format!(
            "{} ... {}   [{} passages]",
            names[0],
            names[names.len() - 1],
            names.len()
        ),
    }
}

fn kind(kind: SiteKind) -> &'static str {
    match kind {
        SiteKind::Passage => "passage ",
        SiteKind::Symbol => "symbol  ",
        SiteKind::Statement => "statement",
    }
}

fn cut(name: &str, width: usize) -> String {
    if name.chars().count() <= width {
        name.to_owned()
    } else {
        format!("{}...", name.chars().take(width - 3).collect::<String>())
    }
}

fn vector(carried: &RatVec3) -> String {
    format!("({}, {}, {})", carried.x, carried.y, carried.z)
}

// -------------------------------------------------------------------------------------------------
// The declared layouts, which the real material cannot exhibit
// -------------------------------------------------------------------------------------------------

/// Two declarations recruiting the same two identifiers: a four-cycle, coordination two everywhere,
/// bipartite with **equal** parts, so the forced scale is zero and flat is the only fixed
/// configuration. `read_derivation` drops single-character tokens, so `: P` recruits nothing.
fn four_cycle() -> ConditionedCircuit {
    declared(vec![
        (
            "alpha".to_owned(),
            "theorem alpha : P := by\n  have one := carryOne\n  have two := carryTwo\n".to_owned(),
        ),
        (
            "beta".to_owned(),
            "theorem beta : P := by\n  have one := carryOne\n  have two := carryTwo\n".to_owned(),
        ),
    ])
}

/// One declaration recruiting three identifiers: a star, bipartite with parts of size three and
/// one. **This is where the nonflat fixed point lives.**
fn star() -> ConditionedCircuit {
    declared(vec![(
        "star".to_owned(),
        "theorem star : P := by\n  have one := carryOne\n  have two := carryTwo\n  \
         have three := carryThree\n"
            .to_owned(),
    )])
}

fn declared(deposit: Vec<(String, String)>) -> ConditionedCircuit {
    ConditionedBody::mount(deposit)
        .expect("the declared deposit reads")
        .circuit(
            &DerivationQuery::reaching(": P"),
            CircuitAperture::DEPOSITED_READER,
        )
        .expect("the declared circuit founds")
}

// -------------------------------------------------------------------------------------------------
// The run
// -------------------------------------------------------------------------------------------------

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let deposit_root = arguments
        .first()
        .cloned()
        .unwrap_or_else(|| "standing/output".to_owned());
    let corpora: Vec<String> = if arguments.len() > 1 {
        arguments[1..].to_vec()
    } else {
        vec![
            "reference/pureholonics-seed/src/pureholonics".to_owned(),
            "reference/holobrochos-a07ff376/src/soma".to_owned(),
        ]
    };

    let mut controls = Controls::new();

    rule("DERIVATION CURVATURE -- the layout, its deficits, the flow, and the write-back");

    let deposit = read_deposit(Path::new(&deposit_root));
    let exposures: Vec<Exposure> = corpora
        .iter()
        .flat_map(|root| read_corpus(Path::new(root)))
        .collect();
    println!("\nmaterial");
    println!(
        "  mathematical   {deposit_root:<52} {} artifacts",
        deposit.len()
    );
    for root in &corpora {
        println!(
            "  linguistic     {root:<52} {} wholes",
            read_corpus(Path::new(root)).len()
        );
    }
    if deposit.is_empty() || exposures.is_empty() {
        println!("\n  the material is absent; nothing can be read.");
        std::process::exit(2);
    }

    let mut body = ConditionedBody::mount(deposit).expect("the deposit reads");
    body.condition(&exposures);
    let query = DerivationQuery::reaching("(P : Prop) (h : P) : exactCarrier P");
    let aperture = CircuitAperture::STATEMENT_INCIDENT;
    let circuit = body
        .circuit(&query, aperture)
        .expect("the conditioned circuit founds");

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE LAYOUT -- the conditioned circuit as a hinge incidence");
    // ---------------------------------------------------------------------------------------------

    let layout = DerivationLayout::read(&circuit).expect("the circuit is a layout");
    println!("\n  aperture: {aperture:?}");
    println!("  query:    {}", query.statement);
    println!(
        "\n  sites        {:>5}   passages {:>4}   symbols {:>3}   statements {:>3}",
        layout.sites().len(),
        layout.of_kind(SiteKind::Passage).len(),
        layout.of_kind(SiteKind::Symbol).len(),
        layout.of_kind(SiteKind::Statement).len()
    );
    println!("  incidences   {:>5}", layout.incidences().len());
    println!(
        "  every cell is named: provenance total {}, anonymous sites {}",
        circuit.provenance_is_total(),
        layout
            .sites()
            .values()
            .filter(|site| site.passages.is_empty())
            .count()
    );

    println!("\n  the widest and the narrowest recruiters, by the derivation's own coordination:");
    let mut by_coordination: Vec<(usize, &str, SiteKind)> = layout
        .sites()
        .values()
        .map(|site| {
            (
                layout.coordination(site.vertex),
                site.name.as_str(),
                site.kind,
            )
        })
        .collect();
    by_coordination.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.cmp(right.1)));
    for (coordination, name, sort) in by_coordination.iter().take(6) {
        println!(
            "    n = {coordination:<4}  {}  {}",
            kind(*sort),
            cut(name, 62)
        );
    }
    println!("    ...");
    for (coordination, name, sort) in by_coordination.iter().rev().take(3).rev() {
        println!(
            "    n = {coordination:<4}  {}  {}",
            kind(*sort),
            cut(name, 62)
        );
    }

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE REALIZATION -- a closed oriented surface the curvature bridge reads");
    // ---------------------------------------------------------------------------------------------

    let mut realized = DerivationCurvatureBody::found(&circuit).expect("the layout realizes");
    let complex = &realized.scaffold().kinematic.complex;
    println!(
        "\n  the ribbon graph's face walks   {}",
        realized.face_walks()
    );
    println!(
        "  scaffold vertices               {}  ({} derivation sites + {} rim vertices, one per dart)",
        complex.vertices.len(),
        realized.layout.sites().len(),
        realized.rim().len()
    );
    println!("  scaffold faces                  {}", complex.faces.len());
    println!(
        "  edges, all hinged at founding   {}   narrowed to the derivation's own {}",
        complex.hinges.len(),
        realized.standing().kinematic.complex.hinges.len()
    );
    println!(
        "  every hinge spends {} along its own edge at founding",
        realized.target()
    );

    let reading = realized.reading().expect("the narrowed standing conducts");
    println!(
        "\n  conducted sites {}   refused {}   conducted incidences {}   refused incidences {}",
        reading.aperture.conducted.len(),
        reading.aperture.refused.len(),
        reading.aperture.conducted_hinges.len(),
        reading.aperture.refused_hinges.len()
    );
    println!(
        "  the aperture leaks at: {:?}",
        reading
            .aperture
            .porous_vertices()
            .keys()
            .collect::<Vec<_>>()
    );

    controls.check(
        "the realization conducts exactly the derivation's sites",
        reading.aperture.conducted.len() == layout.sites().len()
            && reading.aperture.conducted_hinges.len() == layout.incidences().len(),
        "every 0-cell of the circuit is an interior cycle carrying its own 1-cells, and nothing else \
         conducts",
    );
    controls.check(
        "the scaffold is refused by name and leaks nothing",
        reading.aperture.refused.len() == realized.rim().len()
            && reading.aperture.refused_hinges.is_empty()
            && reading.aperture.porous_vertices().is_empty(),
        "every rim vertex is an interior cycle carrying no incidence, and no retained incidence \
         touches one, so the aperture is hinge-closed",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE TWO FRAMES -- the orbit first, then the agreement");
    // ---------------------------------------------------------------------------------------------

    let agreement = realized.frame_agreement().expect("both frames read");
    let orbit = agreement.coordination_orbit();
    println!(
        "\n  frame D   the circuit's own 1-cells at unit response; no face, no position, no projection"
    );
    println!(
        "  frame S   curvature_bridge over the realized standing; scalar per hinge = response . edge_vector"
    );
    println!(
        "\n  the orbit: conducted sites the two frames read differently -- {} of {}",
        orbit.len(),
        agreement.pairs.len()
    );
    println!(
        "\n    {:<44} {:>10} {:>10} {:>12} {:>12}",
        "site", "n (scaffold)", "n (deriv)", "K (frame S)", "K (frame D)"
    );
    for pair in orbit.iter().take(8) {
        println!(
            "    {:<44} {:>10} {:>10} {:>12} {:>12}",
            cut(&pair.name, 44),
            pair.scaffold_coordination,
            pair.derivation_coordination,
            pair.surface_deficit,
            pair.derivation_deficit
        );
    }
    println!("    ... and the rest of the population");
    println!(
        "\n  refused by the aperture, with the reason it carries (first three of {}):",
        agreement.refused_scaffold.len()
    );
    for refused in agreement.refused_scaffold.iter().take(3) {
        println!("    {refused}");
    }

    controls.check(
        "the gauge acts non-trivially before agreement is read",
        !orbit.is_empty() && orbit.len() == agreement.pairs.len(),
        "the scaffold's face-derived coordination differs from the derivation's at every conducted \
         site, so agreement below is a measurement and not a tautology",
    );
    controls.check(
        "the scaffold link is exactly threefold",
        agreement.fold_holds(),
        "each corner contributes two rim vertices and each neighbour itself, so the realization's \
         link is 3n exactly -- a drift in the construction breaks this",
    );
    controls.check(
        "the two frames return the same deficit at every conducted site",
        agreement.deficit_disagreements().is_empty(),
        "the surface reading and the circuit's own reading agree, having first been shown distinct",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE CURVATURE -- every deficit with the passages it sits on");
    // ---------------------------------------------------------------------------------------------

    let mut deficits = realized.named_deficits(&reading);
    deficits.sort_by(|left, right| {
        left.deficit
            .cmp(&right.deficit)
            .then(left.name.cmp(&right.name))
    });
    println!(
        "\n  total deficit {}   flat {}   fixed-point class {}",
        reading.total_deficit(),
        reading.is_flat(),
        class(&reading.configuration.fixed_point())
    );
    println!(
        "\n  {:<52} {:>4} {:>7} {:>8}   founded by",
        "site", "n", "charge", "K"
    );
    println!("  {}", "-".repeat(90));
    for named in deficits.iter().filter(|named| !named.is_flat()) {
        println!(
            "  {:<52} {:>4} {:>7} {:>8}   {}",
            cut(&named.name, 52),
            named.coordination,
            named.combinatorial_charge,
            named.deficit,
            passages(&named.passages)
        );
    }
    let flat: Vec<&NamedDeficit> = deficits.iter().filter(|named| named.is_flat()).collect();
    println!(
        "\n  sites already flat at unit response (K = 0, coordination exactly {}): {}",
        6,
        if flat.is_empty() {
            "none".to_owned()
        } else {
            flat.iter()
                .map(|named| named.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        }
    );

    controls.check(
        "no deficit is anonymous",
        deficits.iter().all(|named| !named.passages.is_empty()),
        "every returned deficit carries the passages that founded the cell it sits on; an anonymous \
         deficit is not an artifact",
    );
    controls.check(
        "the layout carries curvature to move",
        deficits.iter().any(|named| !named.is_flat()),
        "at unit response the deficit is the recruitment coordination, and this layout is not flat",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[5]  THE FLOW -- what moved, what did not, and what the lift refused");
    // ---------------------------------------------------------------------------------------------

    let charges_before: BTreeMap<_, _> = reading.combinatorial_charges();
    let walked = realized.flow(2).expect("the flow applies");
    for step in &walked {
        report_step(step);
    }
    let after = realized.reading().expect("still conducts");
    let charges_after = after.combinatorial_charges();

    println!(
        "\n  the combinatorial charge, before and after two steps: {}",
        if charges_before == charges_after {
            "identical at every site"
        } else {
            "MOVED -- which would mean the circuit changed"
        }
    );
    println!(
        "  the deficit, before and after two steps:              {}",
        if reading.deficits() == after.deficits() {
            "identical -- the flow returned nothing"
        } else {
            "moved"
        }
    );

    controls.check(
        "a nonzero deficit moves under the flow",
        walked.iter().all(NamedFlowStep::moved_something),
        "each step moved a population of deficits, each named by its passages",
    );
    controls.check(
        "the total deficit is negated exactly, never dissipated",
        walked.iter().all(NamedFlowStep::total_is_negated),
        "discrete_curvature Consequence 2: sum K' = -sum K, so the flow is an involution on the \
         total and no convergence is claimed",
    );
    controls.check(
        "the combinatorial charge did not move",
        charges_before == charges_after,
        "the charge is 6 - n_v and moves only when the circuit changes; a run grading it would see \
         nothing and conclude wrongly",
    );
    controls.check(
        "the deficit did move",
        reading.deficits() != after.deficits(),
        "which is what is graded",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE PARTIAL ARM -- the lift refused, and the population it deposits");
    // ---------------------------------------------------------------------------------------------

    let naturally_refused: Vec<_> = walked
        .iter()
        .flat_map(|step| step.unlifted.iter())
        .collect();
    println!(
        "\n  incidences the flow's own steps could not lift -- the terminus the LAW reaches, where a"
    );
    println!("  revised scalar came out exactly zero and the response collapsed onto the origin:");
    if naturally_refused.is_empty() {
        println!("    none -- every conducted incidence still spends something along its own edge");
    }
    for refused in &naturally_refused {
        println!("\n    {}", cut(&refused.name, 70));
        println!(
            "        response {}  edge {}  spends {} along it, requested {}",
            vector(&refused.refusal.response_direction),
            vector(&refused.refusal.edge_vector),
            refused
                .refusal
                .response_direction
                .dot(&refused.refusal.edge_vector),
            refused.refusal.requested
        );
        println!("        founded by {}", passages(&refused.passages));
    }

    // The declared foil: an incidence carrying the defect `local_star`'s own octahedral fixture
    // carries -- a response orthogonal to its own edge. No lift exists for it and inventing a
    // direction there would spend geometry the layout never had.
    let mut foiled = DerivationCurvatureBody::found(&circuit).expect("realizes");
    let foil_hinge = *foiled
        .layout
        .incidences()
        .keys()
        .next()
        .expect("an incidence");
    let foil = foiled
        .refuse_one_lift(foil_hinge)
        .expect("the incidence exists");
    println!(
        "\n  the declared foil: {} carries a response orthogonal to its own edge",
        foil.name
    );
    println!("        founded by {}", passages(&foil.passages));
    let foil_step = foiled.flow(1).expect("the flow applies");
    let deposited = &foil_step[0].unlifted;
    println!(
        "\n  the partial arm lifted {} incidences and deposited {}:",
        foil_step[0].revised.len(),
        deposited.len()
    );
    for refused in deposited {
        println!(
            "    {}\n        response {}  edge {}  spends {} along it, requested {}",
            cut(&refused.name, 70),
            vector(&refused.refusal.response_direction),
            vector(&refused.refusal.edge_vector),
            refused
                .refusal
                .response_direction
                .dot(&refused.refusal.edge_vector),
            refused.refusal.requested
        );
        println!("        founded by {}", passages(&refused.passages));
    }

    controls.check(
        "the partial arm deposits its refusal as a population and lifts the rest",
        !foil_step[0].whole
            && deposited.len() == 1
            && foil_step[0].revised.len() == foiled.layout.incidences().len() - 1
            && deposited.iter().all(|refused| !refused.passages.is_empty()),
        "gate on the boolean, deposit the population: one incidence refused whole, every other \
         conducted incidence revised, and the refusal named by its passages",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[7]  THE WRITE-BACK -- consumed curvature changing local_star's own geometry");
    // ---------------------------------------------------------------------------------------------

    let consumed = realized.consumption_population();
    println!(
        "\n  incidences whose response the consumption revised: {} of {}",
        consumed.len(),
        realized.layout.incidences().len()
    );
    for incidence in consumed.iter().take(3) {
        println!(
            "    {}\n        founded by {}",
            cut(&incidence.name, 70),
            passages(&incidence.passages)
        );
    }
    println!("    ... and the rest of the population");

    let driven = consumed
        .iter()
        .find(|incidence| incidence.derived_only)
        .or_else(|| consumed.first())
        .map(|incidence| incidence.hinge)
        .expect("the consumption revised something");
    let consumption = realized
        .consume_into_geometry(driven, integer(1))
        .expect("local_star's event law enacts");

    println!(
        "\n  driving {} with a source current of {}",
        cut(&consumption.incidence, 62),
        consumption.source_current
    );
    println!("        founded by {}", passages(&consumption.passages));
    println!(
        "        response before {}\n        response after  {}",
        vector(&consumption.response_before),
        vector(&consumption.response_after)
    );
    println!(
        "\n  sites whose realized position differs between the two enactments ({}):",
        consumption.displaced.len()
    );
    println!(
        "\n    {:<46} {:>26} {:>26}",
        "site", "without consumption", "with consumption"
    );
    for displaced in consumption.displaced.iter().take(10) {
        println!(
            "    {:<46} {:>26} {:>26}",
            cut(&displaced.name, 46),
            vector(&displaced.without_consumption),
            vector(&displaced.with_consumption)
        );
        if !displaced.passages.is_empty() {
            println!("        founded by {}", passages(&displaced.passages));
        }
    }
    if consumption.displaced.len() > 10 {
        println!("    ... and the rest of the population");
    }

    // The negative pole. The write-back can reach the geometry only through a coordinate change, so
    // an event that drives nothing must move nothing even after the responses have been revised.
    let quiet = realized
        .consume_into_geometry(driven, integer(0))
        .expect("the quiet event enacts");
    println!(
        "\n  the same incidence driven with a source current of 0 displaces: {}",
        if quiet.displaced.is_empty() {
            "nothing".to_owned()
        } else {
            format!("{} sites -- which would be a defect", quiet.displaced.len())
        }
    );

    controls.check(
        "consuming the curvature moves the geometry local_star's own law returns",
        consumption.moved_the_geometry()
            && consumption.response_before != consumption.response_after,
        "local_star.rs:2082 spends geometry_responses[hinge] * (coordinate_change / 2); the revised \
         response reaches the positions through the owner that spends it",
    );
    controls.check(
        "an event that drives nothing moves nothing",
        quiet.displaced.is_empty() && quiet.response_before != quiet.response_after,
        "the negative pole: the revised response is carried and still nothing moves, so the \
         movement above is the coordinate change spending it and not the enactment itself",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[8]  THE DECLARED FALSIFIER -- 'the flow drives every deficit to zero' is FALSE");
    // ---------------------------------------------------------------------------------------------

    // A four-cycle: coordination two everywhere, bipartite with equal parts. Response three solves
    // 6 - 2r = 0, so it is flat, and a balanced bipartite component is fixed only when flat.
    let mut flat_layout =
        DerivationCurvatureBody::found_at_response(&four_cycle(), integer(3)).expect("realizes");
    let flat_reading = flat_layout.reading().expect("conducts");
    let flat_before = flat_layout.consumed_responses().clone();
    let flat_walk = flat_layout.flow(2).expect("the flow applies");
    println!(
        "\n  a flat region: two declarations recruiting the same two identifiers (a four-cycle)"
    );
    println!(
        "    every deficit {}   fixed-point class {}",
        if flat_reading.is_flat() {
            "= 0"
        } else {
            "NOT zero"
        },
        class(&flat_reading.configuration.fixed_point())
    );
    println!(
        "    after two steps: deficits moved {}   responses changed {}",
        flat_walk.iter().any(NamedFlowStep::moved_something),
        flat_layout.consumed_responses() != &flat_before
    );

    // A star: bipartite with parts of size three and one. Response four solves the alternation
    // h(centre) + h(leaf) = 0, and there the deficits are fixed and NOT zero.
    let mut fixed_layout =
        DerivationCurvatureBody::found_at_response(&star(), integer(4)).expect("realizes");
    let fixed_reading = fixed_layout.reading().expect("conducts");
    let mut fixed_deficits = fixed_layout.named_deficits(&fixed_reading);
    fixed_deficits.sort_by(|left, right| left.name.cmp(&right.name));
    let forced = fixed_layout.forced_component_scale().expect("bipartite");
    println!(
        "\n  a bipartite layout with unequal parts: one declaration recruiting three identifiers"
    );
    println!("    the deficits, which are FIXED and NOT zero:");
    for named in &fixed_deficits {
        println!(
            "      {:<20} n = {}   K = {:>4}   founded by {}",
            cut(&named.name, 20),
            named.coordination,
            named.deficit,
            passages(&named.passages)
        );
    }
    println!(
        "    fixed-point class {}",
        class(&fixed_reading.configuration.fixed_point())
    );
    println!(
        "    forced component scale, computed from the bipartition alone with no response read: {:?}",
        forced.values().map(Rat::to_string).collect::<Vec<_>>()
    );
    let fixed_walk = fixed_layout.flow(3).expect("the flow applies");
    let fixed_after = fixed_layout.reading().expect("conducts");
    println!(
        "    after three steps: any deficit moved {}   still nonflat {}",
        fixed_walk.iter().any(NamedFlowStep::moved_something),
        !fixed_after.is_flat()
    );

    controls.check(
        "a flat region stays exactly fixed",
        flat_reading.is_flat()
            && !flat_walk.iter().any(NamedFlowStep::moved_something)
            && flat_layout.consumed_responses() == &flat_before,
        "a balanced bipartite layout at the response solving 6 - 2r = 0 is flat, every revision is \
         exactly zero, and the write-back changes no response",
    );
    controls.check(
        "a bipartite layout with unequal parts sits FIXED at NONZERO deficit",
        !fixed_reading.is_flat()
            && !fixed_walk.iter().any(NamedFlowStep::moved_something)
            && !fixed_after.is_flat()
            && matches!(
                fixed_reading.configuration.fixed_point(),
                CurvatureFixedPoint::AlternatingTracedDeviation { .. }
            ),
        "the falsifier of 'the flow drives every deficit to zero', exhibited on a derivation layout",
    );
    controls.check(
        "the forced scale agrees with the observed alternation",
        match fixed_reading.configuration.fixed_point() {
            CurvatureFixedPoint::AlternatingTracedDeviation { component_scale } => {
                component_scale == forced && !forced.values().all(Rat::is_zero)
            }
            _ => false,
        },
        "forced_component_scale reads the bipartition and no response at all, so agreement with the \
         observed traced deviation is evidence rather than a restatement",
    );

    // ---------------------------------------------------------------------------------------------
    rule("DECLARED CONTROLS");
    // ---------------------------------------------------------------------------------------------

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {}", controls.failed.join(", "));
        std::process::exit(1);
    }
}

fn class(fixed: &CurvatureFixedPoint) -> String {
    match fixed {
        CurvatureFixedPoint::Flat => "flat".to_owned(),
        CurvatureFixedPoint::AlternatingTracedDeviation { component_scale } => format!(
            "alternating traced deviation, scale {:?}",
            component_scale
                .values()
                .map(Rat::to_string)
                .collect::<Vec<_>>()
        ),
        CurvatureFixedPoint::Moving { revisions } => {
            format!("moving, {} incidences revised", revisions.len())
        }
    }
}

fn report_step(step: &NamedFlowStep) {
    println!(
        "\n  step {}   total deficit {} -> {}   whole {}   refused {}",
        step.ordinal,
        step.total_before,
        step.total_after,
        step.whole,
        step.unlifted.len()
    );
    let mut moved = step.moved.clone();
    moved.sort_by(|left, right| {
        (&right.after - &right.before)
            .cmp(&(&left.after - &left.before))
            .then(left.name.cmp(&right.name))
    });
    println!(
        "    the deficits that moved ({} of {}), by how far, with the passages they sit on:",
        step.moved.len(),
        step.moved.len() + step.still.len()
    );
    println!(
        "\n    {:<50} {:>12} {:>12}   founded by",
        "site", "K before", "K after"
    );
    for entry in moved.iter().take(6) {
        println!(
            "    {:<50} {:>12} {:>12}   {}",
            cut(&entry.name, 50),
            entry.before,
            entry.after,
            passages(&entry.passages)
        );
    }
    if moved.len() > 12 {
        println!("    ...");
    }
    for entry in moved.iter().rev().take(3).rev() {
        println!(
            "    {:<50} {:>12} {:>12}   {}",
            cut(&entry.name, 50),
            entry.before,
            entry.after,
            passages(&entry.passages)
        );
    }
    let still: BTreeSet<&str> = step.still.iter().map(|entry| entry.name.as_str()).collect();
    println!(
        "\n    the deficits that did not move: {}",
        if still.is_empty() {
            "none".to_owned()
        } else {
            still.into_iter().collect::<Vec<_>>().join(", ")
        }
    );
}
