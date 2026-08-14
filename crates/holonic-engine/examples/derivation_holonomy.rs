//! Accumulate along the routes of a conditioned derivation circuit and return the disagreement.
//!
//! ```text
//! cargo run --release --example derivation_holonomy -- \
//!     standing/output \
//!     reference/pureholonics-seed/src/pureholonics \
//!     reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! The three paths are the mathematical deposit and two frames of linguistic material — the same
//! material `conditioned_derivation_body` runs on. That driver builds the circuit; this one
//! integrates over it.
//!
//! ## What this driver is for
//!
//! A **route** is a chain of recruitments between two declarations. The running sum of an exact
//! 1-cochain along a route is what the derivation accumulated getting there. When two routes join
//! the same two declarations and return different sums, that difference is holonomy, and it is the
//! artifact.
//!
//! It runs one control, in two halves that cannot both be satisfied by a trivial construction:
//!
//! > **A circuit with a genuine two-route disagreement AND one without, both exhibited.** Neither
//! > "always winds" nor "never winds" may pass, and before any agreement is read as evidence the
//! > two routes must be proved distinct as chains on this material.
//!
//! The fact that separates them is on the deposit already. `formal_carry` is declared by seven
//! artifacts and recruited by six other declarations: it is **both a result and a resource**, and
//! that is what makes the one-skeleton non-bipartite. Under the head-determined accumulation rule
//! the cochain admits a potential everywhere except at such a collision, so:
//!
//! ```text
//!   circuit W   the whole conditioned production                 winds, and only there
//!   circuit E   the same production with the seven artifacts
//!               that DECLARE `formal_carry` removed              exact, over hundreds of chords
//! ```
//!
//! Removing those artifacts does not remove the vertex — `formal_carry` is still recruited — it
//! removes every one-cell whose *head* is `formal_carry`. That is a structural ablation, and the
//! winding it removes is the load of the derivation that was being used as a resource.
//!
//! The second accumulation rule winds on **both** circuits, which is what keeps the returned
//! exactness attached to the rule rather than to the circuit's shape.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    ConditionedBody, ConditionedCircuit, DerivationQuery, Exposure, expose,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::derivation_integral::{
    AccumulationRule, HolonomyPopulation, NamedPotential, RouteDisagreement, accumulation,
    circuit_loads, loads_agree_with_the_boundary, potential_over, recruited_declaration_family,
    recruited_declarations, statement_lineage, without_declarations,
};

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

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
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

/// The declared base of every potential search: the lexicographically first zero-cell.
///
/// A spanning tree depends on where the walk departs, so the chord population and the retained
/// residuals do too. Naming the base is what makes the return a function of the circuit and this
/// declaration alone; it is a receiver choice and it is printed.
fn declared_base(circuit: &ConditionedCircuit) -> String {
    circuit
        .circuit
        .vertices()
        .keys()
        .next()
        .cloned()
        .unwrap_or_default()
}

fn report_potential(potential: &NamedPotential) {
    println!(
        "\n  rule {:<18} base {:?}",
        potential.rule.named(),
        potential.base
    );
    println!(
        "      chords tested {}   retained {}   reached one-cells left untouched: {}",
        potential.cycle_rank(),
        potential.retained.len(),
        if potential.search.unreached_cells.is_empty() {
            "none".to_owned()
        } else {
            format!("{:?}", potential.search.unreached_cells.len())
        }
    );
    if potential.admits_a_potential() {
        println!(
            "      the cochain is a COBOUNDARY over the reached component: every one of those \
             chords agreed"
        );
        return;
    }
    println!("      the certified remainder, by exact residual, every chord named:");
    for (residual, cells) in potential.residual_classes() {
        println!("        residual {residual}");
        for cell in &cells {
            println!("          {cell}");
        }
    }
    println!("      and what founded each retained chord:");
    for chord in &potential.retained {
        println!(
            "        {}  declared {}  the tree implied {}  standing {}",
            chord.cell, chord.declared, chord.implied, chord.residual
        );
        println!("          tail {}   head {}", chord.tail, chord.head);
        for passage in &chord.founding_passages {
            println!("          founded by {passage}");
        }
    }
}

/// One compared pair, whole: both routes, every cell they crossed with the passages that founded
/// it, and the three carriers' reading of the one residual.
fn exhibit(pair: &RouteDisagreement) {
    println!("\n  {}", pair.named());
    println!(
        "      residual {}   {}",
        pair.residual(),
        if pair.stands() {
            "STANDS -- this is holonomy"
        } else {
            "agrees"
        }
    );
    println!(
        "      the two routes are distinct as chains: {}",
        pair.routes_are_distinct()
    );
    for (side, route, founding, integral) in [
        (
            "left ",
            &pair.left,
            &pair.left_founding,
            &pair.disagreement.left,
        ),
        (
            "right",
            &pair.right,
            &pair.right_founding,
            &pair.disagreement.right,
        ),
    ] {
        println!(
            "      {side} {}   running sum {:?} -> total {}",
            route.named(),
            integral
                .partial_sums()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>(),
            integral.total
        );
        for carried in founding {
            println!(
                "            crossed {}  accumulating {}",
                carried.cell, carried.increment
            );
            for passage in &carried.passages {
                println!("              founded by {passage}");
            }
        }
    }
    println!(
        "      three readings of that one residual:  running sum {}   leader quadrature {}   \
         absorptive face {}",
        pair.residual(),
        pair.leader_residual,
        pair.reflected_residual
    );
    println!(
        "      leader lineage   left FOUND {} RIDE {}   right FOUND {} RIDE {}   germwise oracle \
         {} and {}",
        pair.leader_left.found_count(),
        pair.leader_left.ride_count(),
        pair.leader_right.found_count(),
        pair.leader_right.ride_count(),
        pair.oracle_left,
        pair.oracle_right
    );
    let refoundings = pair.refoundings();
    if refoundings.is_empty() {
        println!("      the founded axis predicted every extension: no refounding was retained");
    } else {
        for (route, index, residual) in &refoundings {
            println!(
                "      refounded on {route} at extension {index}, the axis was wrong by exactly \
                 {residual}"
            );
        }
    }
    println!(
        "      the reflection: structurally causal {}   the second route sits at the advanced \
         indices {:?}",
        pair.response.is_causal(),
        pair.advanced_witness()
            .iter()
            .map(|(index, value)| format!("{index}:{value}"))
            .collect::<Vec<String>>()
    );
    println!(
        "      transfer polynomial extends over infinity {}   pole order there {}   both faces \
         lock {}   law holds {}",
        pair.holomorphy.extends_over_infinity(),
        pair.holomorphy.pole_order_at_infinity(),
        pair.lock.locks(),
        pair.lock.law_holds()
    );
}

fn report_population(population: &HolonomyPopulation) {
    println!("\n  {}", population.family);
    println!("  accumulation rule: {}", population.rule.named());
    if population.is_empty() {
        println!("  this family is empty on this circuit.");
        return;
    }
    println!("\n  the holonomy population, by exact residual, every pair named:");
    for (residual, pairs) in population.residual_classes() {
        println!(
            "    residual {residual}{}",
            if residual == num_bigint::BigInt::from(0) {
                "   (the two routes agreed)"
            } else {
                "   (STANDS)"
            }
        );
        for named in &pairs {
            println!("      {named}");
        }
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let deposit_root = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| "standing/output".to_owned()),
    );
    let frame_a = PathBuf::from(
        arguments
            .get(1)
            .cloned()
            .unwrap_or_else(|| "reference/pureholonics-seed/src/pureholonics".to_owned()),
    );
    let frame_b = PathBuf::from(
        arguments
            .get(2)
            .cloned()
            .unwrap_or_else(|| "reference/holobrochos-a07ff376/src/soma".to_owned()),
    );

    let deposit = read_deposit(&deposit_root);
    let corpus_a = read_corpus(&frame_a);
    if deposit.is_empty() || corpus_a.is_empty() {
        eprintln!(
            "material missing: deposit {} artifacts, frame A {} wholes",
            deposit.len(),
            corpus_a.len()
        );
        std::process::exit(2);
    }
    let corpus_b = read_corpus(&frame_b);

    let mut controls = Controls::new();

    let unconditioned = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let mut body = unconditioned.clone();
    body.condition(&corpus_a);

    // The query the production carried furthest, chosen exactly as `conditioned_derivation_body`
    // chooses it: the statement this body returned the most passages for.
    let statements = unconditioned.standing_statements();
    let query_statement = statements
        .iter()
        .max_by_key(|statement| {
            body.derive(&DerivationQuery::reaching(statement))
                .map(|passages| passages.len())
                .unwrap_or(0)
        })
        .cloned()
        .expect("the deposit reached a statement");
    let query = DerivationQuery::reaching(&query_statement);

    let aperture = CircuitAperture::STATEMENT_INCIDENT;
    let whole = match body.circuit(&query, aperture) {
        Ok(circuit) => circuit,
        Err(refusal) => {
            eprintln!("the circuit was refused: {refusal}");
            std::process::exit(2);
        }
    };

    rule("DERIVATION HOLONOMY -- what two routes accumulated, and what their difference retains");
    println!("\nmaterial");
    println!(
        "  mathematical   {:<52} {} artifacts",
        deposit_root.display(),
        deposit.len()
    );
    println!(
        "  linguistic A   {:<52} {} wholes",
        frame_a.display(),
        corpus_a.len()
    );
    println!(
        "  linguistic B   {:<52} {} wholes   (read only to confirm the frame, not integrated over)",
        frame_b.display(),
        corpus_b.len()
    );
    println!("\n  the query carried forward: {query_statement}");
    println!("  aperture: {aperture:?}");

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE COLLISION -- a derivation that is both a result and a resource");

    let recruited = recruited_declarations(&whole);
    let loads = circuit_loads(&whole);
    println!(
        "\n  every declaration vertex some OTHER declaration recruited, with the load it carries:"
    );
    if recruited.is_empty() {
        println!(
            "    (none -- this circuit is head-separated and the head-determined rule cannot wind)"
        );
    }
    for declaration in &recruited {
        println!(
            "    {declaration}   its own recruitment load {}",
            loads.route_load(declaration)
        );
        println!("      it recruits, and each of those is a route out of it:");
        if let Some(carried) = loads.recruitment.get(declaration) {
            for (symbol, count) in carried {
                println!("        {symbol} named {count} times");
            }
        }
    }
    let recruiting: BTreeMap<String, BTreeSet<String>> = recruited
        .iter()
        .map(|declaration| {
            (
                declaration.clone(),
                loads
                    .recruitment
                    .iter()
                    .filter(|(key, carried)| {
                        key.as_str() != declaration.as_str() && carried.contains_key(declaration)
                    })
                    .map(|(key, _)| key.clone())
                    .collect(),
            )
        })
        .collect();
    for (declaration, recruiters) in &recruiting {
        println!("\n  every declaration that recruits {declaration}, by name:");
        for recruiter in recruiters {
            println!("    {recruiter}");
        }
    }

    // The structural ablation: remove the artifacts that DECLARE the collided names. The vertex
    // survives -- it is still recruited -- and every one-cell whose head it was does not.
    let separated = match without_declarations(&whole, &recruited) {
        Ok(circuit) => circuit,
        Err(refusal) => {
            eprintln!("the ablated circuit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let whole_cells = whole.cell_names();
    let separated_cells = separated.cell_names();
    let removed: BTreeSet<String> = whole_cells.difference(&separated_cells).cloned().collect();
    println!(
        "\n  circuit W: the whole conditioned production, {} passages",
        whole.passages.len()
    );
    println!(
        "  circuit E: the same production with every artifact DECLARING {recruited:?} removed, {} \
         passages",
        separated.passages.len()
    );
    println!("\n  the one-cells the ablation removed, each named:");
    for cell in &removed {
        println!("    {cell}");
    }
    println!(
        "\n  the vertex survives the ablation: {} is still a zero-cell of circuit E",
        recruited
            .iter()
            .filter(|name| separated.circuit.vertices().contains_key(name.as_str()))
            .cloned()
            .collect::<Vec<String>>()
            .join(" ")
    );

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE POTENTIAL -- a spanning tree, and every chord it cannot repair");

    let base_whole = declared_base(&whole);
    let base_separated = declared_base(&separated);
    let mut potentials: BTreeMap<(&str, AccumulationRule), NamedPotential> = BTreeMap::new();
    for (name, circuit, base) in [
        ("W", &whole, &base_whole),
        ("E", &separated, &base_separated),
    ] {
        println!("\n  circuit {name}");
        for accumulation_rule in [
            AccumulationRule::RouteLoad,
            AccumulationRule::RecruitmentLoad,
        ] {
            let cochain = accumulation(circuit, accumulation_rule);
            match potential_over(circuit, &cochain, accumulation_rule, base) {
                Ok(potential) => {
                    report_potential(&potential);
                    potentials.insert((name, accumulation_rule), potential);
                }
                Err(refusal) => println!("    {accumulation_rule:?} refused: {refusal}"),
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule(
        "[3]  THE HOLONOMY -- reaching a derivation as a resource against reaching it as a result",
    );

    let whole_route_load = accumulation(&whole, AccumulationRule::RouteLoad);
    let collision_family = match recruited_declaration_family(
        &whole,
        &whole_route_load,
        AccumulationRule::RouteLoad,
    ) {
        Ok(population) => population,
        Err(refusal) => {
            eprintln!("the collision family was refused: {refusal}");
            std::process::exit(2);
        }
    };
    report_population(&collision_family);
    println!(
        "\n  the law this family returns: the residual is exactly minus the load of the \
         declaration reached."
    );
    for declaration in &recruited {
        println!(
            "    reaching {declaration} winds by {}",
            -loads.route_load(declaration)
        );
    }
    println!("\n  every pair of this family, whole:");
    for pair in &collision_family.compared {
        exhibit(pair);
    }

    let separated_route_load = accumulation(&separated, AccumulationRule::RouteLoad);
    let separated_family = recruited_declaration_family(
        &separated,
        &separated_route_load,
        AccumulationRule::RouteLoad,
    )
    .expect("the ablated family founds");
    println!(
        "\n  the same family on circuit E: {}",
        if separated_family.is_empty() {
            "empty -- nothing is both a result and a resource there"
        } else {
            "NOT empty, which would mean the ablation missed a collision"
        }
    );

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE STATEMENT LINEAGE -- crossing the result against crossing a shared identifier");

    println!(
        "\n  the traversal visits every declaration that reached the query statement, in canonical \
         order,\n  and compares at each adjacent pair. No declaration is privileged and no pair is \
         chosen for\n  what it returns."
    );
    let mut lineages: BTreeMap<&str, HolonomyPopulation> = BTreeMap::new();
    for (name, circuit) in [("W", &whole), ("E", &separated)] {
        let cochain = accumulation(circuit, AccumulationRule::RecruitmentLoad);
        match statement_lineage(
            circuit,
            &cochain,
            AccumulationRule::RecruitmentLoad,
            &query_statement,
        ) {
            Ok(population) => {
                println!("\n  circuit {name}");
                report_population(&population);
                lineages.insert(name, population);
            }
            Err(refusal) => println!("\n  circuit {name}: refused: {refusal}"),
        }
    }

    let forced = {
        let cochain = accumulation(&whole, AccumulationRule::RouteLoad);
        statement_lineage(
            &whole,
            &cochain,
            AccumulationRule::RouteLoad,
            &query_statement,
        )
        .expect("the lineage founds")
    };
    println!(
        "\n  the same traversal under the head-determined rule returns these standing pairs, and \
         that is a TAUTOLOGY, not evidence:"
    );
    for pair in forced.standing() {
        println!("    {}", pair.named());
    }
    if forced.standing().is_empty() {
        println!("    (none -- every pair agreed, as a head-determined rule forces)");
    }
    println!(
        "  both routes are head-determined, so both return the same difference of loads whatever \
         the material says."
    );
    println!("  it is recorded so it is never read as an exactness result.");

    if let Some(lineage) = lineages.get("W") {
        if let Some(pair) = lineage.standing().first() {
            println!("\n  a standing pair of the lineage, whole:");
            exhibit(pair);
        }
        if let Some(pair) = lineage.agreeing().first() {
            println!(
                "\n  an AGREEING pair of the lineage, whole -- and its two routes are distinct:"
            );
            exhibit(pair);
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    let multiplicity = body
        .circuit(&query, CircuitAperture::PER_ROUTE_MULTIPLICITY)
        .ok()
        .and_then(|circuit| loads_agree_with_the_boundary(&circuit));

    let lineage_w = lineages.get("W");
    let lineage_e = lineages.get("E");
    let route_load_w = potentials.get(&("W", AccumulationRule::RouteLoad));
    let route_load_e = potentials.get(&("E", AccumulationRule::RouteLoad));
    let recruitment_load_e = potentials.get(&("E", AccumulationRule::RecruitmentLoad));

    controls.check(
        "the deposit carries a declaration that is itself recruited",
        !recruited.is_empty() && recruiting.values().all(|carried| !carried.is_empty()),
        "without one, nothing here can wind and the winding half of this control is unreachable",
    );
    controls.check(
        "the ablation removed one-cells and kept the vertex",
        !removed.is_empty()
            && recruited
                .iter()
                .all(|name| separated.circuit.vertices().contains_key(name.as_str())),
        "removing the declaring artifacts must remove the cells the collision founded, not the \
         identifier",
    );
    controls.check(
        "every cell of both circuits traces back to a passage",
        whole.provenance_is_total() && separated.provenance_is_total(),
        "a cell no passage names makes every returned route anonymous",
    );
    controls.check(
        "the load table agrees with the complex's own boundary coefficients",
        multiplicity == Some(true),
        "an independent implementation of the same recruitment multiset, read off the incidence \
         the founding wrote",
    );
    controls.check(
        "circuit W: the head-determined rule does NOT admit a potential",
        route_load_w.is_some_and(|potential| !potential.admits_a_potential()),
        "a genuine two-route disagreement, retained as a chord obstruction with an exact residual",
    );
    controls.check(
        "every retained chord of circuit W sits at the recruited declaration",
        route_load_w.is_some_and(|potential| {
            !potential.retained.is_empty()
                && potential
                    .retained
                    .iter()
                    .all(|chord| recruited.contains(&chord.tail) || recruited.contains(&chord.head))
        }),
        "the winding is located, not merely present",
    );
    controls.check(
        "circuit E: the head-determined rule DOES admit a potential",
        route_load_e.is_some_and(|potential| potential.admits_a_potential()),
        "the other half: a circuit whose every pair of routes agrees, so 'always winds' cannot pass",
    );
    controls.check(
        "and circuit E tested a non-empty chord population to say so",
        route_load_e.is_some_and(|potential| potential.cycle_rank() > 0),
        "an empty remainder over no chords is a vacuous receipt; every one of these could have \
         failed",
    );
    controls.check(
        "circuit E still winds under the second rule",
        recruitment_load_e.is_some_and(|potential| !potential.admits_a_potential()),
        "so the exactness above belongs to the accumulation rule, not to the ablated circuit's shape",
    );
    controls.check(
        "the collision family is non-empty on W and empty on E",
        !collision_family.is_empty() && separated_family.is_empty(),
        "the family exists exactly where a derivation is both a result and a resource",
    );
    controls.check(
        "every pair of the collision family stands, at exactly minus the load reached",
        collision_family
            .compared
            .iter()
            .all(|pair| pair.stands() && *pair.residual() == -loads.route_load(&pair.left.to)),
        "the holonomy is the load of the derivation being used as a resource",
    );
    controls.check(
        "the statement lineage exhibits BOTH a standing pair and an agreeing pair",
        lineage_w.is_some_and(|lineage| {
            !lineage.standing().is_empty() && !lineage.agreeing().is_empty()
        }),
        "neither 'always winds' nor 'never winds' can pass on this material",
    );
    controls.check(
        "every compared pair is distinct as a chain",
        collision_family.every_pair_is_distinct()
            && lineage_w.is_some_and(HolonomyPopulation::every_pair_is_distinct)
            && lineage_e.is_some_and(HolonomyPopulation::every_pair_is_distinct),
        "a pair whose cycle is zero cannot disagree on any cochain and its agreement is vacuous",
    );
    controls.check(
        "the three carriers return the same residual on every pair",
        collision_family.every_reading_agrees()
            && lineage_w.is_some_and(HolonomyPopulation::every_reading_agrees)
            && lineage_e.is_some_and(HolonomyPopulation::every_reading_agrees),
        "running sum in Z, leader quadrature in Q, and the absorptive face of the pair's response",
    );
    controls.check(
        "every leader lineage is graded by the germwise antiderivative that costs less",
        collision_family.every_leader_is_graded()
            && lineage_w.is_some_and(HolonomyPopulation::every_leader_is_graded)
            && lineage_e.is_some_and(HolonomyPopulation::every_leader_is_graded),
        "the independent implementation returns the same rational and cannot return the lineage",
    );
    controls.check(
        "every route both FOUNDs and RIDEs",
        collision_family.every_leader_founds_and_rides()
            && lineage_w.is_some_and(HolonomyPopulation::every_leader_founds_and_rides)
            && lineage_e.is_some_and(HolonomyPopulation::every_leader_founds_and_rides),
        "a lineage that only founds has degenerated to grain-only and the ride half is unexercised",
    );
    controls.check(
        "every pair exercises the reflection and its law holds",
        collision_family.every_reflection_law_holds()
            && collision_family.every_pair_exercises_the_reflection()
            && lineage_w.is_some_and(|star| {
                star.every_reflection_law_holds() && star.every_pair_exercises_the_reflection()
            })
            && lineage_e.is_some_and(|star| {
                star.every_reflection_law_holds() && star.every_pair_exercises_the_reflection()
            }),
        "a response supported only at the stimulus locks whatever it was and proves nothing",
    );
    controls.check(
        "the second route is the retained obstruction to extending over infinity",
        collision_family.every_second_route_is_the_obstruction()
            && lineage_w.is_some_and(HolonomyPopulation::every_second_route_is_the_obstruction)
            && lineage_e.is_some_and(HolonomyPopulation::every_second_route_is_the_obstruction),
        "a pair that reads structurally causal is a pair that was never two routes",
    );
    controls.check(
        "the head-determined rule cannot wind on the statement lineage, and this is declared \
         a tautology",
        !forced.winds() && !forced.is_empty(),
        "recorded so a forced agreement is never carried as an exactness result",
    );

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
