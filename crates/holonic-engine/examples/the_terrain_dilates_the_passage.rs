//! Conduct the machine's own deposited derivations as an exact population current, and return the
//! passage delays the terrain's capacitance dilated.
//!
//! `crates/holonic-engine/src/receiver_current.rs` is a transport law with one caller, in the frozen
//! laboratory, which pins `characteristic_delay: 1` on every edge and has never been pointed at a
//! derivation circuit. This driver points it at `standing/output` through `derivation_atlas`.
//!
//! The question it answers is the one
//! `research/records/2026-08-08_FACES_GROW_FROM_COLLOCATION_AND_THE_ATOM_IS_NOT_EMPTY.md` §4(iv)
//! names: seventeen of eighteen recruited identifiers in that deposit are **atoms** — nothing
//! declares them, so the recruitment closure that gives a name its meaning is empty — and an
//! elaboration organ concluded they are therefore undiscriminable. An atom recruited by ninety
//! derivations is not the same terrain as one recruited by two, and the difference is available
//! **without a score**, because capacitance dilates a passage delay rather than ranking anything.
//!
//! ```text
//! cargo run --release --example the_terrain_dilates_the_passage -- standing/output
//! ```
//!
//! The driver exits non-zero if any declared control fails. The controls are stated in
//! `holonic_engine::derivation_capacitance`'s own documentation and the three control circuits carry
//! their predicted dilations in their doc comments, written before this deposit was read.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{
    found_circuit, read_derivation, CircuitAperture, Derivation, DerivationCircuit,
};
use holonic_engine::derivation_capacitance::{
    disjoint_terrain, many_result_star, one_result_star, orient_passages, CapacitanceMapping,
    CapacitanceReading, CapacityLaw, CharacteristicDelayLaw, DilationClasses,
};
use holonic_engine::name_elaboration::ElaborationDeposit;
use num_bigint::BigUint;
use num_traits::One;

/// Every `.lean` artifact under `root`, in a stable filename order. The same walk
/// `derivation_atlas_reader` performs, so the two drivers read one deposit.
fn artifact_paths(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(artifact_paths(&path));
        } else if path.extension().is_some_and(|kind| kind == "lean") {
            found.push(path);
        }
    }
    found
}

/// A population, rendered whole. An elision is a count wearing the population's name.
fn population(indent: &str, members: impl IntoIterator<Item = String>) -> String {
    let mut lines = Vec::new();
    let mut line = String::new();
    for member in members {
        if !line.is_empty() && line.len() + member.len() + 2 > 96 {
            lines.push(std::mem::take(&mut line));
        }
        if !line.is_empty() {
            line.push_str(", ");
        }
        line.push_str(&member);
    }
    if !line.is_empty() {
        lines.push(line);
    }
    if lines.is_empty() {
        return format!("{indent}(empty)");
    }
    lines
        .into_iter()
        .map(|line| format!("{indent}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_delays(reading: &CapacitanceReading, identifier: &str) -> String {
    let Some(site) = reading.site(identifier) else {
        return "-".to_owned();
    };
    let mut delays: Vec<u64> = site
        .departures
        .iter()
        .flat_map(|departure| departure.passages.iter())
        .map(|passage| passage.passage_delay)
        .collect();
    delays.sort_unstable();
    delays.dedup();
    if delays.is_empty() {
        return "-".to_owned();
    }
    delays
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join("/")
}

/// The delay population, whole: every identifier the circuit carries, with what it cost to leave it.
fn print_delay_population(reading: &CapacitanceReading) {
    println!(
        "  capacity law {:?}   delay law {:?}   horizon {}",
        reading.capacity_law, reading.delay_law, reading.horizon
    );
    println!(
        "    {:<28} {:>8} {:>7} {:>7} {:>10} {:>7} {:>9} {:>8}",
        "identifier", "capacity", "onward", "branch", "co-present", "rounds", "delay", "arrival"
    );
    for site in &reading.sites {
        let (branch, co_present, rounds) = match site.departures.first() {
            Some(departure) => (
                departure.branch_population.to_string(),
                departure.co_present_branch_population.to_string(),
                departure.service_rounds.to_string(),
            ),
            None => ("-".to_owned(), "-".to_owned(), "-".to_owned()),
        };
        let arrival = site
            .arrival_chronology
            .map_or_else(|| "unreached".to_owned(), |at| at.to_string());
        println!(
            "    {:<28} {:>8} {:>7} {:>7} {:>10} {:>7} {:>9} {:>8}{}",
            site.identifier,
            site.capacity,
            site.onward_passages,
            branch,
            co_present,
            rounds,
            render_delays(reading, &site.identifier),
            arrival,
            if site.terminal() { "  terminal" } else { "" }
        );
    }
}

fn print_classes(classes: &DilationClasses) {
    for (rounds, members) in &classes.by_service_rounds {
        println!("    service rounds {rounds}");
        println!(
            "{}",
            population("      ", members.iter().cloned())
        );
    }
    println!("    terminal — no onward passage, capacity inert, no service round");
    println!("{}", population("      ", classes.terminal.iter().cloned()));
    if !classes.unreached.is_empty() {
        println!("    unreached within the grown horizon");
        println!("{}", population("      ", classes.unreached.iter().cloned()));
    }
}

fn found(
    circuit: &DerivationCircuit,
    derivations: &[Derivation],
    sources: &[String],
    capacity_law: CapacityLaw,
    delay_law: CharacteristicDelayLaw,
) -> CapacitanceMapping {
    CapacitanceMapping::found(circuit, derivations, sources, capacity_law, delay_law)
        .expect("the derivation circuit founds a passage ecology")
}

fn read(mapping: &CapacitanceMapping) -> CapacitanceReading {
    mapping.read().expect("the current conducts")
}

/// The service-round class of one identifier, as a single value when it departed once.
fn rounds_of(reading: &CapacitanceReading, identifier: &str) -> Option<BigUint> {
    reading
        .site(identifier)?
        .service_rounds()
        .first()
        .cloned()
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "standing/output".to_owned());
    let paths = artifact_paths(Path::new(&root));

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=capacitance dilates a passage delay; it never ranks a population");
    println!("standing={root}");

    if paths.is_empty() {
        println!("\nFAILED — no deposited derivations at {root}");
        std::process::exit(1);
    }

    let sources: Vec<String> = paths
        .iter()
        .filter_map(|path| std::fs::read_to_string(path).ok())
        .collect();
    let mut derivations = Vec::new();
    let mut carried_sources = Vec::new();
    for text in &sources {
        if let Some(derivation) = read_derivation(text) {
            derivations.push(derivation);
            carried_sources.push(text.clone());
        }
    }
    println!(
        "\nread {} artifacts, {} carrying a theorem declaration",
        paths.len(),
        derivations.len()
    );

    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    // ---------------------------------------------------------------------------------------------
    // The mapping, and where each role comes from
    // ---------------------------------------------------------------------------------------------

    println!("\nTHE MAPPING, AND WHERE EACH ROLE COMES FROM");
    println!("-------------------------------------------");
    println!("  site                 a 0-cell of the circuit: a declaration produced, a symbol");
    println!("                       recruited, or a result reached");
    println!("  passage              a 1-cell, oriented by the sign its FOUNDED BOUNDARY carries.");
    println!("                       `+derivation, -symbol` is a difference head - tail, so the");
    println!("                       passage runs symbol -> derivation: current flows from the");
    println!("                       terrain a proof stood on into the proof that stood on it");
    println!("  capacity             the number of onward heads the circuit's coarsest declared");
    println!("                       receiver — the RESULT REACHED — can tell apart");
    println!("  branch population    accumulated by the transport law, not computed here");
    println!("  competing occupancy  branch population x active onward passages, the law's own");
    println!("  source continuity    NOT in the circuit. `Derivation` carries no file, no line, no");
    println!("                       position. Supplied instead by the deposited source: one plus");
    println!("                       the minimal line separation between the theorem line and the");
    println!("                       nearest line naming the recruited identifier");

    let deposited = found_circuit(&derivations, CircuitAperture::DEPOSITED_READER)
        .expect("the deposited reader's aperture is admissible");
    let per_route = found_circuit(&derivations, CircuitAperture::PER_ROUTE)
        .expect("the per-route aperture is admissible");

    let oriented = orient_passages(&deposited).expect("every 1-cell is oriented");
    let orientation_agrees = deposited.recruitments().keys().all(|(head, tail)| {
        oriented
            .iter()
            .any(|passage| &passage.tail == tail && &passage.head == head)
    });
    println!(
        "\n  the orientation read from {} founded boundaries agrees with the recruitment keys: {}",
        oriented.len(),
        orientation_agrees
    );
    holds.push((
        "the passage direction is read off the founded boundary sign, not declared",
        orientation_agrees,
        format!("{} 1-cells oriented", oriented.len()),
    ));

    // ---------------------------------------------------------------------------------------------
    // CONTROL 5 — the declared control circuits, with their predictions stated first
    // ---------------------------------------------------------------------------------------------

    println!("\nTHE DECLARED CONTROL CIRCUITS AND THEIR PREDICTED DILATIONS");
    println!("-----------------------------------------------------------");
    println!("  one_result_star(n)   predicted  shared terrain n rounds, every private symbol 1");
    println!("  many_result_star(n)  predicted  FLAT — every onward head is distinguishable");
    println!("  disjoint_terrain(n)  predicted  FLAT — there is no shared terrain to congest");
    println!("  occurrence capacity  predicted  FLAT at the source layer, by theorem: every onward");
    println!("                                  head named the identifier at least once, so the");
    println!("                                  occurrence total is never below the fan-out");

    for arms in [3usize, 7] {
        let control = one_result_star(arms);
        let circuit = found_circuit(&control, CircuitAperture::DEPOSITED_READER).expect("admissible");
        let reading = read(&found(
            &circuit,
            &control,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        ));
        let shared = rounds_of(&reading, "sharedTerrain");
        let private = rounds_of(&reading, "private0");
        let predicted = shared == Some(BigUint::from(arms)) && private == Some(BigUint::one());
        println!(
            "  one_result_star({arms})    shared {:?} rounds, private0 {:?} rounds  -> {}",
            shared.clone().map(|rounds| rounds.to_string()),
            private.clone().map(|rounds| rounds.to_string()),
            if predicted { "as predicted" } else { "DISAGREES" }
        );
        holds.push((
            "one_result_star dilates the shared terrain by exactly its fan-out",
            predicted,
            format!("arms={arms} shared={shared:?} private={private:?}"),
        ));
    }

    for (name, control) in [
        ("many_result_star(7)", many_result_star(7)),
        ("disjoint_terrain(7)", disjoint_terrain(7)),
    ] {
        let circuit = found_circuit(&control, CircuitAperture::DEPOSITED_READER).expect("admissible");
        let reading = read(&found(
            &circuit,
            &control,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        ));
        let classes = reading.dilation_classes();
        println!(
            "  {name}   classes {:?}  -> {}",
            classes
                .by_service_rounds
                .keys()
                .map(BigUint::to_string)
                .collect::<Vec<_>>(),
            if classes.is_vacuous() {
                "FLAT, as predicted"
            } else {
                "DISAGREES — spread where none was predicted"
            }
        );
        holds.push((
            "the control with nothing to congest returns one service-round class",
            classes.is_vacuous(),
            format!("{name} -> {} classes", classes.by_service_rounds.len()),
        ));
    }

    // ---------------------------------------------------------------------------------------------
    // The delay population over the real deposit
    // ---------------------------------------------------------------------------------------------

    println!("\nTHE DELAY POPULATION — BY DECLARATION, UNIFORM CHARACTERISTIC DELAY");
    println!("-------------------------------------------------------------------");
    let by_declaration = found(
        &deposited,
        &derivations,
        &[],
        CapacityLaw::DistinguishableResults,
        CharacteristicDelayLaw::Uniform,
    );
    let declaration_reading = read(&by_declaration);
    println!(
        "  terrain — every 0-cell with an empty incoming incidence, {} of them",
        declaration_reading.terrain.len()
    );
    println!(
        "{}",
        population("    ", declaration_reading.terrain.iter().cloned())
    );
    print_delay_population(&declaration_reading);
    let declaration_classes = declaration_reading.dilation_classes();
    println!("\n  the classes this dilation induces");
    print_classes(&declaration_classes);
    println!("\n  deferred arrivals — retained testimony, never discarded failed paths");
    for (site, chronologies) in &declaration_reading.deferred {
        println!(
            "    {site} at {}",
            chronologies
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }

    println!("\nTHE DELAY POPULATION — BY ROUTE, UNIFORM CHARACTERISTIC DELAY");
    println!("-------------------------------------------------------------");
    println!("  one 0-cell per artifact, so the fan-out of an identifier is the number of ROUTES");
    println!("  that stood on it rather than the number of declaration names");
    let by_route = found(
        &per_route,
        &derivations,
        &[],
        CapacityLaw::DistinguishableResults,
        CharacteristicDelayLaw::Uniform,
    );
    let route_reading = read(&by_route);
    // Every route vertex is terminal here, so the departing population is exactly the terrain.
    let route_terrain: Vec<&str> = route_reading
        .terrain
        .iter()
        .map(String::as_str)
        .collect();
    println!(
        "  capacity law {:?}   delay law {:?}   horizon {}",
        route_reading.capacity_law, route_reading.delay_law, route_reading.horizon
    );
    println!(
        "    {:<28} {:>8} {:>7} {:>7} {:>10} {:>7} {:>9}",
        "identifier", "capacity", "onward", "branch", "co-present", "rounds", "delay"
    );
    for identifier in &route_terrain {
        let site = route_reading.site(identifier).expect("a terrain site");
        let departure = site.departures.first().expect("terrain departs");
        println!(
            "    {:<28} {:>8} {:>7} {:>7} {:>10} {:>7} {:>9}",
            site.identifier,
            site.capacity,
            site.onward_passages,
            departure.branch_population,
            departure.co_present_branch_population,
            departure.service_rounds,
            render_delays(&route_reading, identifier)
        );
    }
    let route_classes = route_reading.dilation_classes();
    println!("\n  the classes this dilation induces (the {} route vertices are terminal)", route_classes.terminal.len());
    for (rounds, members) in &route_classes.by_service_rounds {
        println!("    service rounds {rounds}");
        println!("{}", population("      ", members.iter().cloned()));
    }

    // ---------------------------------------------------------------------------------------------
    // CONTROL 1 — is the dilation non-trivial on this material?
    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROL — IS THE DILATION NON-TRIVIAL ON THIS MATERIAL?");
    println!("-------------------------------------------------------");
    println!(
        "  by declaration  {} service-round classes over {} departing identifiers",
        declaration_classes.by_service_rounds.len(),
        declaration_reading
            .sites
            .iter()
            .filter(|site| !site.departures.is_empty())
            .count()
    );
    println!(
        "  by route        {} service-round classes over {} departing identifiers",
        route_classes.by_service_rounds.len(),
        route_reading
            .sites
            .iter()
            .filter(|site| !site.departures.is_empty())
            .count()
    );
    let non_trivial = !declaration_classes.is_vacuous() && !route_classes.is_vacuous();
    holds.push((
        "the dilation separates this material under both declared identities",
        non_trivial,
        format!(
            "by declaration {} classes, by route {} classes",
            declaration_classes.by_service_rounds.len(),
            route_classes.by_service_rounds.len()
        ),
    ));

    // ---------------------------------------------------------------------------------------------
    // CONTROL 2 — does it separate atoms the recruitment closure could not?
    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROL — DOES IT SEPARATE ATOMS WHOSE RECRUITMENT CLOSURES ARE BOTH EMPTY?");
    println!("---------------------------------------------------------------------------");
    let deposit = ElaborationDeposit::read(&derivations);
    let declared: BTreeSet<&str> = deposit.declared_names();
    let atoms: BTreeSet<&str> = route_reading
        .terrain
        .iter()
        .map(String::as_str)
        .filter(|identifier| !declared.contains(identifier))
        .collect();
    println!(
        "  {} of the {} departing identifiers are atoms: nothing in the deposit declares them, so",
        atoms.len(),
        route_terrain.len()
    );
    println!("  the downward recruitment closure of each is EMPTY and an elaboration reading cannot");
    println!("  tell any two of them apart");
    println!("{}", population("    ", atoms.iter().map(|atom| (*atom).to_owned())));

    let mut atom_classes: BTreeMap<BigUint, BTreeSet<&str>> = BTreeMap::new();
    for atom in &atoms {
        if let Some(rounds) = rounds_of(&route_reading, atom) {
            atom_classes.entry(rounds).or_default().insert(atom);
        }
    }
    println!("\n  the classes the dilation puts those same atoms into");
    for (rounds, members) in &atom_classes {
        println!(
            "    service rounds {rounds:<4} {}",
            members
                .iter()
                .map(|member| (*member).to_owned())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    let atoms_separate = atom_classes.len() > 1;
    holds.push((
        "two atoms with empty recruitment closures land in different service-round classes",
        atoms_separate,
        format!("{} classes over {} atoms", atom_classes.len(), atoms.len()),
    ));

    // The named pair, with the difference named.
    for (left, right) in [("apply", "exact_chart_carry"), ("contrapose", "simpa")] {
        let (Some(left_site), Some(right_site)) =
            (route_reading.site(left), route_reading.site(right))
        else {
            continue;
        };
        println!(
            "\n  {left} and {right} are both atoms with empty closures, and they separate:"
        );
        for site in [left_site, right_site] {
            let departure = &site.departures[0];
            println!(
                "    {:<20} {} routes stood on it, reaching {} distinguishable result-set(s), so its",
                site.identifier, site.onward_passages, site.capacity
            );
            println!(
                "    {:<20} co-present demand {} met a capacity of {} and cost {} service rounds",
                "",
                departure.co_present_branch_population,
                departure.site_capacity,
                departure.service_rounds
            );
        }
    }

    // ---------------------------------------------------------------------------------------------
    // CONTROL 3 — nothing is ranked
    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROL — NOTHING IS RANKED, AND WHERE A READER WOULD HAVE TO ADD ONE");
    println!("---------------------------------------------------------------------");
    println!("  The return is a population and a partition. The class index is an exact BigUint and");
    println!("  the classes are presented in the integer's own order, which is the order of the");
    println!("  naturals and not an order of importance. A RANKING APPEARS AT EXACTLY ONE STEP AND");
    println!("  THAT STEP IS NOT IN THIS CODE: a reader who reads the class index as a magnitude of");
    println!("  importance and takes the largest class has built an inverse-document weight.");
    println!();
    println!("  The reading resists that step measurably rather than by exhortation. If the service");
    println!("  round were the recruitment count in disguise it would be monotone in the fan-out.");
    println!("  It is not:");

    let mut inversions = Vec::new();
    for left in &route_terrain {
        for right in &route_terrain {
            let (Some(a), Some(b)) = (route_reading.site(left), route_reading.site(right)) else {
                continue;
            };
            let (Some(ra), Some(rb)) = (rounds_of(&route_reading, left), rounds_of(&route_reading, right))
            else {
                continue;
            };
            if a.onward_passages > b.onward_passages && ra < rb {
                inversions.push(format!(
                    "{} ({} routes -> {} rounds) is recruited MORE than {} ({} routes -> {} rounds) and dilates LESS",
                    a.identifier, a.onward_passages, ra, b.identifier, b.onward_passages, rb
                ));
            }
        }
    }
    for inversion in &inversions {
        println!("    {inversion}");
    }
    if inversions.is_empty() {
        println!("    (none — on this material the dilation happens to be monotone in the fan-out)");
    }
    holds.push((
        "the service-round class is not monotone in how often an identifier was recruited",
        !inversions.is_empty(),
        format!("{} inversions against the recruitment count", inversions.len()),
    ));

    let mut same_class_different_count = Vec::new();
    for (rounds, members) in &route_classes.by_service_rounds {
        let counts: BTreeSet<usize> = members
            .iter()
            .filter_map(|member| route_reading.site(member))
            .map(|site| site.onward_passages)
            .collect();
        if counts.len() > 1 {
            same_class_different_count.push(format!(
                "service rounds {rounds}: {} share a class with recruitment counts {:?}",
                members.iter().cloned().collect::<Vec<_>>().join(", "),
                counts
            ));
        }
    }
    println!("  and identifiers with different recruitment counts share one class:");
    for line in &same_class_different_count {
        println!("    {line}");
    }

    // ---------------------------------------------------------------------------------------------
    // CONTROL 4 — returned occurrence changes a capacity and therefore a delay
    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROL — RETURNED OCCURRENCE CHANGES A CAPACITY AND THE DOWNSTREAM DELAY MOVES");
    println!("--------------------------------------------------------------------------------");
    println!("  A capacity that never changes is a constant, not a capacitance. The returned");
    println!("  occurrence used here is the circuit's own: the co-present branch population the");
    println!("  radiation DELIVERED to the site. `set_site_capacity` re-founds the capacity on that");
    println!("  return without re-founding the site and without rewriting prior passage testimony.");

    let mut conditioned = found(
        &deposited,
        &derivations,
        &[],
        CapacityLaw::DistinguishableResults,
        CharacteristicDelayLaw::Uniform,
    );
    // The interior site: the only 0-cell of this deposit that is both recruited and recruits.
    let interior: Option<String> = declaration_reading
        .sites
        .iter()
        .find(|site| {
            !site.departures.is_empty()
                && !declaration_reading.terrain.contains(&site.identifier)
        })
        .map(|site| site.identifier.clone());

    let mut capacity_moved = false;
    if let Some(interior) = interior {
        let downstream: Vec<(String, u64)> = declaration_reading
            .site(&interior)
            .expect("the interior site has a row")
            .departures
            .iter()
            .flat_map(|departure| departure.passages.iter())
            .map(|passage| (passage.to.clone(), passage.arrival_chronology))
            .collect();
        println!(
            "\n  the interior site is `{interior}` — recruited by the terrain and recruiting onward"
        );
        let before = declaration_reading.site(&interior).expect("a row");
        println!(
            "    before   capacity {}   branch population {}   co-present {}   service rounds {}",
            before.capacity,
            before.departures[0].branch_population,
            before.departures[0].co_present_branch_population,
            before.departures[0].service_rounds
        );
        for (head, arrival) in &downstream {
            println!("      downstream arrival at {head}: chronology {arrival}");
        }

        let moved = conditioned
            .refound_capacity_on_return(&declaration_reading, &interior)
            .expect("the interior site departed");
        let after_reading = read(&conditioned);
        let after = after_reading.site(&interior).expect("a row");
        println!(
            "    returned occurrence: capacity {} -> {}",
            moved.as_ref().map_or("-".to_owned(), |(was, _)| was.to_string()),
            moved.as_ref().map_or("-".to_owned(), |(_, now)| now.to_string())
        );
        println!(
            "    after    capacity {}   branch population {}   co-present {}   service rounds {}",
            after.capacity,
            after.departures[0].branch_population,
            after.departures[0].co_present_branch_population,
            after.departures[0].service_rounds
        );
        let mut downstream_moved = false;
        for (head, was) in &downstream {
            let now = after_reading
                .site(&interior)
                .and_then(|site| {
                    site.departures
                        .iter()
                        .flat_map(|departure| departure.passages.iter())
                        .find(|passage| &passage.to == head)
                })
                .map(|passage| passage.arrival_chronology);
            println!(
                "      downstream arrival at {head}: chronology {was} -> {}",
                now.map_or("-".to_owned(), |at| at.to_string())
            );
            if now.is_some_and(|at| at != *was) {
                downstream_moved = true;
            }
        }
        capacity_moved = moved.is_some()
            && after.departures[0].service_rounds != before.departures[0].service_rounds
            && downstream_moved;
    }
    holds.push((
        "a returned occurrence moved a site's capacity and a downstream delay moved with it",
        capacity_moved,
        "set_site_capacity on the interior site".to_owned(),
    ));

    // ---------------------------------------------------------------------------------------------
    // Source continuity — the fifth factor, and the frame it opens
    // ---------------------------------------------------------------------------------------------

    println!("\nSOURCE CONTINUITY — THE ONE FACTOR THE CIRCUIT ITSELF DOES NOT SUPPLY");
    println!("---------------------------------------------------------------------");
    println!("  `derivation_atlas::Derivation` carries a name, a statement and a recruitment");
    println!("  multiset, and NO source coordinate at all. The circuit therefore supplies nothing");
    println!("  that could serve as source continuity, and a mapping restricted to it must report");
    println!("  the term absent. The deposit on disk does carry one: an artifact is a continuous");
    println!("  source and its lines are ordered. What is used, declared exactly: the characteristic");
    println!("  delay of a passage is ONE PLUS THE MINIMAL LINE SEPARATION, over the artifacts that");
    println!("  founded the head, between the theorem line and the nearest line naming the tail.");

    let situated_mapping = found(
        &deposited,
        &derivations,
        &carried_sources,
        CapacityLaw::DistinguishableResults,
        CharacteristicDelayLaw::SourceContinuity,
    );
    let situated = read(&situated_mapping);
    println!("\n  the same by-declaration circuit, with the base delay un-pinned");
    print_delay_population(&situated);
    let situated_classes = situated.dilation_classes();
    println!("\n  the classes the dilation induces under source continuity");
    print_classes(&situated_classes);

    let mut delay_moved = Vec::new();
    for site in &declaration_reading.sites {
        let uniform = render_delays(&declaration_reading, &site.identifier);
        let carried = render_delays(&situated, &site.identifier);
        if uniform != carried {
            delay_moved.push(format!("{}: {uniform} -> {carried}", site.identifier));
        }
    }
    println!("\n  the passages source continuity moved");
    println!("{}", population("    ", delay_moved.iter().cloned()));

    println!(
        "\n  and the class count went DOWN, {} -> {}, which is the honest return here.",
        declaration_classes.by_service_rounds.len(),
        situated_classes.by_service_rounds.len()
    );
    println!("  Under a uniform delay the interior site's terrain all arrives at one chronology and");
    println!("  superposes; separating the arrivals by their source separation DE-CONGESTS it. That");
    println!("  is the coupling running the other way and it is evidence the term is doing work, not");
    println!("  evidence that source continuity improves a reading. A capacitance reading is not a");
    println!("  quantity to be maximised.");
    println!("\n  and the branches that no longer superpose are retained, not lost:");
    for (site, chronologies) in &situated.deferred {
        println!(
            "    {site} at {}",
            chronologies
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The predicted-flat alternative capacity, run rather than asserted
    // ---------------------------------------------------------------------------------------------

    println!("\nTHE ALTERNATIVE CAPACITY THAT WAS PREDICTED FLAT, RUN RATHER THAN ASSERTED");
    println!("--------------------------------------------------------------------------");
    println!("  Capacity = the exact number of times the deposit named the identifier. Every onward");
    println!("  head named it at least once, so the occurrence total is never below the fan-out and");
    println!("  a unit branch population can never require a second round. Predicted: one class at");
    println!("  the source layer, so any non-unit class can only come from an interior site where");
    println!("  the branch population accumulated.");
    let occurrence = read(&found(
        &deposited,
        &derivations,
        &[],
        CapacityLaw::OccurrenceMultiplicity,
        CharacteristicDelayLaw::Uniform,
    ));
    let occurrence_classes = occurrence.dilation_classes();
    println!(
        "  returned classes {:?}",
        occurrence_classes
            .by_service_rounds
            .keys()
            .map(BigUint::to_string)
            .collect::<Vec<_>>()
    );
    for (rounds, members) in &occurrence_classes.by_service_rounds {
        println!(
            "    service rounds {rounds:<6} {}",
            members.iter().cloned().collect::<Vec<_>>().join(", ")
        );
    }
    let terrain_flat = occurrence_classes
        .by_service_rounds
        .iter()
        .all(|(rounds, members)| {
            rounds == &BigUint::one()
                || members
                    .iter()
                    .all(|member| !occurrence.terrain.contains(member))
        });
    println!(
        "  every TERRAIN site returned exactly one service round: {terrain_flat}  (as predicted)"
    );
    holds.push((
        "the occurrence-multiplicity capacity is flat on the terrain, as predicted by theorem",
        terrain_flat,
        format!(
            "{} classes, terrain flat {terrain_flat}",
            occurrence_classes.by_service_rounds.len()
        ),
    ));

    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROLS");
    println!("--------");
    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        println!(
            "  [{}] {claim}\n        {evidence}",
            if *verdict { "holds" } else { "FAILED" }
        );
        if !verdict {
            failed += 1;
        }
    }
    if failed > 0 {
        println!("\n{failed} declared control(s) failed");
        std::process::exit(1);
    }
    println!("\nevery declared control holds");
}
