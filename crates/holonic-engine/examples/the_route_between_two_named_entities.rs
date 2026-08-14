//! **The route between two mathematical entities the caller names, on the machine's own deposits.**
//!
//! Organs, all of them already built and none of them new here: `derivation_atlas::found_circuit`
//! (the graph), `derivation_capacitance::orient_passages` (the direction, read off the founded
//! boundary sign), `derivation_capacitance::CapacitanceMapping::found` (the transport law),
//! `receiver_current::ExactReceiverCurrentLaw::radiate` (the current, with arbitrary source **and**
//! target), and its `exact_path_population` / `witness_paths_to` readers.
//!
//! # Why this driver exists
//!
//! Measured 2026-08-14, before it: `radiate(sources, targets)` had **six call sites in the whole
//! tree and every one was inside `#[cfg(test)]`**. Every production caller anywhere used the
//! *targetless* `radiate_to_horizon`, and the only library consumer of the arrival atlas took
//! `exact_path_population` — the **count** — multiplied it into a factorized population, and never
//! asked for a route.
//!
//! > The machine computed exactly how many routes reached a target and had never once asked for one.
//!
//! That is one shape at four altitudes in this body: a relation is computed, its terms are kept, and
//! the relation is dropped. `found_potential_in` walked a spanning tree and returned two sets. The
//! registry carries 618 dependency edges and nothing parses it. And here, the route population was
//! reduced to its cardinality at the one call site that had it.
//!
//! # What a pointer is
//!
//! `next` is not an address, it is a relative orientation — *from here, that way* — and the same
//! species as `opposite` and `adjacent` at a chosen vertex. Which side is "opposite" is decided by
//! which angle you stand at; the triangle does not move. The six ordered pairs of three sides are
//! exactly the six trigonometric functions, and an identity between them — `sin^2 + cos^2 = 1` — is
//! a rebase with **zero remainder** between two readings of one object, not a fact about numbers.
//!
//! So a head and a tail are identities relative to the contemporary item, and a route is a
//! composition of transports rather than a list of vertices. Where a route climbs and comes back
//! down, the ascending leg carries the opposite hand — the half turn — which is why
//! `running_integral::PotentialSearch::route_between` reverses it and why `causal_body`'s tree walk
//! does the same.
//!
//! # What is returned, and what may not be claimed
//!
//! `RouteReading::Reached` carries the **exact** number of minimal-arrival routes, taken from the
//! factorized arrival body without enumerating them, beside the routes themselves read back into
//! identifiers. `RouteReading::Unreached` names a pair the terrain does not join — it is a fact
//! about the terrain, and an empty vector would report it as an absence of routes instead.
//!
//! This returns routes through a **founded** circuit. It is not a proof search, it does not order
//! the routes by preference, and it commits to none of them.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_route_between_two_named_entities
//! cargo run --release -p holonic-engine --example the_route_between_two_named_entities -- <dir>
//! ```

use std::collections::BTreeSet;
use std::path::PathBuf;

use holonic_engine::derivation_atlas::{
    CircuitAperture, Derivation, found_circuit, read_derivation,
};
use holonic_engine::derivation_capacitance::{
    CapacitanceMapping, CapacityLaw, CharacteristicDelayLaw, RouteReading,
};

const DEFAULT_ROOT: &str = "standing/output/lean-proof-production";

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| DEFAULT_ROOT.to_owned());

    println!("{}", "=".repeat(96));
    println!("THE ROUTE BETWEEN TWO NAMED ENTITIES");
    println!("{}", "=".repeat(96));

    let mut paths: Vec<PathBuf> = match std::fs::read_dir(&root) {
        Ok(entries) => entries
            .filter_map(|entry| Some(entry.ok()?.path()))
            .collect(),
        Err(error) => {
            eprintln!("REFUSED: cannot read {root}: {error}");
            std::process::exit(1);
        }
    };
    paths.sort();
    let derivations: Vec<Derivation> = paths
        .iter()
        .filter_map(|path| read_derivation(&std::fs::read_to_string(path).ok()?))
        .collect();

    if derivations.len() < 2 {
        eprintln!("REFUSED: {root} carries {} derivations", derivations.len());
        std::process::exit(1);
    }
    println!("\n  material: {root}");
    println!(
        "  {} artifacts read, {} derivations recovered",
        paths.len(),
        derivations.len()
    );

    // **The aperture is a declared gauge, and the orbit is measured rather than assumed.** All four
    // declared apertures are asked; if the route population does not move across them, the aperture
    // decided nothing on this material and the sweep says so instead of quoting one reading.
    let mut orbit: Vec<(String, usize, usize, usize, usize, usize)> = Vec::new();
    let mut best: Option<(String, CapacitanceMapping, Vec<String>)> = None;

    for aperture in CircuitAperture::DECLARED {
        let name = format!("{aperture:?}");
        let Ok(circuit) = found_circuit(&derivations, aperture) else {
            println!("\n  aperture {name}: inadmissible on this material");
            continue;
        };
        let Ok(mapping) = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        ) else {
            println!("\n  aperture {name}: founds no passage ecology");
            continue;
        };

        let sites = sites_of(&mapping);
        let mut reached = 0usize;
        let mut unreached = 0usize;
        let mut longest: Vec<String> = Vec::new();
        let mut plural = 0usize;
        for from in &sites {
            for to in &sites {
                if from == to {
                    continue;
                }
                match mapping.route(from, to) {
                    Ok(RouteReading::Reached {
                        population, routes, ..
                    }) => {
                        reached += 1;
                        assert_eq!(
                            population,
                            num_bigint::BigUint::from(routes.len()),
                            "the factorized population disagrees with its own witnesses"
                        );
                        if routes.len() > 1 {
                            plural += 1;
                        }
                        for route in routes {
                            if route.len() > longest.len() {
                                longest = route;
                            }
                        }
                    }
                    Ok(RouteReading::Unreached { .. }) => unreached += 1,
                    Err(error) => {
                        eprintln!("REFUSED {from} -> {to}: {error}");
                        std::process::exit(1);
                    }
                }
            }
        }
        orbit.push((
            name.clone(),
            mapping.site_count(),
            reached,
            unreached,
            plural,
            longest.len(),
        ));
        if best
            .as_ref()
            .is_none_or(|(_, _, held)| longest.len() > held.len())
        {
            best = Some((name, mapping, longest));
        }
    }

    println!("\n{}", "-".repeat(96));
    println!(
        "THE APERTURE ORBIT — every declared aperture asked, both endpoints named at call time"
    );
    println!("{}", "-".repeat(96));
    println!(
        "  {:<52} {:>6} {:>8} {:>9} {:>7} {:>8}",
        "aperture", "sites", "joined", "unjoined", "plural", "longest"
    );
    for (name, sites, reached, unreached, plural, longest) in &orbit {
        println!("  {name:<52} {sites:>6} {reached:>8} {unreached:>9} {plural:>7} {longest:>8}");
    }
    let distinct: BTreeSet<(usize, usize, usize, usize)> = orbit
        .iter()
        .map(|(_, sites, reached, _, plural, longest)| (*sites, *reached, *plural, *longest))
        .collect();
    println!(
        "\n  {} distinct readings over {} declared apertures — the gauge {}",
        distinct.len(),
        orbit.len(),
        if distinct.len() > 1 {
            "ACTS on this material"
        } else {
            "acts TRIVIALLY here, so agreement across it is not evidence"
        }
    );

    let Some((name, mapping, longest)) = best else {
        eprintln!("REFUSED: no aperture returned a mapping");
        std::process::exit(1);
    };

    println!("\n{}", "-".repeat(96));
    println!("THE LONGEST ROUTE RETURNED, under {name}");
    println!("{}", "-".repeat(96));
    if longest.is_empty() {
        println!("  no pair on this material is joined under any aperture");
    } else {
        println!("  {} steps:", longest.len());
        for (at, step) in longest.iter().enumerate() {
            if at == 0 {
                println!("    {step}");
            } else {
                println!("      ->  {step}");
            }
        }
        if longest.len() > 2 {
            println!(
                "\n  Longer than two steps, and every constituent between the endpoints was NAMED"
            );
            println!(
                "  by the return rather than supplied by the caller. That is the deed the existing"
            );
            println!("  two-step route API could not do.");
        } else {
            println!(
                "\n  NOTE: two steps. This material joins nothing through an intermediate, so this"
            );
            println!(
                "  run does NOT exhibit what the existing two-step API could not already return."
            );
            println!("  Reported rather than omitted.");
        }
    }

    println!("\n{}", "-".repeat(96));
    println!("THE CONTROLS");
    println!("{}", "-".repeat(96));
    let sites = sites_of(&mapping);
    let unjoined = orbit
        .iter()
        .find(|(held, ..)| held == &name)
        .map(|(_, _, _, unreached, _, _)| *unreached)
        .unwrap_or(0);
    if unjoined == 0 {
        println!(
            "  every pair is joined under this aperture, so the Unreached branch did NOT run."
        );
        println!("  A refusal that never fires has not shown that it can.");
    } else {
        println!(
            "  {unjoined} ordered pairs returned Unreached BY NAME rather than as an empty vector"
        );
        println!("  — a fact about the terrain, not an absence of routes.");
    }
    match mapping.route(&sites[0], "no-such-entity-in-this-terrain") {
        Err(error) => println!("  an unknown endpoint is refused by name: {error}"),
        Ok(reading) => {
            eprintln!("REFUSED: an unknown endpoint returned a reading: {reading:?}");
            std::process::exit(1);
        }
    }

    println!("\n{}", "=".repeat(96));
    println!("RETURNED — the route population, not its cardinality");
    println!("{}", "=".repeat(96));
}

/// Every site the mapping carries, **read off the mapping**.
///
/// This reconstructed candidate names from the `Derivation` fields until 2026-08-14 and kept the
/// ones that resolved. That silently dropped every 0-cell whose key the aperture rewrote — all 31
/// route-keyed cells under `ByRoute`, whose keys are `name#ordinal` — and then reported the
/// surviving 14 symbols, which link to nothing, as `0 joined`. The driver had authored its own site
/// set and read the result as a property of the circuit.
fn sites_of(mapping: &CapacitanceMapping) -> Vec<String> {
    mapping
        .identifiers()
        .into_iter()
        .map(str::to_owned)
        .collect()
}
