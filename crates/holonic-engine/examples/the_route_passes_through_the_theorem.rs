//! **A route between two mathematical entities, on Lean the machine did not write.**
//!
//! Organs: `lean_development::{read_development, join, declared_recruitment_qualified}` reads the
//! declaration-to-declaration relation; `derivation_atlas::found_circuit` founds the circuit;
//! `derivation_capacitance::{orient_passages, CapacitanceMapping::found, route}` mounts the
//! transport law and answers. **Nothing new is built here — this is an adapter and a driver.**
//!
//! # Why this driver exists
//!
//! `CapacitanceMapping::route` names both endpoints at call time, but on all four committed deposit
//! directories every route is length 2: those artifacts share one theorem name and do not build on
//! each other, so the circuit is a star with no intermediate to name. The three-step route existed
//! only on a chain the test authored, which cannot be cited.
//!
//! `lean_development::declared_recruitment_qualified` returns declaration-to-declaration edges with
//! full namespace resolution, self-edges excluded, and ambiguity retained as `open_recruitment`
//! rather than chosen. Its shape already matches `Derivation { name, statement, recruited }`, so
//! the adapter is a rename and no organ is added.
//!
//! # What is returned
//!
//! Every ordered pair of declarations asked, both endpoints named by the caller. The population is
//! the exact count from the factorized arrival body; the routes are read back into declaration
//! names; a pair the terrain does not join returns `Unreached` **by name**.
//!
//! # What may not be claimed
//!
//! The recruitment relation is **orthographic**: it is read from the source text, so a dependency
//! discharged by `simp`, `ring`, `omega` or `aesop` is invisible by construction, and no kernel is
//! consulted. This returns routes through the relation the text declares, which is a real object
//! and is not the proof-term dependency graph. Nothing here is a proof search, nothing is ranked,
//! and no route is committed to.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_route_passes_through_the_theorem
//! cargo run --release -p holonic-engine --example the_route_passes_through_the_theorem -- <dir>
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use holonic_engine::derivation_atlas::{CircuitAperture, Derivation, found_circuit};
use holonic_engine::derivation_capacitance::{
    CapacitanceMapping, CapacityLaw, CharacteristicDelayLaw, RouteReading,
};
use holonic_engine::lean_development::{DeclarationGrain, join, read_development};

const DEFAULT_ROOT: &str = "formal";

/// Collect every `.lean` file under `root`, skipping `.lake` — build output and vendored packages
/// are not this development's own declarations.
fn lean_files(root: &PathBuf, into: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == ".lake") {
                continue;
            }
            lean_files(&path, into);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            into.push(path);
        }
    }
}

fn main() {
    let root = PathBuf::from(
        std::env::args()
            .nth(1)
            .unwrap_or_else(|| DEFAULT_ROOT.to_owned()),
    );

    println!("{}", "=".repeat(96));
    println!("THE ROUTE PASSES THROUGH THE THEOREM");
    println!("{}", "=".repeat(96));

    let mut paths = Vec::new();
    lean_files(&root, &mut paths);
    paths.sort();
    if paths.is_empty() {
        eprintln!("REFUSED: no .lean files under {}", root.display());
        std::process::exit(1);
    }

    let readings: Vec<_> = paths
        .iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(path).ok()?;
            Some(read_development(
                &text,
                DeclarationGrain::EveryTopLevelDeclaration,
            ))
        })
        .collect();
    // Joined into ONE reading, so a declaration recruited across files resolves. Summing per-file
    // readings would drop exactly the cross-file edges a chain is made of.
    let development = join(readings);
    let recruitment = development.declared_recruitment_qualified();

    println!("\n  material: {} ({} files)", root.display(), paths.len());
    println!(
        "  {} declarations, {} declared-to-declared edges",
        recruitment.len(),
        recruitment.values().map(BTreeSet::len).sum::<usize>()
    );

    // THE ADAPTER. A declaration is a derivation: it is named, it recruits, and what it reaches is
    // itself. No conversion organ — the shapes already match.
    let derivations: Vec<Derivation> = recruitment
        .iter()
        .map(|(name, recruits)| Derivation {
            name: name.clone(),
            statement: name.clone(),
            recruited: recruits
                .iter()
                .map(|recruited| (recruited.clone(), 1u32))
                .collect(),
        })
        .collect();

    let circuit = match found_circuit(&derivations, CircuitAperture::DEPOSITED_READER) {
        Ok(circuit) => circuit,
        Err(error) => {
            eprintln!("REFUSED: the aperture is inadmissible: {error}");
            std::process::exit(1);
        }
    };
    let mapping = match CapacitanceMapping::found(
        &circuit,
        &derivations,
        &[],
        CapacityLaw::DistinguishableResults,
        CharacteristicDelayLaw::Uniform,
    ) {
        Ok(mapping) => mapping,
        Err(error) => {
            eprintln!("REFUSED: the circuit founds no passage ecology: {error}");
            std::process::exit(1);
        }
    };
    let sites: Vec<String> = mapping
        .identifiers()
        .into_iter()
        .map(str::to_owned)
        .collect();
    println!(
        "  circuit: {} sites, {} reachable from terrain, terrain {} sites",
        mapping.site_count(),
        mapping.reachable_sites(),
        mapping.terrain().len()
    );

    println!("\n{}", "-".repeat(96));
    println!("EVERY ORDERED PAIR, ASKED. Both endpoints named at call time.");
    println!("{}", "-".repeat(96));

    let mut joined = 0usize;
    let mut unreached = 0usize;
    let mut by_length: BTreeMap<usize, usize> = BTreeMap::new();
    let mut longest: Option<Vec<String>> = None;
    let mut plural: Vec<(String, String, usize)> = Vec::new();
    let mut crossed: BTreeSet<String> = BTreeSet::new();

    for from in &sites {
        for to in &sites {
            if from == to {
                continue;
            }
            match mapping.route(from, to) {
                Ok(RouteReading::Reached {
                    population, routes, ..
                }) => {
                    joined += 1;
                    if population != num_bigint::BigUint::from(routes.len()) {
                        eprintln!("REFUSED: population disagrees with its own witnesses");
                        std::process::exit(1);
                    }
                    if routes.len() > 1 {
                        plural.push((from.clone(), to.clone(), routes.len()));
                    }
                    for route in &routes {
                        *by_length.entry(route.len()).or_default() += 1;
                        for step in route.iter().skip(1).take(route.len().saturating_sub(2)) {
                            crossed.insert(step.clone());
                        }
                        if longest.as_ref().is_none_or(|held| route.len() > held.len()) {
                            longest = Some(route.clone());
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

    println!(
        "  {} ordered pairs: {joined} joined, {unreached} in different components",
        joined + unreached
    );
    println!("  route lengths returned, and their populations:");
    for (length, count) in &by_length {
        println!("    {length:>3} steps  {count:>8}");
    }
    println!(
        "  {} pairs carry more than one route, all retained and none chosen",
        plural.len()
    );
    println!(
        "  {} distinct declarations were crossed on the way, NAMED by the return",
        crossed.len()
    );

    let past_two = by_length
        .iter()
        .filter(|(length, _)| **length > 2)
        .map(|(_, count)| *count)
        .sum::<usize>();

    match &longest {
        Some(route) if route.len() > 2 => {
            println!("\n  the longest route, {} steps:", route.len());
            for (at, step) in route.iter().enumerate() {
                println!("{}{step}", if at == 0 { "    " } else { "      ->  " });
            }
            println!(
                "\n  {past_two} returned routes exceed two steps on material this driver did not"
            );
            println!(
                "  author. Both endpoints were named at call time and every constituent between"
            );
            println!("  them was named by the return rather than supplied by the caller.");
        }
        _ => {
            println!("\n  NO ROUTE EXCEEDS TWO STEPS on this material. The deed is not exhibited");
            println!("  here, and that is reported rather than omitted.");
        }
    }

    for (from, to, count) in plural.iter().take(2) {
        println!("\n  {from} -> {to}: {count} routes, all retained");
        if let Ok(RouteReading::Reached { routes, .. }) = mapping.route(from, to) {
            for route in routes.iter().take(3) {
                println!("      {}", route.join("  ->  "));
            }
        }
    }

    println!("\n{}", "-".repeat(96));
    println!("THE CONTROL — a pair the terrain does not join");
    println!("{}", "-".repeat(96));
    if unreached == 0 {
        println!("  every pair is joined, so the Unreached branch did NOT run on this material.");
    } else {
        println!(
            "  {unreached} ordered pairs returned Unreached BY NAME rather than as an empty vector."
        );
    }
    match mapping.route(&sites[0], "no-such-declaration-in-this-development") {
        Err(error) => println!("  an unknown endpoint is refused by name: {error}"),
        Ok(reading) => {
            eprintln!("REFUSED: an unknown endpoint returned a reading: {reading:?}");
            std::process::exit(1);
        }
    }

    println!("\n{}", "-".repeat(96));
    println!("WHAT THIS MAY NOT BE REPORTED AS");
    println!("{}", "-".repeat(96));
    println!("  The recruitment relation is ORTHOGRAPHIC — read from the source text — so a");
    println!("  dependency discharged by simp, ring, omega or aesop is invisible by construction");
    println!("  and no kernel is consulted. These are routes through the relation the text");
    println!("  declares. That is a real object and it is not the proof-term dependency graph.");

    println!("\n{}", "=".repeat(96));
    println!(
        "{}",
        if past_two > 0 {
            "RETURNED -- routes through theorems, on material the driver did not author"
        } else {
            "RETURNED -- no route past two steps; the deed remains owed a corpus"
        }
    );
    println!("{}", "=".repeat(96));
}
