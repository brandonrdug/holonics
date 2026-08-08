//! Read the machine's own deposited derivations back, and compute their invariants.
//!
//! `standing/output/` holds proof artifacts the machine produced, each bound to a content hash in
//! `standing/MANIFEST.txt`. **Nothing had ever read them back.** Every artifact this project emits
//! goes into a directory that no organ opens, which is the gap the roadmap has carried as "the
//! atlas reader" since the transition.
//!
//! This is that reader, pointed at real production rather than at an emitted table nothing wrote.
//!
//! ## The derivation is a circuit
//!
//! A derivation names things, depends on things, and reaches a statement. Read as a complex:
//!
//! ```text
//!   0-cells   the declarations named -- theorems produced, symbols recruited, statements reached
//!   1-cells   a recruitment: this derivation named that symbol
//!             a reach:       this derivation proved that statement
//! ```
//!
//! Then the invariants say what the production is:
//!
//! ```text
//!   b_0       independent content classes -- how many distinct things were derived
//!   b_1       independent recruitment cycles; and, across the two statement apertures, the
//!             independent routes to one result
//!   torsion   a recruitment that cannot be un-derived
//! ```
//!
//! No external checker is consulted. The proof sources are read as structure, not submitted to
//! anything, which is the whole point of Lean being an export codec rather than a judge.
//!
//! ## Four corrections this reader carries, all found by grading it rather than reading its output
//!
//! **This file used to declare a 2-cell — *"two derivations reaching the SAME statement by
//! different recruitment"* — that `main` never founded.** It founds none now either, and
//! `holonic_engine::derivation_atlas` says why: a square 2-cell over two derivations sharing two
//! symbols cancels exactly the grade-1 cycle the line above reads as *"independent distinct routes
//! to one result"*. The two sentences are not compatible and the reader does not pick one silently.
//!
//! **`b_1` and `torsion` are read under four declared apertures, not one.** Under the identity this
//! reader has always used, every artifact proving one theorem collapses onto one 0-cell; and under
//! the incidence coefficient it has always used, the boundary is totally unimodular, so `torsion`
//! is empty for *every* deposit. Both zeros were properties of the reading, not measurements of the
//! production, and they are printed below under DECLARED THEOREMS rather than beside things that
//! could have come out otherwise.
//!
//! **`b_1` under one aperture does not measure the routes to one result.** It counts shared
//! recruitment and is blind to statement identity. The quantity `blueprint/THE_ASSEMBLY.md:129`
//! names is the *difference* between the statement-founded and statement-withheld readings, and
//! this reader checks it against the route lineage, which computes it by a disjoint path.
//!
//! **The control "the invariants are capable of being nonzero here" was deleted.** `b_0` is the
//! number of connected components and is at least one for any non-empty vertex set, so that claim
//! was forced for every possible deposit and reported `[holds]` on a run whose grade-1 reading was
//! zero. What replaced it can fail: two independent implementations of the same two numbers.
//!
//! ```text
//! cargo run --release --example derivation_atlas_reader -- standing/output
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{
    found_circuit, invariant_movement, read_derivation, route_cycle_agreement, route_movement,
    CircuitAperture, Derivation, DerivationCircuit, DerivationIdentity, RecruitmentCoefficient,
};
use holonic_engine::rebase_invariants::{invariants_agree, PivotRule, RebaseInvariants};

/// Every `.lean` artifact under `root`, in a stable filename order. Recursive, so a standing that
/// holds several foundings side by side reads as one deposit.
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

fn read_population(paths: &[PathBuf]) -> Vec<Derivation> {
    paths
        .iter()
        .filter_map(|path| read_derivation(&std::fs::read_to_string(path).ok()?))
        .collect()
}

fn render_torsion(invariants: &RebaseInvariants, grade: u32) -> String {
    let torsion = invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map(|carried| carried.torsion.clone())
        .unwrap_or_default();
    if torsion.is_empty() {
        "none".to_owned()
    } else {
        torsion
            .iter()
            .map(|factor| format!("Z/{factor}"))
            .collect::<Vec<_>>()
            .join(" + ")
    }
}

fn betti_at(invariants: &RebaseInvariants, grade: u32) -> usize {
    invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map_or(0, |carried| carried.betti)
}

/// A population, rendered whole. Long populations wrap rather than truncate: the design's "what
/// must not be built" names *a driver reporting counts instead of artifacts*, and an elision is a
/// count wearing the population's name.
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

/// The declaration vertices of a circuit: every 0-cell some artifact declared, as opposed to the
/// symbols they recruited and the statements they reached.
fn declaration_vertices(circuit: &DerivationCircuit) -> BTreeSet<&str> {
    circuit
        .routes()
        .values()
        .flat_map(|reached| reached.iter().map(String::as_str))
        .collect()
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "standing/output/lean-proof-production".to_owned());
    let paths = artifact_paths(Path::new(&root));

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=a derivation is a circuit and its invariants are what survive rebasing it");
    println!("standing={root}");

    if paths.is_empty() {
        println!("\nFAILED — no deposited derivations at {root}");
        println!("this reader refuses to run on anything it made up");
        std::process::exit(1);
    }

    let derivations = read_population(&paths);
    println!(
        "\nread {} artifacts, {} carrying a theorem declaration",
        paths.len(),
        derivations.len()
    );

    // --- the same deposit under every declared aperture ---------------------------------------

    println!("\nTHE SAME DEPOSIT UNDER EVERY DECLARED APERTURE");
    println!("----------------------------------------------");
    let mut readings = Vec::new();
    for aperture in CircuitAperture::DECLARED {
        let circuit =
            found_circuit(&derivations, aperture).expect("a declared aperture is admissible");
        let reading = circuit
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        let forest = circuit.spanning_forest_reading();
        println!(
            "  {:?} / {:?} / statements {:?}",
            circuit.aperture().identity,
            circuit.aperture().coefficient,
            circuit.aperture().statements
        );
        for grade in &reading.grades {
            println!(
                "    grade {}  cells {:>5}  boundary rank {:>5}  betti {:>5}  torsion {}",
                grade.grade,
                grade.cells,
                grade.boundary_rank,
                grade.betti,
                render_torsion(&reading, grade.grade)
            );
        }
        println!(
            "    spanning forest (second frame)  vertices {} edges {} components {} cycles {}",
            forest.vertices,
            forest.edges,
            forest.components,
            forest.betti_1()
        );
        readings.push((aperture, circuit, reading));
    }

    let deposited = &readings[0].1;
    let invariants = &readings[0].2;

    // --- the populations themselves -----------------------------------------------------------

    println!("\nTHE DECLARATIONS, THE SYMBOLS THEY RECRUITED, THE STATEMENTS THEY REACHED");
    println!("------------------------------------------------------------------------");
    let declarations = declaration_vertices(deposited);
    let symbols: BTreeSet<&str> = deposited
        .vertices()
        .keys()
        .map(String::as_str)
        .filter(|name| !declarations.contains(name))
        .collect();
    println!("  declarations");
    println!(
        "{}",
        population("    ", declarations.iter().map(|name| (*name).to_owned()))
    );
    println!("  symbols recruited");
    println!(
        "{}",
        population("    ", symbols.iter().map(|name| (*name).to_owned()))
    );

    println!("\n  statements, with the artifact lineage behind each");
    for (statement, lineage) in deposited.routes() {
        let mut carried: BTreeMap<&str, usize> = BTreeMap::new();
        for vertex in lineage {
            *carried.entry(vertex.as_str()).or_default() += 1;
        }
        println!("    {statement}");
        println!(
            "{}",
            population(
                "      ",
                carried
                    .into_iter()
                    .map(|(vertex, artifacts)| format!("{vertex} x{artifacts}"))
            )
        );
    }

    println!("\n  the target population a later production selects from, ranked by its lineage");
    let ranked = deposited.single_vertex_statements_by_lineage();
    if ranked.is_empty() {
        println!("    (empty — every statement here is already reached by more than one declaration)");
    }
    for (statement, lineage) in &ranked {
        println!("    {} artifacts   {statement}", lineage.len());
    }
    println!(
        "  and the statements it excludes, which more than one declaration already reached\n{}",
        population(
            "    ",
            deposited
                .plural_vertex_statements()
                .iter()
                .map(|statement| (*statement).to_owned())
        )
    );

    // --- is the reading a function of the production, or of the preamble? ----------------------
    //
    // This reading was orthographic until 2026-08-08 and every artifact of one problem then
    // returned the identical recruitment population, so no proof body the machine composed could
    // move the invariant. The population below is the evidence that it can now: the distinct
    // recruitment supports the deposit carries per declaration.

    println!("\nDISTINCT RECRUITMENT POPULATIONS PER DECLARATION");
    println!("------------------------------------------------");
    let mut classes: BTreeMap<&str, BTreeSet<Vec<(String, u32)>>> = BTreeMap::new();
    for derivation in &derivations {
        classes
            .entry(derivation.name.as_str())
            .or_default()
            .insert(
                derivation
                    .recruited
                    .iter()
                    .map(|(symbol, count)| (symbol.clone(), *count))
                    .collect(),
            );
    }
    let mut declarations_with_plural_recruitment = 0;
    for (declaration, distinct) in &classes {
        if distinct.len() > 1 {
            declarations_with_plural_recruitment += 1;
        }
        println!("  {declaration}");
        for recruited in distinct {
            println!(
                "{}",
                population(
                    "    ",
                    recruited
                        .iter()
                        .map(|(symbol, count)| format!("{symbol} x{count}"))
                )
            );
        }
    }

    // --- torsion, and where its material actually is ------------------------------------------
    //
    // "A recruitment that cannot be un-derived." Until 2026-08-08 the ONLY nonzero torsion in the
    // whole standing was the `end` keyword: every artifact names its namespace twice because Lean
    // writes `namespace Soma` ... `end Soma`, so every artifact carried a symbol of multiplicity
    // two and the export codec's closing convention was returning as a homological invariant. The
    // scope closer is no longer a recruitment, and what is printed below is what torsion has left:
    // repeated recruitments the proof body actually made.

    println!("\nTORSION, PER ARTIFACT, UNDER THE MULTIPLICITY COEFFICIENT");
    println!("---------------------------------------------------------");
    let mut torsion_classes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for derivation in &derivations {
        let alone = found_circuit(
            std::slice::from_ref(derivation),
            CircuitAperture::PER_ROUTE_MULTIPLICITY,
        )
        .expect("one artifact carries one route, so nothing is summed");
        let reading = alone
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        let repeated: Vec<String> = derivation
            .recruited
            .iter()
            .filter(|(_, count)| **count > 1)
            .map(|(symbol, count)| format!("{symbol} x{count}"))
            .collect();
        torsion_classes
            .entry(render_torsion(&reading, 0))
            .or_default()
            .insert(if repeated.is_empty() {
                "(no symbol named twice)".to_owned()
            } else {
                repeated.join(", ")
            });
    }
    for (torsion, material) in &torsion_classes {
        println!("  torsion at grade 0 = {torsion}, from the repeated recruitments");
        println!("{}", population("    ", material.iter().cloned()));
    }
    let torsion_somewhere = torsion_classes.keys().any(|torsion| torsion != "none");

    // --- the routes to one result, computed two ways ------------------------------------------

    println!("\nTHE INDEPENDENT ROUTES TO ONE RESULT, COMPUTED TWO WAYS");
    println!("-------------------------------------------------------");
    let mut agreements = Vec::new();
    for identity in [DerivationIdentity::ByDeclaration, DerivationIdentity::ByRoute] {
        let agreement = route_cycle_agreement(&derivations, identity, PivotRule::FirstNonzero)
            .expect("an incidence reading is admissible under either identity");
        println!(
            "  {identity:?}  homological {:>4}   lineage {:>4}   recruitment connected {}",
            agreement.homological, agreement.lineage, agreement.recruitment_connected
        );
        agreements.push(agreement);
    }

    // --- the pivot rule is a receiver coordinate ---------------------------------------------

    let pivot_holds = readings.iter().all(|(_, circuit, reading)| {
        PivotRule::ALL.iter().all(|rule| {
            circuit
                .invariants(*rule)
                .is_ok_and(|other| invariants_agree(reading, &other))
        })
    });

    // --- the reflective face: what a later production would move -----------------------------
    //
    // The reading is only fed back if it can say what changed. Withholding the last artifact and
    // re-reading is the smallest honest instance of that: it is the difference this reader would
    // have returned to the driver that deposited it.

    let mut holds: Vec<(&str, bool, String)> = Vec::new();
    if derivations.len() > 1 {
        let withheld = &derivations[..derivations.len() - 1];
        let before = found_circuit(withheld, CircuitAperture::DEPOSITED_READER)
            .expect("the deposited reader's aperture is admissible");
        let earlier = before
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        let movement = invariant_movement(&earlier, invariants);
        let routes = route_movement(&before, deposited);

        println!("\nTHE REFLECTIVE FACE — withhold the last artifact and re-read");
        println!("-----------------------------------------------------------");
        println!(
            "  grades moved {:?}   fields moved {:?}",
            movement.grades_moved(),
            movement.fields_moved()
        );
        for grade in movement.moved() {
            println!(
                "    grade {}  betti {:?} -> {:?}   torsion {:?} -> {:?}",
                grade.grade,
                grade.before.as_ref().map(|side| side.betti),
                grade.after.as_ref().map(|side| side.betti),
                grade.before.as_ref().map(|side| side.torsion.clone()),
                grade.after.as_ref().map(|side| side.torsion.clone()),
            );
        }
        println!("  statements founded");
        println!(
            "{}",
            population("    ", routes.founded_statements().iter().cloned())
        );
        println!("  became plural");
        println!(
            "{}",
            population("    ", routes.became_plural().iter().cloned())
        );
        println!("  lineage deepened — the frame the deduplicated support cannot see");
        for (statement, deepened) in routes.deepened_routes() {
            println!(
                "    {statement}\n{}",
                population(
                    "      ",
                    deepened
                        .iter()
                        .map(|(vertex, further)| format!("{vertex} +{further}"))
                )
            );
        }
        holds.push((
            "the movement population and invariants_agree return one verdict",
            movement.is_still() == invariants_agree(&earlier, invariants),
            format!(
                "moved {:?}, agree {}",
                movement.grades_moved(),
                invariants_agree(&earlier, invariants)
            ),
        ));
        holds.push((
            "withholding one artifact moves the route reading even when it moves no invariant",
            !routes.is_still(),
            format!(
                "invariants still {}, routes still {}",
                movement.is_still(),
                routes.is_still()
            ),
        ));
    }

    // --- what cannot have come out otherwise, kept apart from what could ----------------------

    println!("\nDECLARED THEOREMS OF THE READING — these could not have come out otherwise");
    println!("--------------------------------------------------------------------------");
    println!(
        "  the incidence coefficient is totally unimodular, so torsion is empty under it for EVERY\n\
         \x20 deposit. Measured here: {} and {}.",
        render_torsion(&readings[0].2, 0),
        render_torsion(&readings[2].2, 0)
    );
    println!(
        "  under ByRoute a route vertex is `name#ordinal` and can never be a recruitment target, so\n\
         \x20 that graph is bipartite and its oriented and unoriented readings coincide. Orientation\n\
         \x20 is testable only under ByDeclaration."
    );
    println!(
        "  Euler characteristic from Betti numbers equals it from cell counts by rank telescoping,\n\
         \x20 for any chain complex. It is not evidence about this one. chi = {}",
        invariants.cell_euler_characteristic()
    );

    // --- controls ---------------------------------------------------------------------------

    holds.insert(
        0,
        (
            "the reader read real deposited artifacts, not a fixture",
            !derivations.is_empty(),
            format!("{} derivations from {}", derivations.len(), root),
        ),
    );
    holds.insert(
        1,
        (
            "the complex carries recruitment 1-cells",
            !deposited.recruitments().is_empty(),
            format!(
                "{} recruitments, {} reaches",
                deposited.recruitments().len(),
                readings[1].1.reaches().len()
            ),
        ),
    );
    holds.push((
        "two independent implementations of betti agree under every incidence aperture",
        readings
            .iter()
            .filter(|(aperture, _, _)| aperture.coefficient == RecruitmentCoefficient::Incidence)
            .all(|(_, circuit, reading)| {
                let forest = circuit.spanning_forest_reading();
                forest.betti_0() == betti_at(reading, 0) && forest.betti_1() == betti_at(reading, 1)
            }),
        "smith normal form against union-find over the same 1-cell supports".to_owned(),
    ));
    holds.push((
        "the cycles the statement incidence opens are the route excess the lineage names",
        agreements.iter().all(|agreement| agreement.holds()),
        format!(
            "homological {:?}, lineage {:?}",
            agreements
                .iter()
                .map(|agreement| agreement.homological)
                .collect::<Vec<_>>(),
            agreements
                .iter()
                .map(|agreement| agreement.lineage)
                .collect::<Vec<_>>()
        ),
    ));
    holds.push((
        "the invariants do not move with the pivot rule, under any aperture",
        pivot_holds,
        "three rules, four apertures".to_owned(),
    ));
    holds.push((
        "CONTROL betti at grade 1 is nonzero under at least one declared aperture",
        readings
            .iter()
            .any(|(_, _, reading)| betti_at(reading, 1) > 0),
        format!(
            "{:?}",
            readings
                .iter()
                .map(|(_, _, reading)| betti_at(reading, 1))
                .collect::<Vec<_>>()
        ),
    ));
    holds.push((
        "CONTROL torsion is nonzero on at least one artifact under the multiplicity coefficient",
        torsion_somewhere,
        format!(
            "distinct torsion classes across the deposit: {:?}",
            torsion_classes.keys().collect::<Vec<_>>()
        ),
    ));
    holds.push((
        "CONTROL the reading is a function of the production, not of the preamble alone",
        declarations_with_plural_recruitment > 0,
        format!(
            "{declarations_with_plural_recruitment} of {} declarations carry more than one \
             recruitment population",
            classes.len()
        ),
    ));

    println!("\nDECLARED CONTROLS — each of these can fail");
    println!("------------------------------------------");
    let mut failed = 0;
    for (claim, held, evidence) in &holds {
        if *held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD — {} declared controls, 0 failed", holds.len());
    } else {
        println!("FAILED — {failed} of {} did not hold", holds.len());
        std::process::exit(1);
    }
}
