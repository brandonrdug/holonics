//! Circuits **grown** from size-agnostic recursive cells, read by the invariants organ.
//!
//! `rebase_invariants.rs` opens by declaring that *the expansion schedule is a receiver* and that
//! the question making a rendering mathematics rather than illustration is *what survives every
//! schedule*. Until `grown_cell.rs` there was no recursive cell in the tree and no expansion
//! schedule: every complex the crate read was produced, never grown. This driver supplies the
//! material and takes the reading.
//!
//! The discipline is MorphoHDL's (Mordvintsev, Google Paradigms of Intelligence, July 2026). There
//! is no `N`, no loop bound and no `if`: width enters as the length of the argument, `split` refuses
//! a bus narrower than two, and the refusal unwinds to a declared fallback. **The base case is the
//! boundary of the material, not a condition the program tests.**
//!
//! What is rendered here is the invariant that survives the schedule, never the embedding that does
//! not. MorphoHDL's pictures are a force-directed relaxation of the *final* gate graph and carry no
//! information about the growth; the rule discipline is ported and the renderer is not.
//!
//! ```text
//!   cargo run --release -p holonic-engine --example grown_circuit_schedules
//! ```
//!
//! Exits nonzero when a declared control fails.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::grown_cell::{
    canonical_netlist, evaluate, found_complex, grow, primitive_section, split, standard_cells, Bus,
    ComplexAperture, Growth, NetId, RuleName, Schedule,
};
use holonic_engine::rebase_invariants::{
    invariants_agree, rebase_invariants_on, rebase_invariants_with_schedule, PivotRule,
    RebaseInvariants,
};
use num_bigint::BigUint;
use num_traits::One;

/// One declared control and whether the run reached it.
struct Control {
    name: &'static str,
    holds: bool,
    detail: String,
}

fn main() {
    let table = standard_cells();
    let mut controls: Vec<Control> = Vec::new();

    banner("what grew");
    println!(
        "  one rule table, {} rules, {} declared output shapes, shared by every width below.",
        table.description().0,
        table.description().1
    );
    println!("  no rule names a width; `split` refuses fewer than two and the refusal is the base case.\n");

    let cells: [(RuleName, &str, fn(usize) -> Vec<usize>); 4] = [
        ("ripple-adder", "carry chain, linear depth", |w| vec![w, w, 1]),
        (
            "brent-kung-adder",
            "prefix adder, logarithmic depth",
            |w| vec![w, w, 1],
        ),
        ("multiplexer", "selection tree", |w| {
            vec![1usize << w, w]
        }),
        ("parity-tree", "reduction tree", |w| vec![w]),
    ];

    println!(
        "  {:<20} {:<34} {:>5} {:>7} {:>6} {:>5} {:>6} {:>6}",
        "cell", "shape", "width", "insts", "gates", "nets", "depth", "sites"
    );
    // The description is the set of `(rule, label)` emission sites the growth used. An indirect
    // encoding is one where that set does not grow with the material.
    //
    // The threshold below which there is nothing to describe is not written down: it is asked of
    // `split`, which is the operation that decides whether material can divide at all.
    let divides_from = (1usize..)
        .find(|width| split(&Bus::new(vec![NetId(1); *width])).is_ok())
        .expect("some width divides");
    let mut steady_sites: BTreeMap<RuleName, BTreeSet<usize>> = BTreeMap::new();
    let mut every_site: BTreeMap<RuleName, BTreeSet<(RuleName, &'static str)>> = BTreeMap::new();
    let mut gate_growth: BTreeMap<RuleName, Vec<usize>> = BTreeMap::new();
    for (rule, shape, material) in cells {
        for width in [1usize, 2, 3, 4, 5, 6, 7] {
            let growth = grow(&table, rule, &material(width), Schedule::Instantiation)
                .unwrap_or_else(|refusal| panic!("{rule} at {width}: {refusal}"));
            if width <= 5 {
                println!(
                    "  {:<20} {:<34} {:>5} {:>7} {:>6} {:>5} {:>6} {:>6}",
                    if width == 1 { rule } else { "" },
                    if width == 1 { shape } else { "" },
                    width,
                    growth.instance_count(),
                    growth.gate_count(),
                    growth.net_count(),
                    growth.depth(),
                    growth.sites.len(),
                );
            }
            if width >= divides_from {
                steady_sites
                    .entry(rule)
                    .or_default()
                    .insert(growth.sites.len());
            }
            every_site
                .entry(rule)
                .or_default()
                .extend(growth.sites.iter().copied());
            gate_growth.entry(rule).or_default().push(growth.gate_count());
        }
        println!();
    }

    // -- control: description length is constant while gate count grows -----------------------
    //
    // Stated exactly, with no threshold written by hand. Below `divides_from` -- the width at which
    // `split` first succeeds -- there is no division to describe and only part of the fallback chain
    // fires, so the description is a strict SUBSET. At and above it the description does not move
    // at all, while the gate count multiplies. A direct encoding would grow with the gates.
    let constant = steady_sites.iter().all(|(_, sites)| sites.len() == 1);
    let union_matches = every_site.iter().all(|(rule, sites)| {
        steady_sites
            .get(rule)
            .and_then(|counts| counts.iter().next().copied())
            == Some(sites.len())
    });
    let growing = gate_growth
        .iter()
        .all(|(_, counts)| counts.last() > counts.first());
    let ratios: Vec<(RuleName, usize)> = gate_growth
        .iter()
        .map(|(rule, counts)| {
            let sites = steady_sites
                .get(rule)
                .and_then(|s| s.iter().next().copied())
                .unwrap_or(1)
                .max(1);
            (*rule, counts.last().copied().unwrap_or(0) / sites)
        })
        .collect();
    println!("  `split` first succeeds at width {divides_from}, which is where a description of division begins.");
    println!("  gates per emission site at the widest growth above: {ratios:?}\n");
    controls.push(Control {
        name: "description length constant while gate count grows",
        holds: constant && union_matches && growing,
        detail: format!(
            "sites at every dividing width {:?}; union over all widths {:?}; gate counts {:?}",
            steady_sites
                .iter()
                .map(|(rule, sites)| (*rule, sites.iter().copied().collect::<Vec<_>>()))
                .collect::<Vec<_>>(),
            every_site
                .iter()
                .map(|(rule, sites)| (*rule, sites.len()))
                .collect::<Vec<_>>(),
            gate_growth
        ),
    });

    // -- the negative pole ---------------------------------------------------------------------
    banner("the negative pole: material that exhausts at once");
    let pole = grow(&table, "multiplexer", &[1, 0], Schedule::Instantiation)
        .expect("the pole grows");
    println!(
        "  multiplexer with no select bits: {} instances, {} gates, {} nets, grew_nothing = {}",
        pole.instance_count(),
        pole.gate_count(),
        pole.net_count(),
        pole.instances[0].grew_nothing
    );
    println!(
        "  the output net IS the input net -- the identity fallback is an alias, not a wire: {:?} == {:?}",
        pole.root_outputs[0].nets(),
        pole.primary_inputs[0].nets()
    );
    let pole_complex = found_complex(&pole, ComplexAperture::BOTH).expect("the pole founds");
    println!(
        "  its complex: {} cells, {} arcs, {} faces",
        pole_complex.complex.cells().len(),
        pole_complex.arcs.len(),
        pole_complex.division_faces + pole_complex.reconvergence_faces
    );
    controls.push(Control {
        name: "a cell whose material exhausts immediately grows nothing",
        holds: pole.gate_count() == 0
            && pole.instances[0].grew_nothing
            && pole.root_outputs[0] == pole.primary_inputs[0]
            && pole_complex.arcs.is_empty(),
        detail: format!("{} gates, {} arcs", pole.gate_count(), pole_complex.arcs.len()),
    });

    // -- the rule-reuse table --------------------------------------------------------------------
    banner("rule reuse: the same rule firing at several widths on different material");
    let wide = grow(&table, "ripple-adder", &[11, 11, 1], Schedule::Instantiation)
        .expect("width eleven grows");
    println!("  ripple-adder at width 11 (an odd width, so `split` is unbalanced throughout)\n");
    println!("  {:<24} {:>10} {:>10}", "rule", "in-width", "instances");
    for ((rule, width), count) in wide.rule_reuse() {
        println!("  {rule:<24} {width:>10} {count:>10}");
    }
    let reused: Vec<(RuleName, usize)> = ["ripple-adder", "full-adder"]
        .iter()
        .map(|rule| (*rule, wide.widths_of(rule).len()))
        .collect();
    println!("\n  distinct widths per rule: {reused:?}");
    controls.push(Control {
        name: "a rule fires at several widths (growth, not macro expansion)",
        holds: reused.iter().any(|(_, widths)| *widths >= 3),
        detail: format!("{reused:?}"),
    });

    // -- the schedules ---------------------------------------------------------------------------
    banner("the expansion schedule is a receiver: different intermediate morphology");
    let odd = 5usize;
    let growths: Vec<Growth> = Schedule::ALL
        .iter()
        .map(|schedule| {
            grow(&table, "ripple-adder", &[odd, odd, 1], *schedule).expect("grows")
        })
        .collect();
    for growth in &growths {
        println!("\n  schedule {}", growth.schedule.name());
        for line in growth.trace_lines().iter().take(6) {
            println!("    {line}");
        }
        if growth.trace_lines().len() > 6 {
            println!("    ... {} more", growth.trace_lines().len() - 6);
        }
    }
    let traces: Vec<Vec<String>> = growths.iter().map(Growth::trace_lines).collect();
    let pairwise_distinct = traces[0] != traces[1] && traces[0] != traces[2] && traces[1] != traces[2];
    println!(
        "\n  three traces pairwise distinct at width {odd}: {pairwise_distinct}"
    );

    // Where the gauge degenerates, and why. A power-of-two bus halves evenly at every level, so
    // widest-first has nothing to prefer. That is a property of the CIRCUIT, exhibited rather than
    // hidden, and it is why the sweep carries a third schedule.
    let balanced: Vec<Vec<String>> = Schedule::ALL
        .iter()
        .map(|schedule| {
            grow(&table, "ripple-adder", &[4, 4, 1], *schedule)
                .expect("grows")
                .trace_lines()
        })
        .collect();
    println!(
        "  at width 4 (balanced halving) instantiation == widest-first: {}, and != deepest: {}",
        balanced[0] == balanced[1],
        balanced[0] != balanced[2]
    );
    controls.push(Control {
        name: "the schedule gauge acts non-trivially on the morphology",
        holds: pairwise_distinct && balanced[0] != balanced[2],
        detail: format!(
            "width {odd} pairwise distinct = {pairwise_distinct}; width 4 deepest differs = {}",
            balanced[0] != balanced[2]
        ),
    });

    // -- and the same netlist under different symbols -------------------------------------------
    banner("...and the same circuit under different symbols");
    let forms: Vec<_> = growths
        .iter()
        .map(|growth| canonical_netlist(growth).expect("canonical"))
        .collect();
    let identifiers: Vec<Vec<u64>> = growths
        .iter()
        .map(|growth| growth.gates.iter().map(|gate| gate.output.0).collect())
        .collect();
    println!(
        "  canonical netlists identical across the three schedules: {}",
        forms[0] == forms[1] && forms[0] == forms[2]
    );
    println!("  first eight gate-output identifiers per schedule (the symbols that moved):");
    for (schedule, ids) in Schedule::ALL.iter().zip(&identifiers) {
        println!(
            "    {:<14} {:?}",
            schedule.name(),
            &ids[..ids.len().min(8)]
        );
    }
    let symbols_moved = identifiers[0] != identifiers[1] || identifiers[0] != identifiers[2];
    controls.push(Control {
        name: "the schedules grow one netlist under different symbols",
        holds: forms[0] == forms[1] && forms[0] == forms[2] && symbols_moved,
        detail: format!("forms agree = {}, symbols moved = {symbols_moved}", forms[0] == forms[1]),
    });

    // The circuit is right, not merely consistent.
    let modulus = 1u32 << odd;
    let mut arithmetic = true;
    for left in 0..modulus {
        for right in 0..modulus {
            let arguments = [bits(left, odd), bits(right, odd), bits(0, 1)];
            let out = evaluate(&growths[0], &arguments).expect("evaluates");
            let total = left + right;
            arithmetic &= number(&out[0]) == total % modulus && number(&out[1]) == total / modulus;
        }
    }
    println!("\n  the grown ripple adder adds, exhaustively over 2^{odd} x 2^{odd}: {arithmetic}");
    controls.push(Control {
        name: "the grown circuit computes what its cell says",
        holds: arithmetic,
        detail: format!("exhaustive over {modulus} x {modulus}"),
    });

    // -- the complex and its invariants ------------------------------------------------------------
    banner("the 2-complex the growth founds");
    println!("  0-cells nets; 1-cells conduction arcs (gate pins and lineage boxes);");
    println!("  2-cells cell division -- a parent's coarse arc against the refinement that replaced it,");
    println!("  attached by the lineage with no embedding search and no choice.\n");
    println!(
        "  {:<20} {:>3} {:>6} {:>5} {:>6} {:>6} {:>6} {:>6} {:>6} {:>8} {:>8}",
        "cell", "w", "cells", "nets", "pins", "boxes", "divis", "recon", "k>1", "max-k", "ms"
    );
    for (rule, widths) in [
        ("ripple-adder", vec![1usize, 2, 3, 4, 5, 6]),
        ("brent-kung-adder", vec![1usize, 2, 3, 4]),
        ("multiplexer", vec![1usize, 2, 3]),
        ("parity-tree", vec![2usize, 4, 6]),
    ] {
        for width in widths {
            let material = material_for(rule, width);
            let growth = grow(&table, rule, &material, Schedule::Instantiation).expect("grows");
            let clock = std::time::Instant::now();
            let grown = found_complex(&growth, ComplexAperture::BOTH).expect("founds");
            println!(
                "  {:<20} {:>3} {:>6} {:>5} {:>6} {:>6} {:>6} {:>6} {:>6} {:>8} {:>8}",
                rule,
                width,
                grown.complex.cells().len(),
                grown.net_cells.len(),
                grown.arcs.iter().filter(|arc| arc.gate.is_some()).count(),
                grown.arcs.iter().filter(|arc| arc.gate.is_none()).count(),
                grown.division_faces,
                grown.reconvergence_faces,
                grown.division_faces_with_multiplicity,
                grown.largest_face_coefficient,
                clock.elapsed().as_millis(),
            );
        }
    }

    // -- the artifact itself: one grown 2-cell, written out ---------------------------------------
    banner("one grown division face, in full");
    println!("  Counts are supporting receipts. This is the cell.\n");
    {
        let growth = grow(&table, "brent-kung-adder", &[2, 2, 1], Schedule::Instantiation)
            .expect("grows");
        let grown = found_complex(&growth, ComplexAperture::DIVISION).expect("founds");
        let names: BTreeMap<_, _> = grown
            .complex
            .cells()
            .iter()
            .map(|(id, cell)| (*id, cell.name.clone()))
            .collect();
        let exhibit = grown
            .complex
            .cells()
            .values()
            .filter(|cell| cell.grade == 2)
            .find(|cell| {
                cell.boundary
                    .coefficients()
                    .values()
                    .any(|coefficient| coefficient.difference().magnitude() > &BigUint::one())
            });
        match exhibit {
            Some(cell) => {
                println!("  2-cell `{}`", cell.name);
                println!("    boundary, as exact integers:");
                let mut terms: Vec<(String, String)> = cell
                    .boundary
                    .coefficients()
                    .iter()
                    .map(|(id, coefficient)| {
                        (
                            names.get(id).cloned().unwrap_or_default(),
                            coefficient.difference().to_string(),
                        )
                    })
                    .collect();
                terms.sort();
                for (name, coefficient) in terms {
                    println!("      {coefficient:>4} * {name}");
                }
                println!("\n    The parent's coarse arc carries the path count; each child arc carries");
                println!("    paths(source -> its tail) * paths(its head -> target). The sum telescopes,");
                println!("    so the face closes -- and `found_cell` refuses `dd != 0`, which is what");
                println!("    verifies the two dynamic programs rather than a comment claiming they are right.");
            }
            None => println!("  NO FACE WITH MULTIPLICITY -- the exhibit did not reach its material."),
        }
    }

    banner("what survives every schedule and every pivot rule");
    println!("  A cost law, measured and declared: the Smith reduction is cubic in the cell count and");
    println!("  its intermediate entries grow, so a reading is taken where it is affordable and the");
    println!("  population census above carries the shape at every width. Elapsed milliseconds are");
    println!("  printed with each reading rather than hidden.\n");

    let readings: Vec<(&str, &str, usize, ComplexAperture)> = vec![
        ("ripple-adder", "division", 3, ComplexAperture::DIVISION),
        ("ripple-adder", "both", 3, ComplexAperture::BOTH),
        ("ripple-adder", "division", 4, ComplexAperture::DIVISION),
        ("brent-kung-adder", "division", 2, ComplexAperture::DIVISION),
        ("brent-kung-adder", "both", 2, ComplexAperture::BOTH),
        ("multiplexer", "division", 2, ComplexAperture::DIVISION),
        ("multiplexer", "both", 2, ComplexAperture::BOTH),
        ("parity-tree", "both", 4, ComplexAperture::BOTH),
    ];

    let mut schedule_agreement = true;
    let mut pivot_agreement = true;
    let mut pivot_paths_differ = false;
    let mut torsion_seen: BTreeMap<u32, Vec<String>> = BTreeMap::new();
    let mut multiplicity_seen = false;

    for (rule, aperture_name, width, aperture) in readings {
        let clock = std::time::Instant::now();
        let material = material_for(rule, width);
        let mut per_schedule: Vec<(Schedule, RebaseInvariants)> = Vec::new();
        let mut populations = String::new();
        for schedule in Schedule::ALL {
            let growth = grow(&table, rule, &material, schedule).expect("grows");
            let grown = match found_complex(&growth, aperture) {
                Ok(grown) => grown,
                Err(refusal) => {
                    println!("  {rule}/{aperture_name} width {width}: REFUSED -- {refusal}");
                    continue;
                }
            };
            if grown.division_faces_with_multiplicity > 0 {
                multiplicity_seen = true;
            }
            if schedule == Schedule::Instantiation {
                populations = format!(
                    "cells {:>5}  nets {:>4}  arcs {:>5} (pins {:>4} / boxes {:>4})  \
                     faces {:>5} (division {:>4} / reconvergence {:>4})  \
                     faces with k>1 {:>4}  largest coefficient {}",
                    grown.complex.cells().len(),
                    grown.net_cells.len(),
                    grown.arcs.len(),
                    grown.arcs.iter().filter(|arc| arc.gate.is_some()).count(),
                    grown.arcs.iter().filter(|arc| arc.gate.is_none()).count(),
                    grown.division_faces + grown.reconvergence_faces,
                    grown.division_faces,
                    grown.reconvergence_faces,
                    grown.division_faces_with_multiplicity,
                    grown.largest_face_coefficient,
                );
            }
            let mut schedules = Vec::new();
            let mut first: Option<RebaseInvariants> = None;
            for pivot in PivotRule::ALL {
                let (invariants, pivot_schedule) =
                    rebase_invariants_with_schedule(&grown.complex, pivot).expect("reads");
                if let Some(reference) = &first {
                    if !invariants_agree(reference, &invariants) {
                        pivot_agreement = false;
                    }
                } else {
                    first = Some(invariants.clone());
                }
                schedules.push(pivot_schedule);
            }
            if schedules[0].per_grade != schedules[1].per_grade
                || schedules[0].per_grade != schedules[2].per_grade
            {
                pivot_paths_differ = true;
            }
            per_schedule.push((schedule, first.expect("one pivot rule at least")));
        }
        if per_schedule.is_empty() {
            continue;
        }
        println!("  {rule} / faces: {aperture_name} / width {width}");
        println!("    {populations}");
        let reference = &per_schedule[0].1;
        for (schedule, invariants) in &per_schedule[1..] {
            if !invariants_agree(reference, invariants) {
                schedule_agreement = false;
                println!("    SCHEDULE DISAGREEMENT at {}", schedule.name());
            }
        }
        for grade in &reference.grades {
            let torsion = if grade.torsion.is_empty() {
                "-".to_owned()
            } else {
                let rendered: Vec<String> = grade
                    .torsion
                    .iter()
                    .map(|factor| format!("Z/{factor}"))
                    .collect();
                torsion_seen
                    .entry(grade.grade)
                    .or_default()
                    .push(format!("{rule}/{aperture_name}/w{width}: {}", rendered.join(" + ")));
                rendered.join(" + ")
            };
            println!(
                "    grade {}  cells {:>5}  boundary-rank {:>5}  filling-rank {:>5}  betti {:>4}  torsion {torsion}",
                grade.grade, grade.cells, grade.boundary_rank, grade.filling_rank, grade.betti
            );
        }
        println!(
            "    euler from betti {} == euler from cells {}: {}   [three schedules x three pivot rules in {} ms]\n",
            reference.euler_characteristic(),
            reference.cell_euler_characteristic(),
            reference.euler_characteristic() == reference.cell_euler_characteristic(),
            clock.elapsed().as_millis()
        );
    }

    controls.push(Control {
        name: "the invariants do not move with the expansion schedule",
        holds: schedule_agreement,
        detail: "betti, ranks and invariant factors compared across all three schedules".to_owned(),
    });
    controls.push(Control {
        name: "the invariants do not move with the pivot rule",
        holds: pivot_agreement,
        detail: "all three pivot rules on every reading".to_owned(),
    });
    controls.push(Control {
        name: "the three pivot rules took different reduction paths (so the agreement has material)",
        holds: pivot_paths_differ,
        detail: "grown division faces carry coefficients above one".to_owned(),
    });
    controls.push(Control {
        name: "a grown face carries multiplicity above one (torsion is reachable in principle)",
        holds: multiplicity_seen,
        detail: "cell division over reconvergent material".to_owned(),
    });

    // -- the aperture axis: a receiver that sees the netlist and not the lineage --------------------
    banner("two apertures on one grown complex");
    println!("  `derivation_atlas` reads one deposit under several declared incidences. The analogue");
    println!("  here is the SECTION: nets and gate pins only -- the netlist a receiver holds when it");
    println!("  cannot see the lineage -- read with `rebase_invariants_on`, against the whole.\n");
    let mut section_agreement = true;
    let mut section_differs = false;
    for (rule, width) in [("ripple-adder", 3usize), ("brent-kung-adder", 2usize)] {
        let mut per_schedule = Vec::new();
        for schedule in Schedule::ALL {
            let growth = grow(&table, rule, &material_for(rule, width), schedule).expect("grows");
            let grown = found_complex(&growth, ComplexAperture::DIVISION).expect("founds");
            let support = primitive_section(&grown).expect("the section is closed");
            let mut readings = Vec::new();
            for pivot in PivotRule::ALL {
                readings.push(
                    rebase_invariants_on(&grown.complex, Some(&support), pivot).expect("reads"),
                );
            }
            if !invariants_agree(&readings[0], &readings[1])
                || !invariants_agree(&readings[0], &readings[2])
            {
                section_agreement = false;
            }
            if schedule == Schedule::Instantiation {
                let whole =
                    rebase_invariants_on(&grown.complex, None, PivotRule::FirstNonzero).unwrap();
                println!(
                    "  {rule} width {width}: section {} of {} cells",
                    support.len(),
                    grown.complex.cells().len()
                );
                for (label, reading) in [("section", &readings[0]), ("whole  ", &whole)] {
                    let rendered: Vec<String> = reading
                        .grades
                        .iter()
                        .map(|grade| {
                            let torsion = if grade.torsion.is_empty() {
                                String::new()
                            } else {
                                format!(
                                    " + {}",
                                    grade
                                        .torsion
                                        .iter()
                                        .map(|factor| format!("Z/{factor}"))
                                        .collect::<Vec<_>>()
                                        .join(" + ")
                                )
                            };
                            format!("H{} = Z^{}{torsion}", grade.grade, grade.betti)
                        })
                        .collect();
                    println!("    {label}  {}", rendered.join("   "));
                }
                if !invariants_agree(&readings[0], &whole) {
                    section_differs = true;
                }
            }
            per_schedule.push(readings.remove(0));
        }
        if !invariants_agree(&per_schedule[0], &per_schedule[1])
            || !invariants_agree(&per_schedule[0], &per_schedule[2])
        {
            section_agreement = false;
        }
        println!();
    }
    controls.push(Control {
        name: "the narrower aperture is a different receiver, and still schedule-independent",
        holds: section_agreement && section_differs,
        detail: format!(
            "section reading agrees across schedules and pivot rules = {section_agreement}; \
             section differs from the whole = {section_differs}"
        ),
    });

    // -- the torsion answer -----------------------------------------------------------------------
    banner("the torsion answer");
    if torsion_seen.is_empty() {
        println!("  NO TORSION AT ANY GRADE, in any reading above.");
    } else {
        for (grade, sightings) in &torsion_seen {
            println!("  grade {grade}:");
            for sighting in sightings {
                println!("    {sighting}");
            }
        }
    }
    println!();
    let reconvergence = reconvergence_census(&table);
    println!("  where multiplicity comes from, measured:");
    for (rule, width, faces, multiplicity, largest) in &reconvergence {
        println!(
            "    {rule:<20} width {width}  division faces {faces:>4}  of which k>1: {multiplicity:>4}  largest coefficient {largest}"
        );
    }
    println!();
    println!("  A ripple-carry adder built from three-input primitives never reconverges: every");
    println!("  net's fan-out enters disjoint cones, so every division face carries k = 1 and the");
    println!("  boundary is an incidence matrix. Brent-Kung reconverges, because the propagate and");
    println!("  the generate of one half both reach the same group carry -- so k > 1 appears from");
    println!("  the CIRCUIT and from nothing the reading chose.");

    // -- verdict ----------------------------------------------------------------------------------
    banner("declared controls");
    let mut failed = 0usize;
    for control in &controls {
        println!(
            "  [{}] {}\n        {}",
            if control.holds { "HOLDS " } else { "FAILED" },
            control.name,
            control.detail
        );
        if !control.holds {
            failed += 1;
        }
    }
    println!();
    if failed > 0 {
        println!("  {failed} declared control(s) did not hold.");
        std::process::exit(1);
    }
    println!("  every declared control held.");
}

fn reconvergence_census(
    table: &holonic_engine::grown_cell::RuleTable,
) -> Vec<(RuleName, usize, usize, usize, BigUint)> {
    let mut rows = Vec::new();
    for (rule, widths) in [
        ("ripple-adder", vec![2usize, 3, 4]),
        ("brent-kung-adder", vec![2usize, 3, 4]),
        ("multiplexer", vec![1usize, 2]),
        ("parity-tree", vec![4usize, 5]),
    ] {
        for width in widths {
            let material = material_for(rule, width);
            let growth = grow(table, rule, &material, Schedule::Instantiation).expect("grows");
            let grown = found_complex(&growth, ComplexAperture::DIVISION).expect("founds");
            rows.push((
                rule,
                width,
                grown.division_faces,
                grown.division_faces_with_multiplicity,
                if grown.largest_face_coefficient.is_one() {
                    BigUint::one()
                } else {
                    grown.largest_face_coefficient.clone()
                },
            ));
        }
    }
    rows
}

/// The material a cell is handed. Not a parameter of the cell: it is the length of what arrives.
fn material_for(rule: RuleName, width: usize) -> Vec<usize> {
    match rule {
        "multiplexer" => vec![1usize << width, width],
        "parity-tree" => vec![width],
        _ => vec![width, width, 1],
    }
}

fn bits(value: u32, width: usize) -> Vec<u8> {
    (0..width).map(|bit| ((value >> bit) & 1) as u8).collect()
}

fn number(bits: &[u8]) -> u32 {
    bits.iter()
        .enumerate()
        .map(|(position, bit)| u32::from(*bit) << position)
        .sum()
}

fn banner(title: &str) {
    println!("\n{title}");
    println!("{}", "=".repeat(title.len()));
}
