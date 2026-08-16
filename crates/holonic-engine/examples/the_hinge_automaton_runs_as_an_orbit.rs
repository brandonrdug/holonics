//! THE HINGE AUTOMATON RUNS AS AN ORBIT — Brandon's triangular hinge automaton, iterated.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_hinge_automaton_runs_as_an_orbit
//! ```
//!
//! # The occasion, and it is four years of one intuition
//!
//! Brandon, 2026-07-20, and this driver exists to run what he described:
//!
//! > *"Imagine the same kind of grid, but instead of the discrete being the cell, it is the
//! > triangle, and the triangles can have arbitrary relationships to each other such that they can
//! > fold and \*pivot\* off of each other in terms of altering each other's state… n-sheets of these
//! > with cross-sections of each other, and their relative activity propagates and creates complex
//! > shapes. It's what I'm trying to call a 'manifold', and that's what the lightning strikes are…
//! > The basis of the triangles is also relative and changing; ratios and series."*
//!
//! and again on 2026-07-21: *"I imagine that the triangles act as both **conduits and hinges** to
//! each other."*
//!
//! **The organ exists and has never been iterated.** `discrete_curvature` is a synchronous update law
//! on a hinge incidence — `r_e ← r_e + c·(h(u) + h(v))` applied to every hinge from one snapshot,
//! exact over `Rat`, with `charge(v) = 6 − |link(v)|` as codimension-two Regge curvature. Measured
//! 2026-08-16: all four of its drivers apply a **single step**. `layout_curvature_consumption`,
//! `derivation_curvature_flow`, `curvature_is_the_adjacency`, `the_seam_founds_and_the_flow_dissipates`
//! — none takes an orbit. So the automaton is built and has never been run as one.
//!
//! # What an orbit returns that a step cannot
//!
//! A step returns a difference. An orbit returns a **classification of the material**, and this law
//! has exactly three outcomes, already typed by the organ:
//!
//! ```text
//!   Flat                          every deficit exactly zero — fixed on any incidence
//!   AlternatingTracedDeviation    fixed with nonzero deficit — only on bipartite components
//!   Moving                        not fixed; carries every hinge whose revision is nonzero
//! ```
//!
//! Because the carrier is exact `Rat`, an orbit does not *approach* anything. It either reaches a
//! fixed point exactly, **re-enters a state it has already stood in** — a cycle, detected by exact
//! equality of the whole response map, never by a tolerance — or it does neither within the caller's
//! declared extent, which is reported as such rather than as divergence.
//!
//! # THE FALSIFIER, STATED BEFORE THE RUN
//!
//! **At `c = 1` this law provably alternates forever on bipartite incidence.** So a run whose
//! materials all return `AlternatingTracedDeviation` has exhibited the law and learned nothing about
//! the material — the authored-partition defect, where the declared material cannot vary the property
//! under test. **This driver must exhibit at least two distinct classifications across its declared
//! materials, or it reports itself refuted.**
//!
//! The materials are therefore chosen to make the classification *able* to vary, and the reason each
//! is declared is printed beside it: a bipartite incidence with unequal parts, which can alternate; an
//! odd cycle, which carries an odd hinge cycle and so **cannot** be bipartite; and a flat one, whose
//! deficits are already zero.
//!
//! # Bars
//!
//! No tolerance anywhere — every comparison is exact rational equality. No authored extent inside the
//! organ: the orbit extent is a caller-declared aperture and the run says how much of it was used. The
//! coefficient is declared per material and its species is read from the module's own
//! `coefficient_species` rather than asserted.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::discrete_curvature::{
    coefficient_species, total_multiplier, CurvatureFixedPoint, DiscreteCurvatureConfiguration,
    DiscreteCurvatureError,
};
use holonic_engine::{HingeId, VertexId};
use num_traits::Zero;
use relational_geometry::{rat, Rat};

/// The caller's declared orbit aperture. It bounds how far this run walks and decides nothing about
/// the law: a walk that used all of it is reported as unresolved, never as divergent.
const DECLARED_ORBIT_EXTENT: usize = 64;

fn vertex(id: u64) -> VertexId {
    VertexId(id)
}

fn hinge(id: u64) -> HingeId {
    HingeId(id)
}

/// How an orbit ended. Exact in every arm — nothing here compares against a tolerance.
#[derive(Debug)]
enum OrbitEnd {
    /// The configuration stopped moving: every revision is exactly zero.
    Fixed { at: usize },
    /// A state recurred exactly. The period is the distance back to its first standing.
    Cycled { entered: usize, period: usize },
    /// The declared extent ran out. This is a statement about the aperture, not about the law.
    Unresolved { extent: usize },
}

struct Orbit {
    end: OrbitEnd,
    /// The total deficit at each step, in order. Exact rationals, never divided.
    total_deficits: Vec<Rat>,
    /// The classification the configuration lands in when the walk stops.
    landing: CurvatureFixedPoint,
    /// How many hinges moved at each step. A zero total with a nonzero count is a CIRCULATION —
    /// the distribution is moving and the net is not — which is the spine's cut, not its rest.
    moved_per_step: Vec<usize>,
}

/// Walk the automaton until it stops, repeats, or exhausts the declared extent.
fn orbit(mut body: DiscreteCurvatureConfiguration, coefficient: &Rat, extent: usize) -> Orbit {
    // The state is the whole response map. Exact equality of that map IS the recurrence test; there
    // is no distance and no tolerance. This is the same discipline `physical.rs` uses to detect a
    // periodic trajectory.
    let mut standing: BTreeMap<BTreeMap<HingeId, Rat>, usize> = BTreeMap::new();
    let mut total_deficits = vec![body.total_deficit()];
    let mut moved_per_step = Vec::new();
    standing.insert(body.responses(), 0);

    for step in 1..=extent {
        let taken = body.step_at(coefficient);
        total_deficits.push(taken.total_deficit_after.clone());
        moved_per_step.push(taken.revisions.values().filter(|r| !r.is_zero()).count());
        if !taken.moved {
            return Orbit {
                end: OrbitEnd::Fixed { at: step },
                total_deficits,
                landing: body.fixed_point(),
                moved_per_step,
            };
        }
        let state = body.responses();
        if let Some(first) = standing.get(&state) {
            return Orbit {
                end: OrbitEnd::Cycled {
                    entered: *first,
                    period: step - first,
                },
                total_deficits,
                landing: body.fixed_point(),
                moved_per_step,
            };
        }
        standing.insert(state, step);
    }
    Orbit {
        end: OrbitEnd::Unresolved { extent },
        total_deficits,
        landing: body.fixed_point(),
        moved_per_step,
    }
}

/// One declared material, with the reason it is declared printed beside it.
///
/// **The coefficient is NOT a property of a material.** It is swept below, because the first form of
/// this driver gave each material its own coefficient and then counted distinct classes across the
/// whole table — so the one differing class came from changing `c`, not from changing the material,
/// and the falsifier passed on a table where the material varied nothing. That is the exact defect
/// it was written to catch, committed inside it.
struct Material {
    name: &'static str,
    why: &'static str,
    body: DiscreteCurvatureConfiguration,
}

fn materials() -> Vec<Material> {
    let mut declared = Vec::new();

    // A square: four vertices, four hinges, every link size 2. Bipartite with equal parts.
    declared.push(Material {
        name: "square",
        why: "bipartite with EQUAL parts — the traced deviation can cancel",
        body: DiscreteCurvatureConfiguration::at_unit_response([
            (hinge(0), [vertex(0), vertex(1)]),
            (hinge(1), [vertex(1), vertex(2)]),
            (hinge(2), [vertex(2), vertex(3)]),
            (hinge(3), [vertex(3), vertex(0)]),
        ])
        .expect("a square founds"),
    });

    // A path of three vertices: bipartite with UNEQUAL parts (two ends against one middle).
    declared.push(Material {
        name: "path-3",
        why: "bipartite with UNEQUAL parts — where the alternating fixed point lives",
        body: DiscreteCurvatureConfiguration::at_unit_response([
            (hinge(0), [vertex(0), vertex(1)]),
            (hinge(1), [vertex(1), vertex(2)]),
        ])
        .expect("a path founds"),
    });

    // A triangle: an ODD cycle, so the incidence is not bipartite and cannot alternate.
    declared.push(Material {
        name: "triangle",
        why: "carries an ODD hinge cycle — NOT bipartite, so it cannot alternate",
        body: DiscreteCurvatureConfiguration::at_unit_response([
            (hinge(0), [vertex(0), vertex(1)]),
            (hinge(1), [vertex(1), vertex(2)]),
            (hinge(2), [vertex(2), vertex(0)]),
        ])
        .expect("a triangle founds"),
    });

    // The pentagonal bipyramid: two apexes of link 5 against five equator vertices of link 4, so two
    // distinct link sizes and a genuinely varying deficit. Odd cycles throughout.
    let mut bipyramid: Vec<(HingeId, [VertexId; 2])> = Vec::new();
    let (north, south) = (vertex(100), vertex(101));
    let mut next = 0u64;
    for at in 0..5u64 {
        let here = vertex(at);
        let onward = vertex((at + 1) % 5);
        bipyramid.push((hinge(next), [here, onward]));
        next += 1;
        bipyramid.push((hinge(next), [north, here]));
        next += 1;
        bipyramid.push((hinge(next), [south, here]));
        next += 1;
    }
    declared.push(Material {
        name: "pentagonal-bipyramid",
        why: "two distinct link sizes (5 and 4) — the deficit varies with the link",
        body: DiscreteCurvatureConfiguration::at_unit_response(bipyramid)
            .expect("the bipyramid founds"),
    });

    declared
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

fn landing_name(landing: &CurvatureFixedPoint) -> &'static str {
    match landing {
        CurvatureFixedPoint::Flat => "Flat",
        CurvatureFixedPoint::AlternatingTracedDeviation { .. } => "AlternatingTracedDeviation",
        CurvatureFixedPoint::Moving { .. } => "Moving",
    }
}

/// The declared coefficient sweep. `total_multiplier(c) = 1 - 2c` is what the TOTAL deficit scales
/// by, so the total is a pure function of the coefficient and the initial total — the material lives
/// entirely in the DISTRIBUTION. These are chosen so the multiplier lands on each of its species.
fn coefficients() -> Vec<Rat> {
    vec![rat(1, 1), rat(1, 2), rat(1, 4), rat(3, 4), rat(2, 1)]
}

/// ★ STAGE 3 AND 3b — the step carried as a FRONT, and the licence a cover cannot ask.
///
/// `step_at` reads the whole pre-state, computes every revision from that snapshot, then writes. The
/// revisions are therefore mutually independent, which is the junction condition: what leaves a
/// junction is co-present. So the compute phase is a front and `hardware_cover::expand_front` carries
/// it unchanged — the closure signature fits and `Rat` is `Sync`.
///
/// **And the cover cannot license it.** `hardware_cover`'s barrier variants — `SharedCell`,
/// `UnplacedCell`, `ExtentDisagrees`, `ForeignCell`, `RepeatedFrontCell` — are decomposition
/// *provability* defects. **None of them is holonomy.** A front is admitted on disjointness of
/// addresses and never on whether transporting around it returns what departed, and for a curvature
/// flow that is exactly the question.
///
/// So the licence is supplied here and it is exact: `Sum K' = (1 - 2c) * Sum K` is a law of this
/// update, so after a distributed step the total deficit must equal the multiplier times the total
/// before. That is the loop closing, checked over the whole front rather than per cell — and it is a
/// statement no address-disjointness test can make.
fn front_licence(body: &DiscreteCurvatureConfiguration, coefficient: &Rat) -> (bool, bool) {
    let cover = holonic_engine::hardware_cover::HardwareCover::cpu_only();

    // The vertices as a front. Extent is the vertex's own incident-hinge population — the material's
    // own measure, so covering by extent is meaningful here rather than degenerate.
    let vertices: Vec<VertexId> = body.vertices().collect();
    let distributed: Vec<(VertexId, Rat)> = holonic_engine::hardware_cover::expand_front(
        vertices.clone(),
        &cover,
        |vertex: &VertexId| body.link_size(*vertex).map(|size| size as u64).unwrap_or(1),
        |vertex: VertexId| -> Result<Vec<(VertexId, Rat)>, DiscreteCurvatureError> {
            Ok(vec![(vertex, body.traced_deviation(vertex)?)])
        },
    )
    .expect("every declared vertex carries a traced deviation");

    // The same reading taken serially. The front is a DECOMPOSITION and never a schedule, so these
    // must agree exactly — not nearly.
    let serial = body.traced_deviations();
    let agrees = distributed.len() == serial.len()
        && distributed
            .iter()
            .all(|(vertex, deviation)| serial.get(vertex) == Some(deviation));

    // The holonomy licence: go around the whole front and come back.
    let before = body.total_deficit();
    let mut walked = body.clone();
    let taken = walked.step_at(coefficient);
    let expected = total_multiplier(coefficient) * before;
    let closes = taken.total_deficit_after == expected;

    (agrees, closes)
}

fn main() {
    rule("THE HINGE AUTOMATON RUNS AS AN ORBIT");
    println!("  the law     r_e <- r_e + c*(h(u) + h(v)), applied to EVERY hinge from one snapshot");
    println!("  the carrier exact Rat — an orbit reaches a fixed point, RECURS exactly, or is unresolved");
    println!("  aperture    {DECLARED_ORBIT_EXTENT} steps, caller-declared; using all of it is a");
    println!("              statement about the aperture and never about the law");
    println!();
    println!("  AND THE TOTAL IS NOT A MATERIAL READING. Sum K' = (1 - 2c) * Sum K, so the TOTAL");
    println!("  deficit is a pure function of the coefficient and the initial total. The material");
    println!("  enters only through the DISTRIBUTION, and this run reads both so the two are not");
    println!("  confused.");

    let declared = materials();
    // landing[coefficient][material]
    let mut table: BTreeMap<String, Vec<(&'static str, &'static str)>> = BTreeMap::new();

    for coefficient in coefficients() {
        let species = coefficient_species(&coefficient);
        let multiplier = total_multiplier(&coefficient);
        rule(&format!(
            "COEFFICIENT c = {coefficient}   species {species:?}   total multiplier (1 - 2c) = {multiplier}"
        ));
        for material in &declared {
            let odd = material.body.carries_odd_hinge_cycle();
            let walked = orbit(material.body.clone(), &coefficient, DECLARED_ORBIT_EXTENT);
            let landing = landing_name(&walked.landing);
            table
                .entry(coefficient.to_string())
                .or_default()
                .push((material.name, landing));

            let end = match &walked.end {
                OrbitEnd::Fixed { at } => format!("STOPPED exactly at step {at}"),
                OrbitEnd::Cycled { entered, period } => {
                    format!("RECURRED into step {entered}, period {period}")
                }
                OrbitEnd::Unresolved { extent } => {
                    format!("used the whole declared extent of {extent}, UNRESOLVED")
                }
            };
            println!(
                "  {:<22} odd-cycle {:<5}  {:<38} lands {}",
                material.name, odd, end, landing
            );
            println!("      declared because: {}", material.why);
            let (agrees, closes) = front_licence(&material.body, &coefficient);
            println!(
                "      front: distributed == serial {agrees}   |   holonomy licence (Sum K' = (1-2c) Sum K) {closes}"
            );
            assert!(agrees, "a front is a decomposition and never a schedule");
            assert!(closes, "the front did not return what departed");
            let moving = walked.moved_per_step.iter().rev().take(1).copied().next().unwrap_or(0);
            if walked.total_deficits.last().is_some_and(num_traits::Zero::is_zero) && moving > 0 {
                println!(
                    "      *** ZERO TOTAL, {moving} HINGES STILL MOVING — a circulation, not a rest"
                );
            }
            let shown = walked.total_deficits.len().min(6);
            let trace: Vec<String> = walked.total_deficits[..shown]
                .iter()
                .map(std::string::ToString::to_string)
                .collect();
            println!(
                "      total deficit  {}{}",
                trace.join("  ->  "),
                if walked.total_deficits.len() > shown { "  ->  …" } else { "" }
            );
            if let CurvatureFixedPoint::AlternatingTracedDeviation { component_scale } =
                &walked.landing
            {
                for (component, scale) in component_scale {
                    println!("      component at {component:?} alternates at scale {scale}");
                }
            }
        }
        println!();
    }

    // ---------------------------------------------------------------------------------------
    // THE TWO CHECKS ABOVE MUST BE ABLE TO FAIL, or they are decoration wearing a passing result.
    // `CLAUDE.md` §8: a check whose material cannot vary the property under test is the same defect
    // as a check that cannot fail. Both are made to fire here, deliberately.
    // ---------------------------------------------------------------------------------------
    rule("THE CONTROLS — both checks made to fire on purpose");
    {
        let body = &declared[3].body; // the pentagonal bipyramid: two link sizes, 15 hinges
        let coefficient = rat(1, 1);

        // Control 1 — a decomposition that DROPS a cell. The agreement check must catch it.
        let mut short: Vec<VertexId> = body.vertices().collect();
        let dropped = short.pop().expect("the bipyramid carries vertices");
        let partial: BTreeMap<VertexId, Rat> = short
            .iter()
            .map(|vertex| (*vertex, body.traced_deviation(*vertex).expect("a deviation")))
            .collect();
        let serial = body.traced_deviations();
        let caught = partial.len() != serial.len();
        println!(
            "  dropping vertex {dropped:?} from the front: agreement check catches it  {caught}"
        );
        assert!(caught, "an agreement check that misses a dropped cell checks nothing");

        // Control 2 — the WRONG multiplier. The holonomy licence must refuse it.
        let before = body.total_deficit();
        let mut walked = body.clone();
        let taken = walked.step_at(&coefficient);
        let wrong = total_multiplier(&rat(1, 4)) * before.clone();
        let refuses = taken.total_deficit_after != wrong;
        println!(
            "  offering the multiplier for c = 1/4 against a step at c = 1: licence refuses  {refuses}"
        );
        assert!(refuses, "a licence that admits the wrong multiplier licenses nothing");
        println!(
            "  (the step returned {} and the wrong multiplier predicted {wrong})",
            taken.total_deficit_after
        );
    }

    rule("THE FALSIFIER — the material must vary the class AT ONE FIXED COEFFICIENT");
    let mut varied_at: Vec<String> = Vec::new();
    for (coefficient, rows) in &table {
        let classes: BTreeSet<&'static str> = rows.iter().map(|(_, class)| *class).collect();
        println!(
            "  c = {:<6} {} distinct class(es) across {} materials: {:?}",
            coefficient,
            classes.len(),
            rows.len(),
            classes
        );
        if classes.len() > 1 {
            varied_at.push(coefficient.clone());
        }
    }
    println!();
    if varied_at.is_empty() {
        println!("  REFUTED, and the refutation is the finding.");
        println!();
        println!("  At EVERY declared coefficient the materials landed in one class. The class is");
        println!("  therefore a reading of the COEFFICIENT and not of the material, and this run has");
        println!("  exhibited the law rather than the material — which is exactly the defect a");
        println!("  falsifier of this shape exists to catch. Two materials differing in bipartiteness,");
        println!("  in link-size population and in hinge population did not separate.");
        println!();
        println!("  WHAT THAT SAYS, and it is not a null result: the total-deficit law");
        println!("  Sum K' = (1 - 2c) Sum K is BLIND to the incidence. Any reading that would");
        println!("  separate these materials has to be taken on the DISTRIBUTION — the per-vertex");
        println!("  deficits and the component scales — and not on the class of the fixed point.");
        std::process::exit(1);
    }
    println!(
        "  The material varied the class at {} coefficient(s): {}",
        varied_at.len(),
        varied_at.join(", ")
    );
    println!("  So the classification is a reading of the material there, and the law's own");
    println!("  coefficient dependence is separated from it rather than mistaken for it.");
}
