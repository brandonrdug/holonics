//! A circuit grown twice under two different schedules, and the invariants that do not move.
//!
//! ## What this is
//!
//! The holonic analogue of MorphoHDL, which grows physical circuit layout from a recursive cell:
//!
//! ```text
//!   MorphoHDL                    holonic
//!   @morpho recursive cell  ->   a founding that divides
//!   SPLIT                   ->   the receiver quotient selecting distinctions
//!   CAT                     ->   composition of returns
//!   fallback=               ->   OPEN, the declared status where nothing more can be founded
//!   inferred bus width      ->   the aperture is fixed by what attaches, never declared
//!   a wire                  ->   a transport
//!   the grown layout        ->   ONE CHART
//! ```
//!
//! The load-bearing figure is the **expansion schedule**, not the picture. The same cell expanded
//! breadth-first and expanded largest-first produces visibly different layouts. The schedule is a
//! receiver; the layout is its chart; and the question that makes rendering mathematics rather than
//! illustration is *what survives every schedule*.
//!
//! This driver answers that question in exact integers and prints both sides so the difference in
//! the charts and the identity of the invariants are visible at once.
//!
//! ## Why it needs no external checker
//!
//! Brandon, 2026-08-06: *"the symbol does not dictate what the information contains, you could
//! reorganize the symbols and the structure of the proof or algorithm would determine the identity
//! of the underlying algorithmic patterns."* Sameness-under-reorganization is a property only the
//! atlas holding both charts can compute, so it is computed here, internally, over `BigInt`, with
//! no tolerance and nothing consulted outside the machine.
//!
//! ## Where it is more than MorphoHDL
//!
//! MorphoHDL grows a two-dimensional layout and the layout is the artifact. Here the complex is the
//! artifact at arbitrary grade, and every layout is a projection of it — *"the lightning arcs cannot
//! be constrained to the plane […] the curve on the plane and the area are projections caused by
//! higher dimensional dynamics."*
//!
//! ## The controls
//!
//! Per `CLAUDE.md` §8, a law that returns zero proves nothing about itself. Three structures are
//! grown, not one:
//!
//! - a **tree**, which must return no loops and no torsion — the free case;
//! - a **cyclic** growth, which must return loops, so the loop count is shown to be capable of
//!   being nonzero;
//! - a **wound** growth whose face attaches to its rim twice, which must return torsion, so the
//!   torsion column is shown to be capable of being nonzero.
//!
//! Without the last two the run would be a law that never fired.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::dilation::{covering_horizon, dilate, euler_reading, Horizon, WalkOrder};
use holonic_engine::rebase_invariants::{
    invariants_agree, rebase_invariants, rebase_invariants_on, PivotRule, RebaseInvariants,
};

// -------------------------------------------------------------------------------------------
// the schedule, which is a receiver

/// The order in which pending cells are expanded.
///
/// This is the whole point of the driver: it is a *parameter*, and the layouts it produces differ.
/// Ten sites in this crate presently hardcode `pop_front`, which is `Breadth` with the choice
/// invisible.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Schedule {
    /// Take the oldest pending site. MorphoHDL's breadth-first layout.
    Breadth,
    /// Take the pending site with the largest remaining aperture. MorphoHDL's largest-first layout.
    LargestFirst,
    /// Take the newest pending site. Depth-first, included so the sweep is not two points.
    Depth,
}

impl Schedule {
    const ALL: [Self; 3] = [Self::Breadth, Self::LargestFirst, Self::Depth];

    fn name(self) -> &'static str {
        match self {
            Self::Breadth => "breadth",
            Self::LargestFirst => "largest-first",
            Self::Depth => "depth",
        }
    }

    fn take(self, pending: &mut VecDeque<Site>) -> Option<Site> {
        match self {
            Self::Breadth => pending.pop_front(),
            Self::Depth => pending.pop_back(),
            Self::LargestFirst => {
                let at = pending
                    .iter()
                    .enumerate()
                    .max_by_key(|(index, site)| (site.aperture, std::cmp::Reverse(*index)))
                    .map(|(index, _)| index)?;
                pending.remove(at)
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// the recursive cell

/// One pending expansion site: a vertex that has not yet divided, and how much aperture remains.
#[derive(Clone, Debug)]
struct Site {
    vertex: CausalCellId,
    label: String,
    aperture: u32,
}

/// What a growth returns: the complex, the order sites were actually expanded in, and the layout.
struct Growth {
    complex: GradedCausalComplex,
    root: CausalCellId,
    /// The chart. Expansion order is exactly what differs between schedules.
    layout: Vec<String>,
    edges: Vec<CausalCellId>,
    rim: Vec<CausalCellId>,
}

/// The shape being grown. `Rim` closes the frontier into a cycle; `Wound` then attaches a face to
/// that cycle **twice**, which is the only way an integer reduction returns torsion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Closure {
    Tree,
    Rim,
    Wound,
}

fn event(counter: &mut u64) -> BTreeSet<EventId> {
    *counter += 1;
    BTreeSet::from([EventId(*counter)])
}

/// Grow a recursive cell under one schedule.
///
/// The cell divides into `split` children while aperture remains; `aperture == 0` is `fallback=`,
/// the declared OPEN where no further founding is possible. The aperture is never declared on a
/// wire — it is fixed by what attaches.
fn grow(schedule: Schedule, depth: u32, split: u32, closure: Closure) -> Growth {
    let mut complex = GradedCausalComplex::default();
    let mut counter = 0u64;
    let mut layout = Vec::new();
    let mut edges = Vec::new();

    let root = complex
        .found_cell("root", event(&mut counter), 0, CausalChain::default())
        .expect("the root vertex has no boundary");
    let mut pending = VecDeque::from([Site {
        vertex: root,
        label: "root".to_owned(),
        aperture: depth,
    }]);

    let mut frontier: Vec<(CausalCellId, String)> = Vec::new();
    let mut step = 0usize;

    while let Some(site) = schedule.take(&mut pending) {
        if site.aperture == 0 {
            // fallback= : OPEN. The site is a declared terminus, not a failure.
            layout.push(format!("  {step:>3}  OPEN   {}", site.label));
            frontier.push((site.vertex, site.label));
            step += 1;
            continue;
        }
        layout.push(format!(
            "  {step:>3}  SPLIT  {} -> {split} (aperture {})",
            site.label, site.aperture
        ));
        step += 1;
        for child in 0..split {
            let label = format!("{}.{child}", site.label);
            let vertex = complex
                .found_cell(label.clone(), event(&mut counter), 0, CausalChain::default())
                .expect("a vertex has no boundary");
            let mut boundary = CausalChain::default();
            boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(site.vertex, ComparativeMultiplicity::negative(1u32));
            let edge = complex
                .found_cell(
                    format!("wire:{}->{label}", site.label),
                    event(&mut counter),
                    1,
                    boundary,
                )
                .expect("an edge between two founded vertices closes");
            edges.push(edge);
            // NON-UNIFORM on purpose, and non-uniform in the direction that matters. If every
            // branch carried the same remaining aperture, `LargestFirst` would coincide with
            // `Breadth` exactly and the sweep would be two points wearing three names — a schedule
            // that cannot change the layout is not a schedule.
            //
            // Giving the FIRST child the larger aperture is not enough either, and the first run
            // proved it: the widest site was then always the oldest, so largest-first still picked
            // what breadth-first would have picked. The LAST child carries the deepest branch, so
            // the widest pending site is a young one and the two schedules genuinely diverge. This
            // is also the honest reading of MorphoHDL, where cell size does not track discovery
            // order at all.
            let inherited = if child + 1 == split {
                site.aperture - 1
            } else {
                site.aperture.saturating_sub(2)
            };
            pending.push_back(Site {
                vertex,
                label,
                aperture: inherited,
            });
        }
    }

    // Closing the frontier into a rim is what makes loops, and a rim is what a face can wind on.
    let mut rim = Vec::new();
    if closure != Closure::Tree && frontier.len() > 1 {
        for index in 0..frontier.len() {
            let (from, from_label) = &frontier[index];
            let (to, to_label) = &frontier[(index + 1) % frontier.len()];
            let mut boundary = CausalChain::default();
            boundary.add_term(*to, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(*from, ComparativeMultiplicity::negative(1u32));
            let edge = complex
                .found_cell(
                    format!("rim:{from_label}->{to_label}"),
                    event(&mut counter),
                    1,
                    boundary,
                )
                .expect("a rim edge closes");
            rim.push(edge);
        }
    }

    if closure == Closure::Wound && !rim.is_empty() {
        // The face attaches to the rim twice. Its boundary is 2 * (the rim cycle), which is a
        // boundary the rationals cannot distinguish from zero and the integers can.
        let mut boundary = CausalChain::default();
        for edge in &rim {
            boundary.add_term(*edge, ComparativeMultiplicity::positive(2u32));
        }
        complex
            .found_cell("wound-face", event(&mut counter), 2, boundary)
            .expect("the doubled rim is a cycle, so the face closes");
    }

    Growth {
        complex,
        root,
        layout,
        edges,
        rim,
    }
}

// -------------------------------------------------------------------------------------------
// reporting

fn render(invariants: &RebaseInvariants) -> String {
    let mut out = String::new();
    for grade in &invariants.grades {
        let torsion = if grade.torsion.is_empty() {
            "-".to_owned()
        } else {
            grade
                .torsion
                .iter()
                .map(|factor| format!("Z/{factor}"))
                .collect::<Vec<_>>()
                .join(" + ")
        };
        out.push_str(&format!(
            "    grade {}  cells {:>4}  betti {:>3}  torsion {torsion}\n",
            grade.grade, grade.cells, grade.betti
        ));
    }
    out
}

struct Reading {
    schedule: Schedule,
    invariants: RebaseInvariants,
    layout_digest: String,
    cells: usize,
}

/// A cheap order-sensitive digest of the chart, so "the layouts differ" is shown rather than
/// asserted. Deliberately sensitive to expansion order and nothing else.
fn layout_digest(layout: &[String]) -> String {
    let mut accumulator: u64 = 0xcbf2_9ce4_8422_2325;
    for (position, line) in layout.iter().enumerate() {
        for octet in line.as_bytes() {
            accumulator ^= u64::from(*octet).wrapping_add(position as u64);
            accumulator = accumulator.wrapping_mul(0x100_0000_01b3);
        }
    }
    format!("{accumulator:016x}")
}

fn sweep(title: &str, depth: u32, split: u32, closure: Closure) -> Vec<Reading> {
    println!("\n{title}");
    println!("{}", "-".repeat(title.len()));

    let mut readings = Vec::new();
    for schedule in Schedule::ALL {
        let growth = grow(schedule, depth, split, closure);
        let invariants = rebase_invariants(&growth.complex, PivotRule::SmallestMagnitude)
            .expect("every cell in a grown complex resolves");
        println!(
            "\n  schedule {:<14} sites {:>3}  wires {:>3}  rim {:>3}  layout {}",
            schedule.name(),
            growth.layout.len(),
            growth.edges.len(),
            growth.rim.len(),
            layout_digest(&growth.layout),
        );
        for line in growth.layout.iter().take(4) {
            println!("  {line}");
        }
        if growth.layout.len() > 4 {
            println!("       ... {} more", growth.layout.len() - 4);
        }
        print!("{}", render(&invariants));
        readings.push(Reading {
            schedule,
            layout_digest: layout_digest(&growth.layout),
            cells: growth.complex.cells().len(),
            invariants,
        });
    }
    readings
}

/// Dilation on a structure the machine grew, rather than one authored for the test.
///
/// A receiver at a declared horizon holds a section. Above the covering horizon, changing the
/// horizon or the walk order moves the chart and nothing else — the gauge. Below it, the receiver
/// genuinely sees less and the invariants move, which is not a defect and is the only reason the
/// gauge half is testable at all.
fn dilation_sweep(holds: &mut Vec<(&'static str, bool, String)>) {
    println!("\nDilating a receiver over the grown circuit");
    println!("------------------------------------------");

    let growth = grow(Schedule::Breadth, 3, 2, Closure::Rim);
    let whole = rebase_invariants_on(&growth.complex, None, PivotRule::SmallestMagnitude)
        .expect("the whole incidence reads");
    let covering = covering_horizon(&growth.complex, growth.root).expect("the focus resolves");
    println!(
        "  focus {:?}  covering horizon {covering}  whole {:?}",
        growth.root,
        whole.betti_vector()
    );

    let unbounded_support = dilate(
        &growth.complex,
        growth.root,
        Horizon::Unbounded,
        WalkOrder::Breadth,
    )
    .expect("an unbounded dilation resolves")
    .support;

    let mut above_charts = BTreeSet::new();
    let mut above_settled: Option<Vec<usize>> = None;
    let mut above_agree = true;
    let mut frontier_law = true;
    let mut frames_agree = true;
    let mut lineage_recorded = false;
    let mut restricted_moved = false;
    let mut restricted_proper = true;

    for horizon in 0..=covering + 2 {
        for order in WalkOrder::ALL {
            let section = dilate(
                &growth.complex,
                growth.root,
                Horizon::Steps(horizon),
                order,
            )
            .expect("a dilation from a founded focus resolves");
            let seen = rebase_invariants_on(
                &growth.complex,
                Some(section.support()),
                PivotRule::SmallestMagnitude,
            )
            .expect("a section reads");

            // is_covering() means nothing incident is outside the section -- the receiver covered
            // its own component. The right comparison is against what an UNBOUNDED horizon reaches
            // from the same focus, not against the whole complex, which would make the horizon
            // answer for connectivity as well.
            let covers = section.support == unbounded_support;
            if section.lineage.is_covering() != covers {
                frontier_law = false;
            }
            if !section.lineage.closure_added.is_empty() {
                lineage_recorded = true;
            }

            // Second frame, free: Euler against Smith normal form wherever Euler applies.
            if let Some((components, cycles)) =
                euler_reading(&growth.complex, Some(section.support())).expect("graph-like or not")
            {
                let betti = seen.betti_vector();
                if (betti[0], betti.get(1).copied().unwrap_or(0)) != (components, cycles) {
                    frames_agree = false;
                }
            }

            if horizon >= covering {
                above_charts.insert(section.lineage.reached.clone());
                match &above_settled {
                    None => above_settled = Some(seen.betti_vector()),
                    Some(first) => {
                        if *first != seen.betti_vector() {
                            above_agree = false;
                        }
                    }
                }
            } else {
                if section.support.len() >= unbounded_support.len() {
                    restricted_proper = false;
                }
                if seen.betti_vector() != whole.betti_vector() {
                    restricted_moved = true;
                }
                if order == WalkOrder::Breadth {
                    println!(
                        "  horizon {horizon:>2} RESTRICTS  cells {:>3}/{:<3}  betti {:?}  frontier {:>2}  closure {:>2}",
                        section.support.len(),
                        growth.complex.cells().len(),
                        seen.betti_vector(),
                        section.lineage.open_frontier.len(),
                        section.lineage.closure_added.len(),
                    );
                }
            }
        }
    }
    println!(
        "  horizon {:>2}+ GAUGE      cells {:>3}      betti {:?}  charts {}",
        covering,
        growth.complex.cells().len(),
        above_settled.clone().unwrap_or_default(),
        above_charts.len()
    );

    holds.push((
        "DILATION above the covering horizon does not move the invariants",
        above_agree,
        format!("covering {covering}, betti {:?}", above_settled.unwrap_or_default()),
    ));
    holds.push((
        "the walk order produced distinct charts above covering, so that is not a self-comparison",
        above_charts.len() > 1,
        format!("{} distinct charts", above_charts.len()),
    ));
    holds.push((
        "CONTROL below the covering horizon the section is PROPER",
        restricted_proper,
        "every sub-covering horizon held fewer cells than the whole".to_owned(),
    ));
    holds.push((
        "CONTROL below the covering horizon the invariants DO move, so the gauge is not vacuous",
        restricted_moved,
        "at least one restricting horizon returned different invariants".to_owned(),
    ));
    holds.push((
        "the open frontier is empty exactly when the receiver has covered its own component",
        frontier_law,
        "is_covering() agreed with the unbounded-horizon support at every horizon".to_owned(),
    ));
    holds.push((
        "LINEAGE the closure the walk pivoted off is recorded, not folded in",
        lineage_recorded,
        "at least one section reached a cell whose faces it had not walked".to_owned(),
    ));
    holds.push((
        "TWO FRAMES Euler-formula and Smith-normal-form agree on every section they both see",
        frames_agree,
        "independent implementations, never before compared in this tree".to_owned(),
    ));
}

fn main() {
    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=what survives every expansion schedule is the identity of the grown structure");
    println!("carrier=exact BigInt; Smith normal form; no float, no tolerance, nothing external");

    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    let tree = sweep("A grown tree (fallback= terminates every branch)", 3, 2, Closure::Tree);
    let cyclic = sweep("The same growth with its frontier closed into a rim", 3, 2, Closure::Rim);
    let wound = sweep("The same rim with a face attached to it TWICE", 3, 2, Closure::Wound);

    // -- the claim ---------------------------------------------------------------------------

    for (name, readings) in [("tree", &tree), ("cyclic", &cyclic), ("wound", &wound)] {
        let first = &readings[0];
        let agree = readings
            .iter()
            .all(|reading| invariants_agree(&first.invariants, &reading.invariants));
        holds.push((
            "the invariants are identical across every schedule",
            agree,
            format!(
                "{name}: {}",
                readings
                    .iter()
                    .map(|r| format!("{}={:?}", r.schedule.name(), r.invariants.betti_vector()))
                    .collect::<Vec<_>>()
                    .join("  ")
            ),
        ));

        let charts: BTreeSet<&str> = readings
            .iter()
            .map(|reading| reading.layout_digest.as_str())
            .collect();
        // EVERY schedule must produce its own chart. Accepting "more than one distinct layout"
        // would let two of the three coincide and still pass, which is what happened on the first
        // run: a uniform aperture made `LargestFirst` identical to `Breadth`, and the agreement it
        // then reported was an agreement between a reading and itself.
        holds.push((
            "every schedule produced a DISTINCT chart, so the agreement is not a self-comparison",
            charts.len() == readings.len(),
            format!("{name}: {} distinct layouts of {}", charts.len(), readings.len()),
        ));

        let same_size = readings.iter().all(|reading| reading.cells == first.cells);
        holds.push((
            "every schedule grew the same population, so nothing was lost",
            same_size,
            format!("{name}: {} cells", first.cells),
        ));

        let euler = readings.iter().all(|reading| {
            reading.invariants.euler_characteristic()
                == reading.invariants.cell_euler_characteristic()
        });
        holds.push((
            "Euler characteristic from Betti numbers equals it from cell counts",
            euler,
            format!("{name}: chi = {}", first.invariants.cell_euler_characteristic()),
        ));
    }

    // -- the controls, so no law here returns zero and calls that evidence --------------------

    let tree_loops: usize = tree[0].invariants.betti_vector().iter().skip(1).sum();
    holds.push((
        "CONTROL a tree carries no loop",
        tree_loops == 0,
        format!("tree loop total {tree_loops}"),
    ));

    let cyclic_loops: usize = cyclic[0].invariants.betti_vector().iter().skip(1).sum();
    holds.push((
        "CONTROL closing the rim MAKES loops, so the loop reading can be nonzero",
        cyclic_loops > 0,
        format!("cyclic loop total {cyclic_loops}"),
    ));

    holds.push((
        "CONTROL the tree and the cyclic growth are DISTINGUISHED by the invariant",
        !invariants_agree(&tree[0].invariants, &cyclic[0].invariants),
        format!(
            "tree {:?} vs cyclic {:?}",
            tree[0].invariants.betti_vector(),
            cyclic[0].invariants.betti_vector()
        ),
    ));

    holds.push((
        "CONTROL a tree and a rim carry no torsion",
        tree[0].invariants.total_torsion().is_empty()
            && cyclic[0].invariants.total_torsion().is_empty(),
        "no winding deposited".to_owned(),
    ));

    let wound_torsion = wound[0].invariants.total_torsion();
    holds.push((
        "CONTROL winding the face twice DEPOSITS torsion, so the torsion column can be nonzero",
        !wound_torsion.is_empty(),
        format!("{wound_torsion:?}"),
    ));

    let torsion_stable: BTreeSet<Vec<String>> = wound
        .iter()
        .map(|reading| {
            reading
                .invariants
                .total_torsion()
                .iter()
                .map(std::string::ToString::to_string)
                .collect()
        })
        .collect();
    holds.push((
        "the torsion itself does not move with the schedule",
        torsion_stable.len() == 1,
        format!("{torsion_stable:?}"),
    ));

    // A rational rank sees betti and destroys torsion; that is why this organ is integral.
    //
    // The exact claim, which the first run corrected: the face attaches to the rim with boundary
    // 2*(rim cycle). Over the rationals its image spans the same line as the rim itself, so it
    // removes EXACTLY ONE free loop — not all of them; the other rim loops are untouched. Over the
    // integers the image is the even multiples inside that line, so what stands where the free loop
    // was is Z/2. Asserting "kills the loop" was too strong and this control caught it.
    let wound_betti = wound[0].invariants.betti_vector();
    let cyclic_betti = cyclic[0].invariants.betti_vector();
    let one_loop_traded = match (cyclic_betti.get(1), wound_betti.get(1)) {
        (Some(before), Some(after)) => *before > 0 && *after + 1 == *before,
        _ => false,
    };
    holds.push((
        "the wound face trades EXACTLY ONE free loop for a Z/2 the rationals cannot see",
        one_loop_traded && wound_torsion == vec![num_bigint::BigInt::from(2)],
        format!("cyclic betti {cyclic_betti:?} -> wound betti {wound_betti:?} + {wound_torsion:?}"),
    ));

    dilation_sweep(&mut holds);

    // -- report ------------------------------------------------------------------------------

    println!("\n\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for (claim, held, evidence) in &holds {
        let occurrence = seen.entry(claim).or_default();
        *occurrence += 1;
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
        println!("FAILED — {failed} of {} declared controls did not hold", holds.len());
        std::process::exit(1);
    }
}
