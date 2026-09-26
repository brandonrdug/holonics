//! **The landmark tree on the standing real cut, executed on its declared dyadic lattice**
//! (Decision 28, count-only; rebuild step 4, #73): the notebook's receipt of
//! `holonics::hnn::landmark::{choose_depth, prequential, oracle_cost}`, a committed command run once
//! in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
//! ```
//!
//! [definition] **What it runs** (the owner's header, `hnn::landmark`):
//! - the cut file and its manifest (`exterior::read_cut`): the cells and the held-out range;
//! - the receiver's grain `L_R` and the exterior chart's `|A|` from campaign 1's field declared at
//!   the cut's population (`FieldDeclaration::campaign_one`), so no grain is a literal here;
//! - the depth sweep on the development cells only (`choose_depth`: `D = 1, 2, …` while the
//!   development code length decreases strictly), every depth tried printed with its development
//!   code length and its derived widths, and the choice's description bits `⌈log₂⌉` of the family;
//! - the prequential measurement at the chosen depth (`prequential`): every cell, development and
//!   held-out, scored at the current standing before its own deposit, then deposited, for the tree
//!   (its executed lattice face) and the online baselines (uniform, order-0 and order-1 KT, PPM-2)
//!   over the same cells in the same order;
//! - the hot path alone: the passage through the tree without any reading, one all-class face read
//!   at the final standing, the held-out addresses' face reads at that standing, and a clone of the
//!   final tree;
//! - the executed face's cost against the reference oracle (`oracle_cost`): the ideal tree
//!   weighting in ℚ at the reference width `W_o`, cell by cell, never on the hot path.
//!
//! [established-bounded; measured] **The readout**: per population, each coder's bits a cell read
//! at the receiver's grain (`n + k/L_R + ε`, with `ε`'s exact enclosure); each strict ordering of the
//! tree against order-0, order-1 and PPM-2, decided by disjoint exact enclosures (the tree charged
//! its choice's description bits) or printed undecided with the overlap; the derived widths, the β
//! chart's rebases and drift, the rule's bound and the largest certified per-cell residual; the
//! executed face's cost over the oracle; and wall times in integer milliseconds or microseconds,
//! averages as a quotient with its remainder. The cut is private: only its scope and counts are
//! printed.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::hnn::landmark::{
    Coded, DepthSweep, IdealLandmarks, LandmarkDeclaration, Landmarks, OracleCost, TreeRun, Widths,
    address, choose_depth, code_length, oracle_cost, prequential,
};
use holonics::hnn::ratio::interval_sum;
use holonics::hnn::reference::PPM_ORDER;
use holonics::hnn::{Cut, Field, FieldDeclaration};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;

use exterior::{against, difference, enclosure, exact, per, read_cut, receiver_grain};

/// The tree's code length charged its depth choice's description bits.
fn charged(bits: &ExactInterval, description: u64) -> ExactInterval {
    interval_sum(
        bits,
        &ExactInterval::point(Rat::from_integer(BigInt::from(description))),
    )
    .expect("an enclosure")
}

/// **A strict ordering**, `a` against `b`: decided by disjoint exact enclosures, with the exact
/// difference in bits and a cell; or undecided, with the overlap.
fn ordering(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64, grain: u64) {
    let side = against(a, b);
    println!("  {label}: {side}");
    if a.upper < b.lower || a.lower > b.upper {
        let delta = ExactInterval {
            lower: &a.lower - &b.upper,
            upper: &a.upper - &b.lower,
        };
        println!("    difference {}", difference(a, b, grain));
        println!("    a cell: {}", per(&delta, cells, grain));
    } else {
        let lower = if a.lower > b.lower {
            &a.lower
        } else {
            &b.lower
        };
        let upper = if a.upper < b.upper {
            &a.upper
        } else {
            &b.upper
        };
        println!("    overlap [{}, {}] bits", exact(lower), exact(upper));
    }
}

fn widths(widths: &Widths) -> String {
    format!(
        "B = {}, M_p = {}, W = {}, C = {}",
        widths.digits, widths.face, widths.carrier, widths.certificate
    )
}

fn sweep(sweep: &DepthSweep, declared: &LandmarkDeclaration, cells: u64, grain: u64) {
    println!("the depth sweep: the development code length by depth ({cells} cells)");
    for (depth, bits) in &sweep.tried {
        let tree = Landmarks::new(LandmarkDeclaration {
            depth: *depth,
            ..declared.clone()
        })
        .expect("a declared depth");
        println!(
            "  D = {depth} ({}): {}; a cell {}",
            widths(&tree.widths()),
            enclosure(bits, grain),
            per(bits, cells, grain)
        );
    }
    println!(
        "  chosen D = {} of {} tried; description bits ⌈log₂ {}⌉ = {}",
        sweep.chosen,
        sweep.tried.len(),
        sweep.tried.len(),
        sweep.description_bits
    );
}

fn population(label: &str, coded: &Coded, grain: u64) {
    let cells = coded.cells;
    println!("{label} ({cells} cells), bits a cell at L_R = {grain}:");
    let rows: [(&str, &ExactInterval); 5] = [
        ("tree (executed lattice face)", &coded.tree),
        ("uniform", &coded.uniform),
        ("online order-0 KT", &coded.order_zero),
        ("online order-1 KT", &coded.order_one),
        ("PPM order 2, escape C", &coded.ppm),
    ];
    for (name, bits) in rows {
        println!("  {name}: {}", per(bits, cells, grain));
        println!(
            "    total exact [{}, {}] bits",
            exact(&bits.lower),
            exact(&bits.upper)
        );
    }
}

fn orderings(label: &str, coded: &Coded, description: u64, grain: u64) {
    println!("{label}: the tree charged its depth choice's {description} description bits");
    let cells = coded.cells;
    let bits = charged(&coded.tree, description);
    ordering(
        "tree against online order-0 KT",
        &bits,
        &coded.order_zero,
        cells,
        grain,
    );
    ordering(
        "tree against online order-1 KT",
        &bits,
        &coded.order_one,
        cells,
        grain,
    );
    ordering(
        &format!("tree against PPM order {PPM_ORDER}"),
        &bits,
        &coded.ppm,
        cells,
        grain,
    );
}

fn below_grain(value: &Rat, grain: u64) -> &'static str {
    if value < &Rat::new(BigInt::from(1), BigInt::from(grain)) {
        "below"
    } else {
        "NOT below"
    }
}

fn tree_run(run: &TreeRun, grain: u64) {
    let chart = &run.chart;
    println!(
        "the tree: D = {}, {}; {} nodes founded, {} stored bits",
        run.declaration.depth,
        widths(&run.widths),
        run.nodes,
        run.bits
    );
    println!(
        "  β chart: {} rebases, {} at the most-rebased node; the largest node drift certificate |log₂ β̂ − log₂ β| ≤ {} bits",
        chart.rebases,
        chart.node_rebases,
        exact(&dyadic_ceiling(&chart.drift))
    );
    println!(
        "  the rule's bound a cell: {} bits, {} 1/L_R",
        exact(&dyadic_ceiling(&run.face_rule)),
        below_grain(&run.face_rule, grain)
    );
    println!(
        "  the largest certified per-cell residual: at most {} bits, {} the rule's bound",
        exact(&dyadic_ceiling(&run.largest_residual)),
        if run.largest_residual <= run.face_rule {
            "within"
        } else {
            "ABOVE"
        }
    );
}

fn oracle(cost: &OracleCost, cells: [u64; 2], grain: u64) {
    println!(
        "the reference oracle: β at W_o = {} bits ({} rebases), its own rule a cell {} bits",
        cost.reference_width,
        cost.rebases,
        exact(&dyadic_ceiling(&cost.drift_rule))
    );
    for (part, label) in ["development", "held out"].iter().enumerate() {
        let delta = ExactInterval {
            lower: &cost.executed[part].lower - &cost.ideal[part].upper,
            upper: &cost.executed[part].upper - &cost.ideal[part].lower,
        };
        println!(
            "  {label} ({} cells): the ideal face {}",
            cells[part],
            per(&cost.ideal[part], cells[part], grain)
        );
        println!(
            "    the executed face's cost over the ideal: {}",
            difference(&cost.executed[part], &cost.ideal[part], grain)
        );
        println!("    a cell: {}", per(&delta, cells[part], grain));
    }
    println!(
        "  the largest observed per-cell deviation |log₂(q̂/q)|: at most {} bits; the largest certificate {} bits; every cell within its certificate: {}",
        exact(&dyadic_ceiling(&cost.largest_deviation)),
        exact(&dyadic_ceiling(&cost.largest_certificate)),
        cost.certified
    );
}

/// An exact upper bound of a nonnegative value on the dyadic grid `2^(−READING)`, `⌈v 2^R⌉ / 2^R`:
/// a long ratio printed short, never below it.
fn dyadic_ceiling(value: &Rat) -> Rat {
    let scale = BigInt::from(1) << READING;
    let scaled = value * Rat::from_integer(scale.clone());
    Rat::new(scaled.ceil().to_integer(), scale)
}

/// The dyadic grid of a printed upper bound: `2^(−48)`.
const READING: usize = 48;

/// A total of microseconds over `count` reads: the integer quotient with its remainder.
fn average(total: u128, count: u128) -> String {
    format!(
        "{} µs in all, {} rem {} over {count} µs a read",
        total,
        total / count,
        total % count
    )
}

/// **The hot path alone** at the chosen depth: the passage without any reading, one all-class
/// face read at the final standing, the held-out addresses' face reads there, and a clone.
fn hot_path(cut: &Cut, declared: &LandmarkDeclaration, held: &std::ops::Range<usize>) {
    let mut tree = Landmarks::new(declared.clone()).expect("the chosen declaration");
    let clock = Instant::now();
    for (position, &cell) in cut.cells.iter().enumerate() {
        tree.receive(&address(&cut.cells, position, declared.depth), cell)
            .expect("a cell within the declaration");
    }
    let passage = clock.elapsed().as_millis();
    let mut read = Landmarks::new(declared.clone()).expect("the chosen declaration");
    let mut sum = ExactInterval::point(Rat::from_integer(BigInt::from(0)));
    let clock = Instant::now();
    for (position, &cell) in cut.cells.iter().enumerate() {
        let reading = read
            .receive(&address(&cut.cells, position, declared.depth), cell)
            .expect("a cell within the declaration");
        sum = interval_sum(
            &sum,
            &code_length(&reading.executed).expect("a code length"),
        )
        .expect("an enclosure");
    }
    let scored = clock.elapsed().as_millis();
    let next = address(&cut.cells, cut.cells.len(), declared.depth);
    let clock = Instant::now();
    let face = tree.face(&next, declared.grain).expect("a face");
    let one = clock.elapsed().as_micros();
    let total: Rat = face.probabilities.iter().cloned().sum();
    let clock = Instant::now();
    for position in held.clone() {
        tree.face(
            &address(&cut.cells, position, declared.depth),
            declared.grain,
        )
        .expect("a face");
    }
    let reads = clock.elapsed().as_micros();
    let clock = Instant::now();
    let copy = tree.clone();
    let cloned = clock.elapsed().as_micros();
    println!(
        "the hot path at D = {}: the passage of {} cells (receive only) {} ms; one all-class face read ({} classes) at the final standing {} µs, the faces summing to {}",
        declared.depth,
        cut.cells.len(),
        passage,
        face.probabilities.len(),
        one,
        exact(&total)
    );
    println!(
        "  the tree's own prequential run (receive, code length and sum of every cell): {scored} ms, {} bits in all",
        exact(&sum.upper)
    );
    println!(
        "  the held-out addresses' all-class face reads at the final standing: {}",
        average(reads, held.len() as u128)
    );
    println!(
        "  a clone of the final tree ({} nodes): {} µs; equal: {}",
        tree.nodes(),
        cloned,
        copy == tree
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let path = match arguments.as_slice() {
        [key, value] if key == "cut-file" => value.clone(),
        _ => {
            println!("usage: hnn_landmark cut-file <path>");
            return;
        }
    };
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(&path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let cut = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
    };
    let setup = setup.elapsed().as_millis();
    let development = (count - held.len()) as u64;
    println!(
        "hnn_landmark: the landmark tree on its declared lattice (Decision 28, count-only) over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}; held out: cells {}..{} ({} cells, from the manifest); development: {development} cells",
        held.start,
        held.end,
        held.len()
    );
    println!(
        "declared: n* = {count}, L_R = {grain} (campaign 1's receiver); per depth D the widths M_p = ⌈log₂(3 B L_R (2n* + 2)(n* D² + 2D + 1))⌉, W = ⌈log₂(12 B L_R n* D²)⌉, C = M_p + W"
    );
    println!("setup: {setup} ms wall");
    println!();

    let clock = Instant::now();
    let chosen = choose_depth(&cut, &declared).expect("the sweep");
    let sweep_wall = clock.elapsed().as_millis();
    sweep(&chosen, &declared, development, grain);
    println!("the sweep: {sweep_wall} ms wall");
    println!();

    let at = LandmarkDeclaration {
        depth: chosen.chosen,
        ..declared.clone()
    };
    let clock = Instant::now();
    let run = prequential(&cut, &at).expect("the prequential measurement");
    let run_wall = clock.elapsed().as_millis();
    let chosen_bits = chosen
        .tried
        .iter()
        .find(|(depth, _)| *depth == chosen.chosen)
        .map(|(_, bits)| bits.clone())
        .expect("the chosen depth was tried");
    println!(
        "check: the run's development code length is the sweep's at the chosen depth: {}",
        run.development.tree == chosen_bits
    );
    println!();
    population("held out", &run.held_out, grain);
    println!();
    population("development", &run.development, grain);
    println!();
    orderings(
        "held out, the orderings",
        &run.held_out,
        chosen.description_bits,
        grain,
    );
    println!();
    orderings(
        "development, the orderings",
        &run.development,
        chosen.description_bits,
        grain,
    );
    println!();
    tree_run(&run.run, grain);
    println!();
    hot_path(&cut, &at, &held);
    println!();

    let clock = Instant::now();
    let cost = oracle_cost(&cut, &at).expect("the oracle's run");
    let oracle_wall = clock.elapsed().as_millis();
    println!(
        "the oracle's reference width at D = {}: {}",
        at.depth,
        IdealLandmarks::reference_width(&at)
    );
    oracle(&cost, [development, held.len() as u64], grain);
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; the sweep {sweep_wall} ms; the prequential run {run_wall} ms; the oracle's run {oracle_wall} ms"
    );
}
