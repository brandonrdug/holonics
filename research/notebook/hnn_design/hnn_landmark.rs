//! **The landmark tree on the standing real cut** (Decision 28, count-only; rebuild step 4, #73):
//! the notebook's receipt of `holonics::hnn::landmark::{choose_depths, prequential}`, a committed
//! command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
//! ```
//!
//! [definition] **What it runs** (the owner's header, `hnn::landmark`):
//! - the cut file and its manifest (`exterior::read_cut`): the cells and the held-out range;
//! - the receiver's grain `L_R` and the exterior chart's `|A|` from campaign 1's field declared at
//!   the cut's population (`FieldDeclaration::campaign_one`), so no grain is a literal here;
//! - each emission's depth sweep on the development cells only (`choose_depths`: `D = 1, 2, …`
//!   while the development code length decreases strictly), every depth tried printed with its
//!   development code length, and the choice's description bits `⌈log₂⌉` of the family tried;
//! - the prequential measurement at the chosen depths (`prequential`): every cell, development and
//!   held-out, scored at the current standing before its own deposit, then deposited, for the tree
//!   (`Digits`, its executed dyadic face and its ideal ℚ face beside it; `Cell`) and the online
//!   baselines (uniform, order-0 and order-1 KT, PPM-2) over the same cells in the same order.
//!
//! [established-bounded; measured] **The readout**: per population, each coder's bits a cell read
//! at the receiver's grain (`n + k/L_R + ε`, with `ε`'s exact enclosure); each strict ordering of a
//! tree against order-0, order-1 and PPM-2, decided by disjoint exact enclosures (the tree charged
//! its choice's description bits) or printed undecided with the overlap; the β chart's rebases and
//! bounds; the executed face's width and its largest per-cell residual against the ideal face;
//! and the wall time in integer milliseconds. The cut is private: only its scope and counts are
//! printed.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::hnn::landmark::{
    Coded, DepthSweep, Emission, LandmarkDeclaration, Landmarks, TreeRun, carrier_width,
    choose_depths, prequential,
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

fn sweep(label: &str, sweep: &DepthSweep, cells: u64, grain: u64) {
    println!("{label}: the development code length by depth ({cells} cells)");
    for (depth, bits) in &sweep.tried {
        println!(
            "  D = {depth}: {}; a cell {}",
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
    let rows: [(&str, &ExactInterval); 7] = [
        ("tree Digits (executed dyadic face)", &coded.digits),
        ("tree Digits (ideal ℚ face)", &coded.digits_ideal),
        ("tree Cell", &coded.cell),
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
    println!(
        "  the executed face's cost over the ideal: {}",
        difference(&coded.digits, &coded.digits_ideal, grain)
    );
}

fn orderings(label: &str, coded: &Coded, digits: u64, cell: u64, grain: u64) {
    println!(
        "{label}: each tree charged its depth choice's description bits (Digits {digits}, Cell {cell})"
    );
    let cells = coded.cells;
    for (tree, bits) in [
        ("tree Digits", charged(&coded.digits, digits)),
        ("tree Cell", charged(&coded.cell, cell)),
    ] {
        ordering(
            &format!("{tree} against online order-0 KT"),
            &bits,
            &coded.order_zero,
            cells,
            grain,
        );
        ordering(
            &format!("{tree} against online order-1 KT"),
            &bits,
            &coded.order_one,
            cells,
            grain,
        );
        ordering(
            &format!("{tree} against PPM order {PPM_ORDER}"),
            &bits,
            &coded.ppm,
            cells,
            grain,
        );
    }
}

fn tree_run(label: &str, run: &TreeRun, grain: u64) {
    let declaration = &run.declaration;
    let chart = &run.chart;
    let grain_unit = Rat::new(BigInt::from(1), BigInt::from(grain));
    println!(
        "{label}: D = {}, {} nodes founded; β chart W = {} bits: {} rebases, {} at the most-rebased node",
        declaration.depth, run.nodes, chart.width, chart.rebases, chart.node_rebases
    );
    println!(
        "  summed log₂ residual bound rebases · 2^(3−W) = {} bits; at the most-rebased node {} bits, {} 1/L_R",
        exact(&chart.residual_bound),
        exact(&chart.node_bound),
        if chart.node_bound < grain_unit {
            "below"
        } else {
            "NOT below"
        }
    );
    if declaration.emission == Emission::Digits {
        println!(
            "  executed face: M_f = {} bits a digit; the rule's per-cell bound {} bits, {} 1/L_R",
            run.face_bits,
            exact(&run.face_rule),
            if run.face_rule < grain_unit {
                "below"
            } else {
                "NOT below"
            }
        );
        println!(
            "  the largest certified per-cell residual against the ideal face: at most {} bits, {} the rule's bound",
            exact(&dyadic_ceiling(&run.largest_residual)),
            if run.largest_residual <= run.face_rule {
                "within"
            } else {
                "ABOVE"
            }
        );
    }
}

/// An exact upper bound of a nonnegative value on the dyadic grid `2^(−READING)`, `⌈v 2^R⌉ / 2^R`:
/// a long ratio printed short, never below it.
fn dyadic_ceiling(value: &Rat) -> Rat {
    let scale = BigInt::from(1) << READING;
    let scaled = value * Rat::from_integer(scale.clone());
    Rat::new(scaled.ceil().to_integer(), scale)
}

/// The dyadic grid of a printed upper bound: `2^(−32)`.
const READING: usize = 32;

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
    let declared = |emission| LandmarkDeclaration {
        alphabet,
        depth: 1,
        emission,
        forced: 0,
        population: count as u64,
        grain,
    };
    let (digits, cell) = (declared(Emission::Digits), declared(Emission::Cell));
    let tree = Landmarks::new(digits.clone()).expect("the Digits tree's declaration");
    let setup = setup.elapsed().as_millis();
    let development = (count - held.len()) as u64;
    println!("hnn_landmark: the landmark tree (Decision 28, count-only) over the cut file {path}");
    println!(
        "cut: {count} cells, |A| = {alphabet}; held out: cells {}..{} ({} cells, from the manifest); development: {development} cells",
        held.start,
        held.end,
        held.len()
    );
    println!(
        "declared: n* = {count}, L_R = {grain} (campaign 1's receiver); β carrier W = {} (least W with 2^W > 8 L_R n*); Digits: B = {} digits, M_f = {} bits a digit",
        carrier_width(count as u64, grain),
        tree.digits(),
        tree.face_bits()
    );
    println!("setup: {setup} ms wall");
    println!();

    let clock = Instant::now();
    let (digits_sweep, cell_sweep) = choose_depths(&cut, &digits, &cell).expect("the sweeps");
    let sweep_wall = clock.elapsed().as_millis();
    sweep("Digits", &digits_sweep, development, grain);
    sweep("Cell", &cell_sweep, development, grain);
    println!("the sweeps: {sweep_wall} ms wall");
    println!();

    let clock = Instant::now();
    let run = prequential(
        &cut,
        &LandmarkDeclaration {
            depth: digits_sweep.chosen,
            ..digits
        },
        &LandmarkDeclaration {
            depth: cell_sweep.chosen,
            ..cell
        },
    )
    .expect("the prequential measurement");
    let run_wall = clock.elapsed().as_millis();
    let chosen_bits = |sweep: &DepthSweep| {
        sweep
            .tried
            .iter()
            .find(|(depth, _)| *depth == sweep.chosen)
            .map(|(_, bits)| bits.clone())
            .expect("the chosen depth was tried")
    };
    println!(
        "check: the run's development code lengths are the sweeps' at the chosen depths: Digits {}, Cell {}",
        run.development.digits == chosen_bits(&digits_sweep),
        run.development.cell == chosen_bits(&cell_sweep)
    );
    println!();
    population("held out", &run.held_out, grain);
    println!();
    population("development", &run.development, grain);
    println!();
    orderings(
        "held out, the orderings",
        &run.held_out,
        digits_sweep.description_bits,
        cell_sweep.description_bits,
        grain,
    );
    println!();
    orderings(
        "development, the orderings",
        &run.development,
        digits_sweep.description_bits,
        cell_sweep.description_bits,
        grain,
    );
    println!();
    tree_run("tree Digits", &run.digits, grain);
    tree_run("tree Cell", &run.cell, grain);
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; the sweeps {sweep_wall} ms; the prequential run {run_wall} ms"
    );
}
