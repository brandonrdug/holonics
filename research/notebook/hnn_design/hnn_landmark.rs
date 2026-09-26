//! **The landmark tree on the standing real cut, executed on its declared dyadic lattice**
//! (Decision 28, count-only; rebuild step 4, #73): the notebook's receipt of
//! `holonics::hnn::landmark::{choose_depth, prequential, oracle_cost}`, a committed command run once
//! in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters contacts
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior
//! ```
//!
//! [definition; agent-inferred] **The stop-prior decision** (`prior`; Decision 32): on the
//! **development cells only** (the manifest's held-out range is cut away before the sweep reads
//! anything), the cell-only tree under every law of the declared family
//! (`hnn::landmark::prior_family`: the global dyadic ladder `w = 1 − 2^(−j)`, `j = 1, …, J`, then the
//! per-depth pairs `(j_root, j_below)`, `j_root ≠ j_below`; `J = ⌈log₂(n* B)⌉`,
//! `hnn::landmark::ladder_top`), each law with its own depth sweep (`choose_depth`) and charged
//! `⌈log₂⌉` of its depths tried, the choice charged `⌈log₂⌉` of the laws tried
//! (`hnn::landmark::choose_prior`):
//! - each law's development code length and its difference from the `½` tree (Decision 28's law),
//!   uncharged and charged, with its sign when decided by disjoint enclosures;
//! - the choice: the least charged law when it lies strictly below the `½` tree, the `½` tree
//!   otherwise, and whether it lies strictly below every other law;
//! - **where campaign 2's constant-slot controls found their bits** (development only; it chooses
//!   nothing): every law's development code length split by dyadic cell (the digit trees), each
//!   digit's executed face read by `Landmarks::opened` before its deposit. The controls are the
//!   cell tree joined, per dyadic cell, with the per-depth law `(1, r + 1)` (the test
//!   `landmark_constant_slots_are_the_per_depth_prior`), and a join codes each dyadic cell within
//!   `[min, min + 1]` of its two branches (Lean `sequential_mixture_bounds`): so it prints, per law,
//!   `Σ_h min(L_(½,h), L_(law,h)) − L_½` and the dyadic cells where the law is decided below `½`,
//!   and the least law per dyadic cell over the whole family, `Σ_h min_law L_(law,h) − L_½`;
//! - **then the held-out pass, once, for the chosen law** at its chosen depth (`prequential` over
//!   the whole cut, every cell scored before its own deposit): the chosen tree against online
//!   order-0, order-1, PPM-2 and the `½` tree (`tree_prequential` at its own chosen depth), each in
//!   all and a cell at the grain, the chosen tree charged its whole description (the laws' and its
//!   depths' `⌈log₂⌉`) and the `½` tree its depths' (Decision 28's receipt); and the wall times.
//!
//! [definition; agent-inferred] **The development harness** (`letters`; campaign 2's receiving
//! letters, Decision 31): on the **development cells only** (the manifest's held-out range is cut
//! away before anything is read, and no held-out cell reaches any choice or reading), the tree
//! addressed by typed bundles (each tick's cell with its declared rings' phase classes, read by the
//! clock-only replay `hnn::receiving::clock_letters`, the resident's clock law with its key
//! location and re-keying at each carry-out, without the wave) against the tree with cells only:
//! - the families tried: every nonempty set of campaign 1's four rings at one declared grain, the
//!   ring's period `d_g` (its own port chart, an empty fibre) or `2` (the half of the rotor's cycle
//!   its clock phase is in; not the parametron's half-turn sheets, which no letter reads), so
//!   `2 (2^4 − 1) = 30` families; each is declared (`LetterFamily`) and read with its own depth
//!   sweep (`choose_depth`), prequentially, every cell scored before its own deposit;
//! - each family's description charge: `⌈log₂(N + 1)⌉` bits for the family chosen among the `N`
//!   declared and the cell-only one, plus `⌈log₂⌉` of its depths tried; a slot of one letter is never
//!   declared (`LetterFamily::new` refuses it: it carries nothing), so nothing is charged for one;
//! - `Δ_tree = L_(tree+letters) − L_(tree, cells) + description`, an exact enclosure, and its
//!   sign when decided;
//! - with `contacts`, the contact families (every set of the field's contacts whose code fits 32
//!   bits, each contact's letter its owner's reading, `hnn::contact::ContactReading`), their site
//!   kinds read from the exposure's development part on the host (its deadline the development's
//!   last window: only its constitution curve's contact site readings are read);
//! - the constant-slot controls (`LetterFamily::constant_control`: `r` slots of one letter each,
//!   never declared and never charged), whose difference from the cell-only tree is the enlarged
//!   tree's own reweighting, and each family's
//!   `Δ_letters = L_(tree+letters) − L_(control, r slots) + description`; the family chosen is the
//!   least charged one with both `Δ_tree < 0` and `Δ_letters < 0` decided, the cell-only tree
//!   otherwise;
//! - the passage bound of every enlarged tree, family or control (Lean
//!   `HNN/LandmarkAddress.cell_only_dominance_with_feature_charge`, `passage_join_bound`): at its
//!   chosen depth `D` its executed code is at most the cell-only tree's at `D` plus one bit a dyadic
//!   cell the development cells opened, plus both trees' certified drift (each tree's a-priori rule
//!   a cell, `Landmarks::face_rule`, times the cells), checked by exact enclosures;
//! - the widths each family derives (its path depth `P = D + D(1 + r) + 2`) and its wall time.
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

use rayon::prelude::*;

use holonics::hnn::landmark::{
    Coded, DepthSweep, Feature, IdealLandmarks, LandmarkDeclaration, Landmarks, Letter,
    LetterFamily, OracleCost, PriorSweep, StopPrior, TreeRun, Widths, address, cell_letters,
    choose_depth, choose_prior, code_length, development, ladder_top, odometer_digits, oracle_cost,
    prequential, prior_family, tree_prequential,
};
use holonics::hnn::ratio::interval_sum;
use holonics::hnn::receiving::clock_letters;
use holonics::hnn::reference::PPM_ORDER;
use holonics::hnn::{Cut, Field, FieldDeclaration, Reference};
use holonics::navigator::trace::SiteKind;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use std::collections::BTreeSet;

use exterior::{against, difference, enclosure, exact, per, read_cut, reading_of, receiver_grain};

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

/// One family's development sweep: its declaration's features, its sweep, the chosen depth's code
/// length, its description bits, and its wall time.
struct FamilyRun {
    name: String,
    family: LetterFamily,
    sweep: DepthSweep,
    bits: ExactInterval,
    description: u64,
    wall: u128,
    /// The distinct feature codes the family read over the development passage.
    distinct: usize,
}

/// The sign of an enclosure, when decided.
fn decided(delta: &ExactInterval) -> &'static str {
    if delta.upper < Rat::from_integer(BigInt::from(0)) {
        "< 0 (decided)"
    } else if delta.lower > Rat::from_integer(BigInt::from(0)) {
        "> 0 (decided)"
    } else {
        "undecided"
    }
}

fn chosen_bits(sweep: &DepthSweep) -> ExactInterval {
    sweep
        .tried
        .iter()
        .find(|(depth, _)| *depth == sweep.chosen)
        .map(|(_, bits)| bits.clone())
        .expect("the chosen depth was tried")
}

/// **The site kinds of the development pass** (module header, "The contact letters"): the exposure's
/// development part on the host (the reference, its deadline the development's last window, so no
/// held-out cell is read), whose constitution curve carries each commit's contact site readings;
/// the kinds the register holds at cell `i` are the commit after the deposits of the windows
/// before `i`'s (the register refreshes after each ingest). Only the kinds are read of it.
fn development_kinds(field: &Field, full: &Cut, development: usize) -> Vec<Vec<SiteKind>> {
    let aperture = field.receivers()[0].aperture;
    let windows = (development / aperture) as u64;
    let clock = Instant::now();
    let exposure = Reference::campaign_one()
        .with_deadline(windows)
        .expose(field, full)
        .expect("the exposure's development pass");
    let wall = clock.elapsed().as_millis();
    let stopped = exposure
        .deadline
        .expect("the development pass ends at its deadline");
    assert!(
        stopped as usize <= development,
        "the development pass read no held-out cell"
    );
    let curve = &exposure.constitution_curve;
    println!(
        "the site kinds: the exposure's development part on the host, {} windows, stopped at cell {stopped} (the held-out range opens at {development}); {} commits; budget stop: {}; {wall} ms wall",
        exposure.compares,
        curve.len(),
        if exposure.stop.is_some() {
            "yes"
        } else {
            "none"
        }
    );
    for contact in 0..field.contacts().len() {
        let mut seen: Vec<(String, usize)> = Vec::new();
        for point in curve {
            let reading = &point.contacts[contact];
            let label = format!(
                "{:?} (rotations {}, nulls {}, boosts {})",
                reading.kind, reading.census.rotation, reading.census.null, reading.census.boost
            );
            match seen.iter_mut().find(|(seen, _)| *seen == label) {
                Some((_, count)) => *count += 1,
                None => seen.push((label, 1)),
            }
        }
        let (from, to) = field.contact(contact).ends();
        println!(
            "  contact {contact} ({from} → {to}): {}",
            seen.iter()
                .map(|(label, count)| format!("{label} at {count} commits"))
                .collect::<Vec<_>>()
                .join("; ")
        );
    }
    (0..development)
        .map(|cell| {
            let point = &curve[(cell / aperture).min(curve.len() - 1)];
            point.contacts.iter().map(|reading| reading.kind).collect()
        })
        .collect()
}

/// **The development harness** (module header, "The development harness").
fn letters_harness(path: &str, contacts: bool) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let full = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    println!(
        "hnn_landmark letters: the development harness (campaign 2's receiving letters, Decision 31) over the cut file {path}"
    );
    // The contact letters' site kinds need the learned constitution: the exposure's development
    // part, stopped before the held-out range.
    let kinds = if contacts {
        development_kinds(&field, &full, held.start)
    } else {
        Vec::new()
    };
    // The development cells alone: nothing after this line reads a held-out cell.
    let cut = Cut {
        cells: development(&full),
        held_out: Vec::new(),
    };
    drop(full);
    let cells = cut.cells.len() as u64;
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: holonics::hnn::StopPrior::half(),
    };
    println!(
        "development: {cells} cells (the manifest's held-out range {}..{} is cut away before any reading); |A| = {alphabet}, n* = {count}, L_R = {grain}",
        held.start, held.end
    );
    println!("setup: {} ms wall", setup.elapsed().as_millis());
    println!();

    let clock = Instant::now();
    let letters = cell_letters(&cut.cells);
    let cell_sweep = choose_depth(&cut, &letters, &declared).expect("the cell-only sweep");
    let cell_wall = clock.elapsed().as_millis();
    sweep(&cell_sweep, &declared, cells, grain);
    let cell_bits = chosen_bits(&cell_sweep);
    println!("the cell-only tree: {cell_wall} ms wall");
    println!();

    let rings = field.rings();
    let mut families: Vec<(String, LetterFamily)> = Vec::new();
    for sheet in [false, true] {
        for subset in 1u32..(1 << rings.len()) {
            let chosen: Vec<usize> = (0..rings.len()).filter(|g| subset >> g & 1 == 1).collect();
            let features = chosen
                .iter()
                .map(|&ring| Feature::Phase {
                    ring,
                    grain: if sheet { 2 } else { rings[ring].period() },
                })
                .collect();
            let name = chosen
                .iter()
                .map(|&ring| {
                    format!(
                        "ring {ring} (d = {}) at grain {}",
                        rings[ring].period(),
                        if sheet { 2 } else { rings[ring].period() }
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            families.push((
                name,
                LetterFamily::new(features).expect("a declared family"),
            ));
        }
    }
    if contacts {
        // Every set of contacts whose letters' code fits the bundle's 32 bits, each contact's
        // letter its lock address at its derived bound times its site kind.
        let count = field.contacts().len();
        for subset in 1u32..(1 << count) {
            let chosen: Vec<usize> = (0..count).filter(|a| subset >> a & 1 == 1).collect();
            let features: Vec<Feature> = chosen
                .iter()
                .map(|&contact| Feature::contact(&field, contact))
                .collect();
            let name = chosen
                .iter()
                .map(|&contact| {
                    let (from, to) = field.contact(contact).ends();
                    let Feature::Contact { bound, .. } = Feature::contact(&field, contact) else {
                        unreachable!("a contact feature")
                    };
                    format!(
                        "contact {contact} ({from} → {to}, P = {}, Q = {})",
                        bound.numerator, bound.denominator
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            match LetterFamily::new(features) {
                Ok(family) => families.push((name, family)),
                Err(refusal) => println!("not declared: {name}: {refusal}"),
            }
        }
    }
    // ⌈log₂(N + 1)⌉: the family chosen among the N tried and the cell-only tree.
    let choice_bits = u64::from(64 - (families.len() as u64).leading_zeros());
    println!(
        "families tried: {}; the family's description: ⌈log₂({} + 1)⌉ = {choice_bits} bits, plus ⌈log₂⌉ of its depths tried",
        families.len(),
        families.len()
    );
    let run_family = |name: String, family: LetterFamily, charge: u64| -> FamilyRun {
        let clock = Instant::now();
        let letters =
            clock_letters(&field, &family, &cut.cells, &kinds).expect("the passage's letters");
        let distinct = letters
            .iter()
            .filter_map(|letter| match letter {
                Letter::Bundle(bundle) => Some(bundle.features),
                _ => None,
            })
            .collect::<std::collections::BTreeSet<u32>>()
            .len();
        let at = LandmarkDeclaration {
            family: family.clone(),
            ..declared.clone()
        };
        let family_sweep = choose_depth(&cut, &letters, &at).expect("a family's sweep");
        let wall = clock.elapsed().as_millis();
        let bits = chosen_bits(&family_sweep);
        let description = charge + family_sweep.description_bits;
        FamilyRun {
            name,
            family,
            sweep: family_sweep,
            bits,
            description,
            wall,
            distinct,
        }
    };
    let runs: Vec<FamilyRun> = families
        .into_iter()
        .map(|(name, family)| run_family(name, family, choice_bits))
        .collect();
    // [agent-inferred] **The constant-slot controls**: `r` slots that read one letter at every tick
    // (a ring's phase class at grain 1). They carry no information, so their code length against
    // the cell-only tree is the enlarged tree's own reweighting (`r` constant slots after each cell
    // make the stop weight at every cell depth past the first `1 − 2^(−(r+1))` instead of `1/2`,
    // joined with the cell tree), not a letter's; a family's letters are credited only with what
    // they code below the control of its slots,
    // `Δ_letters = L_(tree+letters) − L_(control, r slots) + description`.
    let widest = runs.iter().map(|run| run.family.slots()).max().unwrap_or(0);
    let controls: Vec<FamilyRun> = (1..=widest)
        .map(|slots| {
            run_family(
                format!("the constant control of {slots} slots"),
                LetterFamily::constant_control(slots),
                0,
            )
        })
        .collect();
    println!();
    println!(
        "the constant-slot controls against the cell-only tree (no letter information: the enlarged tree's reweighting, uncharged):"
    );
    for control in &controls {
        let delta = ExactInterval {
            lower: &control.bits.lower - &cell_bits.upper,
            upper: &control.bits.upper - &cell_bits.lower,
        };
        println!(
            "  {} ({} distinct letters): chosen D = {}; L_control − L_(tree, cells): {}",
            control.name,
            control.distinct,
            control.sweep.chosen,
            enclosure(&delta, grain)
        );
    }
    // The passage bound (Lean `cell_only_dominance_with_feature_charge`): at its chosen depth an
    // enlarged tree codes within one bit a dyadic cell opened of the cell-only tree at that depth,
    // plus both trees' certified drift (the a-priori rule a cell times the cells).
    let opened: BTreeSet<usize> = cut
        .cells
        .iter()
        .flat_map(|&class| declared.emitted(class).into_iter().map(|(h, _)| h))
        .collect();
    let opened = opened.len() as u64;
    let cell_bits_at = |depth: usize| -> ExactInterval {
        cell_sweep
            .tried
            .iter()
            .find(|(tried, _)| *tried == depth)
            .map(|(_, bits)| bits.clone())
            .unwrap_or_else(|| {
                prequential(
                    &cut,
                    &letters,
                    &LandmarkDeclaration {
                        depth,
                        ..declared.clone()
                    },
                )
                .expect("the cell-only tree at a family's depth")
                .development
                .tree
            })
    };
    let rule = |declaration: LandmarkDeclaration| -> Rat {
        Landmarks::new(declaration)
            .expect("a declared tree")
            .face_rule()
            * Rat::from_integer(BigInt::from(cells))
    };
    println!();
    println!(
        "the passage bound (Lean cell_only_dominance_with_feature_charge): L_(tree+letters) ≤ L_(tree, cells) at the same depth + {opened} (one bit a dyadic cell the development cells opened) + ρ_letters + ρ_cells (the rule a cell times {cells} cells):"
    );
    let mut bound_holds = true;
    for run in runs.iter().chain(&controls) {
        let depth = run.sweep.chosen;
        let cells_at = cell_bits_at(depth);
        let drift = rule(LandmarkDeclaration {
            depth,
            family: run.family.clone(),
            ..declared.clone()
        }) + rule(LandmarkDeclaration {
            depth,
            ..declared.clone()
        });
        let ceiling = &cells_at.lower + Rat::from_integer(BigInt::from(opened)) + &drift;
        let holds = run.bits.upper <= ceiling;
        bound_holds &= holds;
        let margin = ExactInterval {
            lower: &ceiling - &run.bits.upper,
            upper: &ceiling - &run.bits.upper,
        };
        println!(
            "  {} at D = {depth}: {}; margin (ceiling − L_(tree+letters).upper) {}",
            run.name,
            if holds { "holds" } else { "VIOLATED" },
            enclosure(&margin, grain)
        );
    }
    println!("  every enlarged tree within its passage bound: {bound_holds}");
    println!();
    println!(
        "each family against the cell-only tree at its chosen depth, Δ_tree = L_(tree+letters) − L_(tree, cells) + description:"
    );
    for run in &runs {
        let tried: Vec<String> = run
            .sweep
            .tried
            .iter()
            .map(|(depth, bits)| format!("D = {depth}: {}", per(bits, cells, grain)))
            .collect();
        let charged = charged(&run.bits, run.description);
        let delta = ExactInterval {
            lower: &charged.lower - &cell_bits.upper,
            upper: &charged.upper - &cell_bits.lower,
        };
        let sign = if delta.upper < Rat::from_integer(BigInt::from(0)) {
            "Δ_tree < 0 (decided)"
        } else if delta.lower > Rat::from_integer(BigInt::from(0)) {
            "Δ_tree > 0 (decided)"
        } else {
            "Δ_tree undecided"
        };
        let tree = Landmarks::new(LandmarkDeclaration {
            depth: run.sweep.chosen,
            family: run.family.clone(),
            ..declared.clone()
        })
        .expect("the chosen declaration");
        println!(
            "  {} ({} slots, {} bundle codes):",
            run.name,
            run.family.slots(),
            run.family.bundle_codes(alphabet)
        );
        println!("    sweep {}", tried.join("; "));
        println!(
            "    chosen D = {} ({}, P = {}); description {} bits; {} ms wall",
            run.sweep.chosen,
            widths(&tree.widths()),
            tree.declaration().path_depth(),
            run.description,
            run.wall
        );
        let uncharged = ExactInterval {
            lower: &run.bits.lower - &cell_bits.upper,
            upper: &run.bits.upper - &cell_bits.lower,
        };
        println!(
            "    uncharged L_(tree+letters) − L_(tree, cells): {}",
            enclosure(&uncharged, grain)
        );
        println!("    Δ_tree {}: {}", sign, enclosure(&delta, grain));
        let control = &controls[run.family.slots() - 1];
        let against = ExactInterval {
            lower: &charged.lower - &control.bits.upper,
            upper: &charged.upper - &control.bits.lower,
        };
        println!(
            "    distinct feature codes read: {}; Δ_letters (against the constant control of {} slots, charged) {}: {}",
            run.distinct,
            run.family.slots(),
            decided(&against),
            enclosure(&against, grain)
        );
    }
    // The choice: the least charged family whose letters pay their description beyond both the
    // cell-only tree and the constant control of their slots, each decided by disjoint enclosures.
    let admitted: Vec<&FamilyRun> = runs
        .iter()
        .filter(|run| {
            let charged = charged(&run.bits, run.description);
            let control = &controls[run.family.slots() - 1];
            charged.upper < cell_bits.lower && charged.upper < control.bits.lower
        })
        .collect();
    let best = runs
        .iter()
        .min_by(|a, b| {
            let (a, b) = (
                charged(&a.bits, a.description),
                charged(&b.bits, b.description),
            );
            a.upper.cmp(&b.upper)
        })
        .expect("a family");
    let best_charged = charged(&best.bits, best.description);
    println!();
    println!(
        "the least charged family: {} at D = {}: {} a cell charged ({} bits in all)",
        best.name,
        best.sweep.chosen,
        per(&best_charged, cells, grain),
        exact(&best_charged.upper)
    );
    println!(
        "the cell-only tree at D = {}: {} a cell",
        cell_sweep.chosen,
        per(&cell_bits, cells, grain)
    );
    ordering(
        "least charged family against the cell-only tree",
        &best_charged,
        &cell_bits,
        cells,
        grain,
    );
    match admitted.iter().min_by(|a, b| {
        charged(&a.bits, a.description)
            .upper
            .cmp(&charged(&b.bits, b.description).upper)
    }) {
        Some(chosen) => println!(
            "the choice: {} at D = {} (Δ_tree < 0 and Δ_letters < 0 decided)",
            chosen.name, chosen.sweep.chosen
        ),
        None => println!(
            "the choice: the cell-only family at D = {} (no family's letters code below both the cell-only tree and the constant control of their slots by their description)",
            cell_sweep.chosen
        ),
    }
    println!();
    println!(
        "wall time (exterior): the harness {} ms",
        setup.elapsed().as_millis()
    );
}

/// One law's line of the stop-prior sweep: its depths, its development code length and its
/// difference from the `½` tree, uncharged and charged (each law its depths' `⌈log₂⌉`).
fn prior_line(sweep: &PriorSweep, index: usize, cells: u64, grain: u64) {
    let (prior, depths) = &sweep.tried[index];
    let bits = sweep.bits(index);
    let half = sweep.bits(sweep.incumbent);
    let uncharged = ExactInterval {
        lower: &bits.lower - &half.upper,
        upper: &bits.upper - &half.lower,
    };
    let (charged, half_charged) = (sweep.charged(index), sweep.charged(sweep.incumbent));
    let delta = ExactInterval {
        lower: &charged.lower - &half_charged.upper,
        upper: &charged.upper - &half_charged.lower,
    };
    println!(
        "  {prior}: D = {} of {} tried ({} depth bits); L = {} bits in all, {} a cell",
        depths.chosen,
        depths.tried.len(),
        depths.description_bits,
        exact(&bits.upper),
        per(&bits, cells, grain)
    );
    println!(
        "    L − L_½ {}: {}; charged {}",
        decided(&uncharged),
        reading_of(&uncharged, grain),
        reading_of(&delta, grain)
    );
}

/// **One law's development code length by dyadic cell**: every digit's executed face read at the
/// standing before its cell's deposit (`Landmarks::opened`), enclosed and summed per dyadic cell.
fn dyadic_lengths(dev: &Cut, declared: &LandmarkDeclaration) -> Vec<ExactInterval> {
    let mut tree = Landmarks::new(declared.clone()).expect("a declared law");
    let zero = ExactInterval::point(Rat::from_integer(BigInt::from(0)));
    let mut sums = vec![zero; 1usize << tree.digits()];
    for (position, &class) in dev.cells.iter().enumerate() {
        let here = address(&dev.cells, position, declared.depth);
        for path in tree
            .opened(&here, class)
            .expect("a cell within the declaration")
        {
            let length = code_length(&path.faces[0]).expect("a code length");
            sums[path.dyadic] = interval_sum(&sums[path.dyadic], &length).expect("an enclosure");
        }
        tree.deposit(&here, class)
            .expect("a cell within the declaration");
    }
    sums
}

/// **Where the constant-slot controls found their bits** (module header; development only).
fn dyadic_split(dev: &Cut, declared: &LandmarkDeclaration, sweep: &PriorSweep, grain: u64) {
    let clock = Instant::now();
    let lengths: Vec<Vec<ExactInterval>> = (0..sweep.tried.len())
        .into_par_iter()
        .map(|index| {
            let (prior, depths) = &sweep.tried[index];
            dyadic_lengths(
                dev,
                &LandmarkDeclaration {
                    depth: depths.chosen,
                    prior: prior.clone(),
                    ..declared.clone()
                },
            )
        })
        .collect();
    let wall = clock.elapsed().as_millis();
    let half = &lengths[sweep.incumbent];
    let opened: Vec<usize> = (0..half.len())
        .filter(|&h| half[h].upper > Rat::from_integer(BigInt::from(0)))
        .collect();
    let total = |pick: &dyn Fn(usize) -> ExactInterval| -> ExactInterval {
        opened.iter().fold(
            ExactInterval::point(Rat::from_integer(BigInt::from(0))),
            |sum, &h| interval_sum(&sum, &pick(h)).expect("an enclosure"),
        )
    };
    let least = |a: &ExactInterval, b: &ExactInterval| {
        if a.upper <= b.upper {
            a.clone()
        } else {
            b.clone()
        }
    };
    let half_total = total(&|h| half[h].clone());
    let whole = sweep.bits(sweep.incumbent);
    let meets = half_total.lower <= whole.upper && whole.lower <= half_total.upper;
    println!(
        "where the constant-slot controls found their bits (development, {} dyadic cells opened; {wall} ms wall): per law, Σ_h min(L_(½,h), L_(law,h)) − L_½ (a join of the two codes within [that, that + {}]) and the dyadic cells where the law lies below ½:",
        opened.len(),
        opened.len()
    );
    let mut rows: Vec<(usize, ExactInterval, usize)> = (0..sweep.tried.len())
        .filter(|&index| index != sweep.incumbent)
        .map(|index| {
            let law = &lengths[index];
            let joined = total(&|h| least(&half[h], &law[h]));
            let below = opened
                .iter()
                .filter(|&&h| law[h].upper < half[h].lower)
                .count();
            (
                index,
                ExactInterval {
                    lower: &joined.lower - &half_total.upper,
                    upper: &joined.upper - &half_total.lower,
                },
                below,
            )
        })
        .collect();
    println!("  check: the ½ tree's dyadic cells sum to its code length: {meets}");
    rows.sort_by(|a, b| a.1.upper.cmp(&b.1.upper));
    for (index, gain, below) in rows.iter().take(8) {
        println!(
            "  {}: {}; below ½ at {below} of {} dyadic cells",
            sweep.tried[*index].0,
            reading_of(gain, grain),
            opened.len()
        );
    }
    for slots in 1..=4u32 {
        let law = StopPrior::per_depth(vec![1, slots + 1]).expect("a ladder law");
        if let Some((index, gain, below)) = rows
            .iter()
            .find(|(index, _, _)| sweep.tried[*index].0 == law)
        {
            println!(
                "  the control of {slots} slots, {}: {}; below ½ at {below} dyadic cells",
                sweep.tried[*index].0,
                reading_of(gain, grain)
            );
        }
    }
    // The least join by the odometer's digit level (the dyadic cell's depth in the tower thread).
    let (join, _, _) = &rows[0];
    let law = &lengths[*join];
    println!(
        "  by digit level, the least join ({}): Σ_(h at level i) min(L_(½,h), L_(law,h)) − L_(½,h) and the dyadic cells where the law lies below ½",
        sweep.tried[*join].0
    );
    let digits = half.len().trailing_zeros();
    for level in 0..digits {
        let at: Vec<usize> = opened
            .iter()
            .copied()
            .filter(|&h| h >> level == 1)
            .collect();
        let sum = |pick: &dyn Fn(usize) -> ExactInterval| {
            at.iter().fold(
                ExactInterval::point(Rat::from_integer(BigInt::from(0))),
                |sum, &h| interval_sum(&sum, &pick(h)).expect("an enclosure"),
            )
        };
        let (joined, alone) = (
            sum(&|h| least(&half[h], &law[h])),
            sum(&|h| half[h].clone()),
        );
        let below = at.iter().filter(|&&h| law[h].upper < half[h].lower).count();
        println!(
            "    level {level}: {}; below ½ at {below} of {}",
            reading_of(
                &ExactInterval {
                    lower: &joined.lower - &alone.upper,
                    upper: &joined.upper - &alone.lower,
                },
                grain
            ),
            at.len()
        );
    }
    let best = total(&|h| {
        lengths
            .iter()
            .map(|law| law[h].clone())
            .reduce(|a, b| least(&a, &b))
            .expect("a law")
    });
    let gain = ExactInterval {
        lower: &best.lower - &half_total.upper,
        upper: &best.upper - &half_total.lower,
    };
    println!(
        "  the least law in every dyadic cell (uncharged; naming it costs ⌈log₂ {}⌉ bits a dyadic cell): Σ_h min_law L_(law,h) − L_½ = {}",
        sweep.tried.len(),
        reading_of(&gain, grain)
    );
}

/// **The stop-prior decision** (module header, "The stop-prior decision"; Decision 32).
fn prior_harness(path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let full = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    // The development cells alone: the sweep reads nothing else.
    let dev = Cut {
        cells: development(&full),
        held_out: Vec::new(),
    };
    let cells = dev.cells.len() as u64;
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
    };
    let top = ladder_top(&declared);
    let family = prior_family(top);
    println!("hnn_landmark prior: the stop-prior decision (Decision 32) over the cut file {path}");
    println!(
        "development: {cells} cells (the manifest's held-out range {}..{} is cut away before the sweep); |A| = {alphabet}, n* = {count}, L_R = {grain}",
        held.start, held.end
    );
    println!(
        "the family: the global ladder j = 1..{top} and the per-depth pairs (j_0, j_(≥1)), j_0 ≠ j_(≥1): {} laws, J = ⌈log₂(n* B)⌉ = ⌈log₂({count} · {})⌉ = {top}",
        family.len(),
        odometer_digits(alphabet)
    );
    let setup = setup.elapsed().as_millis();
    println!("setup: {setup} ms wall");
    println!();

    let clock = Instant::now();
    let sweep = choose_prior(&dev, &cell_letters(&dev.cells), &declared, &family)
        .expect("the stop-prior sweep");
    let sweep_wall = clock.elapsed().as_millis();
    println!(
        "the sweep: every law with its own depth sweep, charged ⌈log₂⌉ of its depths; the choice ⌈log₂ {}⌉ = {} bits; {sweep_wall} ms wall",
        family.len(),
        sweep.description_bits
    );
    for index in 0..sweep.tried.len() {
        prior_line(&sweep, index, cells, grain);
    }
    let mut least = 0;
    for index in 0..sweep.tried.len() {
        if sweep.charged(index).upper < sweep.charged(least).upper {
            least = index;
        }
    }
    let (chosen, depths) = &sweep.tried[sweep.chosen];
    println!();
    println!(
        "the least charged law: {} at D = {}",
        sweep.tried[least].0, sweep.tried[least].1.chosen
    );
    println!(
        "the choice: {chosen} at D = {} ({}); strictly below every other law: {}; its description {} bits (the laws' {} and its depths' {})",
        depths.chosen,
        if sweep.chosen == sweep.incumbent {
            "Decision 28's ½: no law lies strictly below it"
        } else {
            "strictly below the ½ tree"
        },
        sweep.decided,
        sweep.chosen_description(),
        sweep.description_bits,
        depths.description_bits
    );
    let (half_depths, chosen_bits) = (&sweep.tried[sweep.incumbent].1, sweep.bits(sweep.chosen));
    ordering(
        "development: the chosen law (charged its whole description) against the ½ tree (charged its depths)",
        &charged(&chosen_bits, sweep.chosen_description()),
        &charged(&sweep.bits(sweep.incumbent), half_depths.description_bits),
        cells,
        grain,
    );
    println!();
    dyadic_split(&dev, &declared, &sweep, grain);
    println!();

    // The held-out pass, once, for the chosen law.
    let at = LandmarkDeclaration {
        depth: depths.chosen,
        prior: chosen.clone(),
        ..declared.clone()
    };
    let half_at = LandmarkDeclaration {
        depth: half_depths.chosen,
        ..declared.clone()
    };
    let letters = cell_letters(&full.cells);
    let clock = Instant::now();
    let run = prequential(&full, &letters, &at).expect("the chosen law's prequential run");
    let run_wall = clock.elapsed().as_millis();
    let clock = Instant::now();
    let ([half_development, half_held], half_run) =
        tree_prequential(&full, &letters, &half_at).expect("the ½ tree's prequential run");
    let half_wall = clock.elapsed().as_millis();
    println!(
        "the held-out pass (once): {chosen} at D = {}, every cell scored before its own deposit",
        at.depth
    );
    println!(
        "check: the run's development code length is the sweep's: {}; the ½ tree's: {}",
        run.development.tree == chosen_bits,
        half_development == sweep.bits(sweep.incumbent)
    );
    let held_cells = run.held_out.cells;
    println!("held out ({held_cells} cells), bits a cell at L_R = {grain}:");
    let rows: [(&str, &ExactInterval); 5] = [
        ("the chosen tree", &run.held_out.tree),
        ("the ½ tree (Decision 28)", &half_held),
        ("online order-0 KT", &run.held_out.order_zero),
        ("online order-1 KT", &run.held_out.order_one),
        ("PPM order 2, escape C", &run.held_out.ppm),
    ];
    for (name, bits) in rows {
        println!("  {name}: {}", per(bits, held_cells, grain));
        println!(
            "    total exact [{}, {}] bits",
            exact(&bits.lower),
            exact(&bits.upper)
        );
    }
    let description = sweep.chosen_description();
    let bits = charged(&run.held_out.tree, description);
    println!("held out, the orderings: the chosen tree charged its {description} description bits");
    ordering(
        "chosen tree against online order-0 KT",
        &bits,
        &run.held_out.order_zero,
        held_cells,
        grain,
    );
    ordering(
        "chosen tree against online order-1 KT",
        &bits,
        &run.held_out.order_one,
        held_cells,
        grain,
    );
    ordering(
        &format!("chosen tree against PPM order {PPM_ORDER}"),
        &bits,
        &run.held_out.ppm,
        held_cells,
        grain,
    );
    ordering(
        &format!(
            "chosen tree against the ½ tree (charged its {} depth bits)",
            half_depths.description_bits
        ),
        &bits,
        &charged(&half_held, half_depths.description_bits),
        held_cells,
        grain,
    );
    ordering(
        "chosen tree against the ½ tree, uncharged",
        &run.held_out.tree,
        &half_held,
        held_cells,
        grain,
    );
    println!();
    tree_run(&run.run, grain);
    println!(
        "the ½ tree at D = {}: {} nodes founded, {} stored bits",
        half_at.depth, half_run.nodes, half_run.bits
    );
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; the sweep {sweep_wall} ms; the held-out pass: the chosen law's prequential run (the tree and the baselines together) {run_wall} ms, the ½ tree's run {half_wall} ms"
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let path = match arguments.as_slice() {
        [key, value] if key == "cut-file" => value.clone(),
        [key, value, mode] if key == "cut-file" && mode == "letters" => {
            letters_harness(value, false);
            return;
        }
        [key, value, mode] if key == "cut-file" && mode == "prior" => {
            prior_harness(value);
            return;
        }
        [key, value, mode, with]
            if key == "cut-file" && mode == "letters" && with == "contacts" =>
        {
            letters_harness(value, true);
            return;
        }
        _ => {
            println!("usage: hnn_landmark cut-file <path> [letters [contacts] | prior]");
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
        family: LetterFamily::cells(),
        prior: holonics::hnn::StopPrior::half(),
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
    let letters = cell_letters(&cut.cells);
    let chosen = choose_depth(&cut, &letters, &declared).expect("the sweep");
    let sweep_wall = clock.elapsed().as_millis();
    sweep(&chosen, &declared, development, grain);
    println!("the sweep: {sweep_wall} ms wall");
    println!();

    let at = LandmarkDeclaration {
        depth: chosen.chosen,
        ..declared.clone()
    };
    let clock = Instant::now();
    let run = prequential(&cut, &letters, &at).expect("the prequential measurement");
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
    let cost = oracle_cost(&cut, &letters, &at).expect("the oracle's run");
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
