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
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin local
//! ```
//!
//! [definition; agent-inferred] **Weighing is local** (`local`; Decision 34): on the **development
//! cells only** (the manifest's held-out range is cut away before anything is read), the receiver's
//! tree (`hnn::receiving::landmark_declaration_with`: the cell-only family at `D = 4`, Decision 28's
//! `½`), every law of Decision 32's declared family (`prior_family(ladder_top)`) and every member of
//! Decision 33's Born family (both emissions at `χ = 2^j`, `j ≤ J` by the cost bound
//! `14·4^J·B·n_dev ≤ 2^37`) are read prequentially, each digit's split before its cell's deposit
//! (`Landmarks::receive_digits`, `Born::read`). These per-digit splits are an exterior measurement
//! of this harness; no owner retains them (no tape).
//! - **1. The oracles** `Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T` at three grains (`u` a digit, a cell, a
//!   dyadic cell), each exactly enclosed: the units' products of observed sides on the tree's
//!   lattice compare exactly, and the chosen products' ratio to the tree's is read by one certified
//!   binary logarithm; for every Born member, every stop law (the eight least and the constant-slot
//!   controls printed), and the least stop law in every unit.
//! - **2. The three local laws**, each measured prequentially on the development cells and charged
//!   `⌈log₂⌉` of its family (the tree's depth bits are common and cancel), each ordering decided by
//!   disjoint exact enclosures, each law refused when its oracle's gain does not exceed its price:
//!   - **at each landmark**: the tree under `LocalLaw` at every rung `j = 1..J` of the ladder
//!     (`J = ladder_top`), the external face each Born member's digit split (`rescale_split` onto
//!     the tree's lattice); the oracle the best member's digit grain, the price its family charge
//!     (a landmark's naming is per landmark and cannot be read from a per-digit oracle);
//!   - **in each digit tree**: the owner's joins (`FaceJoins`) on the laws' executed digit faces,
//!     the members the `½` tree against every other law at the incumbent's rungs `j = 1..J`
//!     (`JoinTree::incumbent`) and the balanced joins of the global ladder and of the whole family;
//!     the oracle the best pair's dyadic-cell grain, the price one bit a dyadic cell opened plus the
//!     charge; and the least law in every dyadic cell against its naming (`⌈log₂⌉` of the laws a
//!     dyadic cell);
//!   - **across epochs**: `Mixture::switching` of the tree's and each Born member's cell faces at
//!     `α = 2^(−j)`, `j = 1..⌈log₂ n*⌉`, beside Decision 30's plain mixture; the oracle the best
//!     member's cell grain, the price the best switching sequence's naming (its dominance bound,
//!     Lean `fixed_share`, by exact Viterbi on integers, less the oracle) plus the charge.
//! - **3. The held-out pass**, once, only for a law whose charged development code lies below the
//!   tree: the tree, online order-0, order-1, PPM-2 (`prequential`) and the chosen law over the
//!   whole cut, every cell scored before its own deposit, in all and a cell at the grain; the stop
//!   mixture's pass through the owner's `StopMixture`, checked against the joins' development code.
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

use holonics::compression::cost::ceil_log2;
use holonics::hnn::born::{Born, BornDeclaration, Emission};
use holonics::hnn::landmark::{
    Coded, DepthSweep, FaceJoins, Feature, IdealLandmarks, JoinTree, LandmarkDeclaration,
    Landmarks, Letter, LetterFamily, LocalLaw, OracleCost, PriorSweep, StopMixture, StopPrior,
    TreeRun, Widths, address, cell_letters, choose_depth, choose_prior, code_length, development,
    development_run, ladder_top, odometer_digits, oracle_cost, prequential, prior_family,
    ratio_code_length, rescale_split, tree_prequential,
};
use holonics::hnn::ratio::interval_sum;
use holonics::hnn::receiving::clock_letters;
use holonics::hnn::receiving::{Mixture, MixtureStep, landmark_declaration_with};
use holonics::hnn::reference::PPM_ORDER;
use holonics::hnn::{Cut, Field, FieldDeclaration, Reference};
use holonics::navigator::trace::SiteKind;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::{One, Zero};
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

// -------------------------------------------------------------------------------------------
// Decision 34: weighing is local (`local`)

/// The development digits in cell order: per opened digit its cell, its dyadic cell and its digit,
/// and each cell's first digit.
struct Digits {
    cell: Vec<usize>,
    dyadic: Vec<usize>,
    symbol: Vec<usize>,
    starts: Vec<usize>,
}

impl Digits {
    fn len(&self) -> usize {
        self.cell.len()
    }

    fn of_cell(&self, cell: usize) -> std::ops::Range<usize> {
        self.starts[cell]..self.starts.get(cell + 1).copied().unwrap_or(self.len())
    }
}

/// **A face source's development splits**: each digit's digit-0 numerator on `2^(−bits)`, read
/// before its cell's deposit.
struct Source {
    label: String,
    splits: Vec<u64>,
    bits: u64,
}

impl Source {
    /// The observed side on the common lattice `2^(−lattice)` (`lattice ≥ bits`, exact).
    fn side(&self, digits: &Digits, i: usize, lattice: u64) -> u64 {
        let zero = self.splits[i];
        let side = if digits.symbol[i] == 0 {
            zero
        } else {
            (1u64 << self.bits) - zero
        };
        side << (lattice - self.bits)
    }
}

/// A balanced product of integers.
fn product(mut values: Vec<BigUint>) -> BigUint {
    if values.is_empty() {
        return BigUint::from(1u32);
    }
    while values.len() > 1 {
        values = values
            .par_chunks(2)
            .map(|pair| {
                if pair.len() == 2 {
                    &pair[0] * &pair[1]
                } else {
                    pair[0].clone()
                }
            })
            .collect();
    }
    values.pop().expect("a product")
}

/// `−log₂(numerator/denominator)`, enclosed (`landmark::ratio_code_length`, unreduced).
fn log_ratio(numerator: &BigUint, denominator: &BigUint) -> ExactInterval {
    ratio_code_length(numerator, denominator).expect("a positive ratio")
}

/// The grains of the oracle: each digit alone, each cell's digits, each dyadic cell's digits.
#[derive(Clone, Copy)]
enum Grain {
    Digit,
    Cell,
    Dyadic,
}

impl Grain {
    fn name(self) -> &'static str {
        match self {
            Grain::Digit => "digit",
            Grain::Cell => "cell",
            Grain::Dyadic => "dyadic cell",
        }
    }

    fn unit(self, digits: &Digits, i: usize) -> usize {
        match self {
            Grain::Digit => i,
            Grain::Cell => digits.cell[i],
            Grain::Dyadic => digits.dyadic[i],
        }
    }

    fn units(self, digits: &Digits, cells: usize, dyadic: usize) -> usize {
        match self {
            Grain::Digit => digits.len(),
            Grain::Cell => cells,
            Grain::Dyadic => dyadic,
        }
    }
}

/// **Each unit's product of observed sides** on the common lattice (each unit's code length is
/// `−log₂` of it over its lattice power; units share the lattice, so products compare exactly).
fn unit_products(
    source: &Source,
    digits: &Digits,
    grain: Grain,
    units: usize,
    lattice: u64,
) -> Vec<BigUint> {
    let mut sides: Vec<Vec<BigUint>> = vec![Vec::new(); units];
    for i in 0..digits.len() {
        sides[grain.unit(digits, i)].push(BigUint::from(source.side(digits, i, lattice)));
    }
    sides.into_par_iter().map(product).collect()
}

/// **The oracle** `Σ_u min_X ℓ_X(u) − L_T ≤ 0` at a grain, exactly enclosed: every unit takes the
/// largest product among the sources, against the tree's (`−log₂` of the chosen products' ratio to
/// the tree's); with how many units a source other than the tree wins.
fn unit_oracle(
    tree: &[BigUint],
    tree_total: &BigUint,
    others: &[&Vec<BigUint>],
) -> (ExactInterval, usize) {
    let mut wins = 0;
    let chosen: Vec<BigUint> = (0..tree.len())
        .map(|u| {
            let mut best = &tree[u];
            for other in others {
                if other[u] > *best {
                    best = &other[u];
                }
            }
            if best != &tree[u] {
                wins += 1;
            }
            best.clone()
        })
        .collect();
    let oracle = log_ratio(&product(chosen), tree_total);
    (oracle, wins)
}

/// A code length accumulated exactly: the product of dyadic faces' numerators and their exponent.
#[derive(Default)]
struct Coder {
    numerators: Vec<BigUint>,
    exponent: u64,
}

impl Coder {
    fn add(&mut self, face: &Rat) {
        let denominator = face.denom().magnitude();
        assert_eq!(denominator.count_ones(), 1, "a dyadic face");
        self.numerators.push(face.numer().magnitude().clone());
        self.exponent += denominator.bits() - 1;
    }

    fn add_side(&mut self, side: u64, bits: u64) {
        self.numerators.push(BigUint::from(side));
        self.exponent += bits;
    }

    fn bits(self) -> ExactInterval {
        let numerator = product(self.numerators);
        log_ratio(&numerator, &(BigUint::from(1u32) << self.exponent as usize))
    }
}

/// The Born receiver's development splits: each digit's digit-0 numerator on `2^(−M)`, read before
/// its cell's deposit, and the wall time.
fn born_source(cells: &[usize], declaration: &BornDeclaration) -> (Source, u128) {
    let clock = Instant::now();
    let mut born = Born::new(declaration.clone()).expect("a Born declaration");
    let bits = u64::from(born.widths().face);
    let mut splits = Vec::with_capacity(cells.len() * 8);
    for &cell in cells {
        let reception = born.read(cell).expect("a Born reception");
        splits.extend(reception.digits.iter().map(|digit| digit.numerator));
        born.deposit(reception).expect("a Born deposit");
    }
    let label = format!(
        "Born {} χ = {}",
        match declaration.emission {
            Emission::Position => "Position",
            Emission::Dyadic => "Dyadic",
        },
        declaration.width
    );
    (
        Source {
            label,
            splits,
            bits,
        },
        clock.elapsed().as_millis(),
    )
}

/// A tree's development splits (any stop prior), with the digits it opens.
fn tree_source(cells: &[usize], declaration: &LandmarkDeclaration) -> (Source, Digits) {
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared tree");
    let bits = tree.face_bits();
    let mut digits = Digits {
        cell: Vec::new(),
        dyadic: Vec::new(),
        symbol: Vec::new(),
        starts: Vec::new(),
    };
    let mut splits = Vec::new();
    for (position, &class) in cells.iter().enumerate() {
        digits.starts.push(digits.len());
        let reading = tree
            .receive_digits(&address(cells, position, declaration.depth), class, &[])
            .expect("a cell within the declaration");
        for digit in reading.digits {
            digits.cell.push(position);
            digits.dyadic.push(digit.dyadic);
            digits.symbol.push(digit.symbol);
            splits.push(digit.split);
        }
    }
    (
        Source {
            label: declaration.prior.to_string(),
            splits,
            bits,
        },
        digits,
    )
}

/// One member's development code length and its label.
struct Member {
    label: String,
    bits: ExactInterval,
    note: String,
}

/// The least member (by upper endpoint) and whether it lies strictly below every other member.
fn least(members: &[Member]) -> (usize, bool) {
    let mut best = 0;
    for (index, member) in members.iter().enumerate() {
        if member.bits.upper < members[best].bits.upper {
            best = index;
        }
    }
    let decided = members
        .iter()
        .enumerate()
        .all(|(index, member)| index == best || members[best].bits.upper < member.bits.lower);
    (best, decided)
}

/// A family's charge `⌈log₂ |family|⌉`.
fn family_charge(members: usize) -> u64 {
    ceil_log2(&BigUint::from(members))
}

/// **The node-local law's run** over a stream: the tree under [`LocalLaw`] reading the external
/// source's splits at each opened digit; the code length on the parts `held` selects (development
/// `false`, held out `true`), the largest certified residual and the founded nodes.
fn local_run(
    cells: &[usize],
    held: &dyn Fn(usize) -> bool,
    declaration: &LandmarkDeclaration,
    law: LocalLaw,
    external: &Source,
) -> ([ExactInterval; 2], Rat, usize) {
    let mut tree = Landmarks::local(declaration.clone(), law).expect("a node-local tree");
    let lattice = tree.face_bits();
    let (mut coders, mut residual) = ([Coder::default(), Coder::default()], Rat::zero());
    let mut index = 0;
    for (position, &class) in cells.iter().enumerate() {
        let opened = declaration.emitted(class).len();
        let splits: Vec<u64> = external.splits[index..index + opened]
            .iter()
            .map(|&x| rescale_split(x, external.bits, lattice))
            .collect();
        index += opened;
        let reading = tree
            .receive_with(&address(cells, position, declaration.depth), class, &splits)
            .expect("a node-local reception");
        coders[usize::from(held(position))].add(&reading.executed);
        if reading.residual > residual {
            residual = reading.residual;
        }
    }
    let [development, held_out] = coders;
    (
        [development.bits(), held_out.bits()],
        residual,
        tree.nodes(),
    )
}

/// **The stop-weight mixture's run on the laws' development splits** (the owner's joins,
/// [`FaceJoins`], on the trees' executed digit faces, which the mixture does not change): the
/// code length of the mixed faces.
fn joins_run(
    digits: &Digits,
    sources: &[&Source],
    tree: JoinTree,
    widths: holonics::hnn::landmark::Widths,
) -> ExactInterval {
    let mut joins = FaceJoins::new(tree, widths).expect("the joins");
    let full = 1u64 << widths.face;
    let zeros = vec![0u128; sources.len()];
    let mut coder = Coder::default();
    for i in 0..digits.len() {
        let faces: Vec<u64> = sources.iter().map(|source| source.splits[i]).collect();
        let symbol = digits.symbol[i];
        let receipt = joins
            .receive(digits.dyadic[i], &faces, symbol, &zeros, &zeros)
            .expect("a join step");
        let side = if symbol == 0 {
            receipt.split
        } else {
            full - receipt.split
        };
        coder.add_side(side, widths.face);
    }
    coder.bits()
}

/// **The switching mixture's run** over the development cells: the tree's cell face and the
/// external source's, mixed by [`Mixture::switching`] (or the plain mixture at `None`), each cell
/// scored before its step; the code length enclosed cell by cell, and the chart's drift.
fn switching_run(
    tree: &[Rat],
    other: &[Rat],
    rung: Option<u32>,
    carrier: u64,
) -> (ExactInterval, Rat) {
    let mut mixture = match rung {
        Some(rung) => Mixture::switching(carrier, rung).expect("a switch rate"),
        None => Mixture::new(carrier),
    };
    let mut bits = ExactInterval::point(Rat::zero());
    for (q_tree, q_other) in tree.iter().zip(other) {
        let weight = mixture.weight();
        let face = &weight * q_tree + (Rat::one() - &weight) * q_other;
        bits = interval_sum(&bits, &code_length(&face).expect("a face")).expect("an enclosure");
        mixture
            .step(&MixtureStep {
                ring: 0,
                tree: q_tree.clone(),
                combined: q_other.clone(),
                residual: Rat::zero(),
            })
            .expect("a positive step");
    }
    (bits, mixture.drift().clone())
}

/// Each cell's face from a source's splits on the common lattice: `Π side/2^(lattice · digits)`.
fn cell_faces(source: &Source, digits: &Digits, cells: usize, lattice: u64) -> Vec<Rat> {
    (0..cells)
        .map(|cell| {
            let range = digits.of_cell(cell);
            let numerator: BigUint = range
                .clone()
                .map(|i| BigUint::from(source.side(digits, i, lattice)))
                .product();
            Rat::new(
                BigInt::from(numerator),
                BigInt::from(1u32) << (lattice as usize * range.len()),
            )
        })
        .collect()
}

/// **The switching law's dominance bound** (Lean `HNN/LocalWeighing.fixed_share`), exact: the
/// best switching sequence's prior times its faces, `max_σ ½ Π T(σ_t, σ_(t+1)) Π f_σ(t)`, by
/// Viterbi on integers over the common lattice; returned as the bound minus `L_T` (`−log₂` of its
/// ratio to the tree's product).
fn switching_bound(
    tree: &[BigUint],
    tree_total: &BigUint,
    other: &[BigUint],
    rung: u32,
) -> ExactInterval {
    let keep = (BigUint::from(1u32) << rung as usize) - 1u32;
    let mut values = [tree[0].clone(), other[0].clone()];
    for t in 1..tree.len() {
        let faces = [&tree[t], &other[t]];
        let next = [0, 1].map(|x| {
            let stay = &values[x] * &keep;
            let switch = &values[1 - x];
            let best = if &stay >= switch {
                stay
            } else {
                switch.clone()
            };
            best * faces[x]
        });
        values = next;
    }
    let best = if values[0] >= values[1] {
        &values[0]
    } else {
        &values[1]
    };
    // The prior's denominator: ½ at the opening and 2^j a transition.
    let transitions = (tree.len() - 1) as u64 * u64::from(rung) + 1;
    log_ratio(best, &(tree_total << transitions as usize))
}

/// **Decision 34's development decision** (module header, "Weighing is local").
fn local_harness(path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let receiver = field.receivers()[0].clone();
    let declared = landmark_declaration_with(&field, &receiver, LetterFamily::cells())
        .expect("the receiver's tree");
    let full = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    let dev = development(&full);
    let cells = dev.len();
    let population = count as u64;
    println!("hnn_landmark local: weighing is local (Decision 34) over the cut file {path}");
    println!(
        "development: {cells} cells (the manifest's held-out range {}..{} is cut away before anything is read); |A| = {alphabet}, n* = {count}, L_R = {grain}; the tree at D = {} under {}",
        held.start, held.end, declared.depth, declared.prior
    );

    // The tree, the declared stop laws and the Born members, each prequential on the development
    // cells; their splits read before each cell's deposit (an exterior measurement, never retained
    // by the machine).
    let clock = Instant::now();
    let (tree, digits) = tree_source(&dev, &declared);
    let lattice = tree.bits;
    let tree_widths = Landmarks::new(declared.clone()).expect("a tree").widths();
    let top = ladder_top(&declared);
    let laws = prior_family(top);
    let law_sources: Vec<Source> = laws
        .par_iter()
        .map(|prior| {
            tree_source(
                &dev,
                &LandmarkDeclaration {
                    prior: prior.clone(),
                    ..declared.clone()
                },
            )
            .0
        })
        .collect();
    let laws_ms = clock.elapsed().as_millis();
    let bits_b = u128::from(odometer_digits(alphabet));
    let mut bound = 0u32;
    while 14 * (1u128 << (2 * (bound + 1))) * bits_b * cells as u128 <= 1u128 << 37 {
        bound += 1;
    }
    let born_declarations: Vec<BornDeclaration> = [Emission::Position, Emission::Dyadic]
        .into_iter()
        .flat_map(|emission| {
            (0..=bound).map(move |order| BornDeclaration {
                alphabet,
                width: 1 << order,
                emission,
                population,
                grain,
            })
        })
        .collect();
    let clock = Instant::now();
    let born: Vec<(Source, u128)> = born_declarations
        .par_iter()
        .map(|declaration| born_source(&dev, declaration))
        .collect();
    let born_ms = clock.elapsed().as_millis();
    let dyadic_cells = 1usize << odometer_digits(alphabet);
    println!(
        "read: the ½ tree and the {} declared stop laws (J = {top}) in {laws_ms} ms; the {} Born members (both emissions, χ = 1..2^{bound}) in {born_ms} ms wall ({} digits)",
        laws.len(),
        born.len(),
        digits.len()
    );
    for (source, ms) in &born {
        println!("  {}: M = {}, {ms} ms", source.label, source.bits);
    }
    let setup_ms = setup.elapsed().as_millis();
    println!();

    // ---- 1. The oracles, on the development cells only.
    let tree_code = {
        let mut coder = Coder::default();
        for i in 0..digits.len() {
            coder.add_side(tree.side(&digits, i, lattice), lattice);
        }
        coder.bits()
    };
    let (sweep_bits, _) = development_run(&dev_cut(&dev), &cell_letters(&dev), &declared)
        .expect("the tree's development run");
    // The tree's depth, chosen on the development cells (Decision 28), and its description bits.
    let depth_sweep =
        choose_depth(&dev_cut(&dev), &cell_letters(&dev), &declared).expect("the depth sweep");
    assert_eq!(
        depth_sweep.chosen, declared.depth,
        "the receiver's depth is the sweep's"
    );
    let depth_bits = depth_sweep.description_bits;
    println!(
        "the ½ tree: L_T {} ({} a cell); the sweep's enclosure agrees: {}; its depth D = {} of {} tried, {depth_bits} description bits, common to every law here",
        enclosure(&tree_code, grain),
        per(&tree_code, cells as u64, grain),
        sweep_bits.lower <= tree_code.upper && tree_code.lower <= sweep_bits.upper,
        depth_sweep.chosen,
        depth_sweep.tried.len()
    );
    println!(
        "1. the oracles Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T (development; u a digit, a cell or a dyadic cell; exact enclosures, bits at L_R = {grain}; before any price):"
    );
    let grains = [Grain::Digit, Grain::Cell, Grain::Dyadic];
    let tree_units: Vec<Vec<BigUint>> = grains
        .iter()
        .map(|&g| {
            unit_products(
                &tree,
                &digits,
                g,
                g.units(&digits, cells, dyadic_cells),
                lattice,
            )
        })
        .collect();
    let tree_totals: Vec<BigUint> = tree_units
        .iter()
        .map(|units| product(units.clone()))
        .collect();
    let units_of = |source: &Source| -> Vec<Vec<BigUint>> {
        grains
            .iter()
            .map(|&g| {
                unit_products(
                    source,
                    &digits,
                    g,
                    g.units(&digits, cells, dyadic_cells),
                    lattice,
                )
            })
            .collect()
    };
    let oracle_line = |label: &str, units: &[Vec<BigUint>]| -> Vec<ExactInterval> {
        let mut gains = Vec::new();
        let mut line = format!("  {label}:");
        for (g, grain_units) in units.iter().enumerate() {
            let (oracle, wins) = unit_oracle(&tree_units[g], &tree_totals[g], &[grain_units]);
            line += &format!(
                " {} {} (wins {wins});",
                grains[g].name(),
                reading_of(&oracle, grain)
            );
            gains.push(oracle);
        }
        println!("{line}");
        gains
    };
    let born_units: Vec<Vec<Vec<BigUint>>> = born.iter().map(|(s, _)| units_of(s)).collect();
    let mut born_oracles = Vec::new();
    for ((source, _), units) in born.iter().zip(&born_units) {
        let code = {
            let mut coder = Coder::default();
            for i in 0..digits.len() {
                coder.add_side(source.side(&digits, i, lattice), lattice);
            }
            coder.bits()
        };
        println!(
            "  {} alone: {} a cell",
            source.label,
            per(&code, cells as u64, grain)
        );
        born_oracles.push(oracle_line(&source.label, units));
    }
    let law_units: Vec<Vec<Vec<BigUint>>> = law_sources.par_iter().map(units_of).collect();
    let mut law_rows: Vec<(usize, Vec<ExactInterval>)> = (1..laws.len())
        .into_par_iter()
        .map(|k| {
            let gains = (0..grains.len())
                .map(|g| unit_oracle(&tree_units[g], &tree_totals[g], &[&law_units[k][g]]).0)
                .collect();
            (k, gains)
        })
        .collect();
    law_rows.sort_by(|a, b| a.1[2].upper.cmp(&b.1[2].upper));
    println!(
        "  the stop laws, by their dyadic-cell oracle (the eight least, then the constant-slot controls):"
    );
    let law_line = |k: usize, gains: &[ExactInterval]| {
        println!(
            "    {}: digit {}; cell {}; dyadic cell {}",
            laws[k],
            reading_of(&gains[0], grain),
            reading_of(&gains[1], grain),
            reading_of(&gains[2], grain)
        );
    };
    for (k, gains) in law_rows.iter().take(8) {
        law_line(*k, gains);
    }
    for slots in 1..=4u32 {
        let control = StopPrior::per_depth(vec![1, slots + 1]).expect("a ladder law");
        if let Some((k, gains)) = law_rows.iter().find(|(k, _)| laws[*k] == control) {
            law_line(*k, gains);
        }
    }
    let least_law: Vec<(ExactInterval, usize)> = (0..grains.len())
        .map(|g| {
            let all: Vec<&Vec<BigUint>> = (1..laws.len()).map(|k| &law_units[k][g]).collect();
            unit_oracle(&tree_units[g], &tree_totals[g], &all)
        })
        .collect();
    println!(
        "  the least stop law in every unit: digit {} (the least law wins {}); cell {} ({}); dyadic cell {} ({} of {} dyadic cells opened)",
        reading_of(&least_law[0].0, grain),
        least_law[0].1,
        reading_of(&least_law[1].0, grain),
        least_law[1].1,
        reading_of(&least_law[2].0, grain),
        least_law[2].1,
        tree_units[2]
            .iter()
            .filter(|p| **p != BigUint::from(1u32))
            .count()
    );
    println!();

    // ---- 2. The laws, measured prequentially on the development cells, charged.
    let opened = tree_units[2]
        .iter()
        .filter(|p| **p != BigUint::from(1u32))
        .count() as u64;
    println!(
        "2. the local laws on the development cells, prequential, each charged ⌈log₂⌉ of its family (the tree's depth bits are common and cancel):"
    );

    // (a) Node-local mixing, Born's digit split as the admitted external face.
    let clock = Instant::now();
    let local_members: Vec<(usize, u32)> = (0..born.len())
        .flat_map(|m| (1..=top).map(move |j| (m, j)))
        .collect();
    let never = |_: usize| false;
    let local_runs: Vec<Member> = local_members
        .par_iter()
        .map(|&(m, j)| {
            let law = LocalLaw::new(j).expect("a rung");
            let ([bits, _], residual, nodes) = local_run(&dev, &never, &declared, law, &born[m].0);
            Member {
                label: format!("{} with {}", law, born[m].0.label),
                bits,
                note: format!(
                    "{nodes} nodes, largest residual ≤ {} bits",
                    exact(&residual)
                ),
            }
        })
        .collect();
    let local_ms = clock.elapsed().as_millis();
    let local_charge = family_charge(local_runs.len());
    let decide = |label: &str,
                  runs: &[Member],
                  charge: u64,
                  oracle: &ExactInterval,
                  price: &Rat|
     -> Option<usize> {
        let (best, decided) = least(runs);
        let charged_bits = charged(&runs[best].bits, charge);
        let gain = ExactInterval {
            lower: -&oracle.upper,
            upper: -&oracle.lower,
        };
        let exceeds = gain.lower > *price;
        println!(
            "  {label}: {} members, charged {charge} bits; the oracle's gain {} against the price {}: {}",
            runs.len(),
            reading_of(&gain, grain),
            reading_of(&ExactInterval::point(price.clone()), grain),
            if exceeds {
                "exceeds it"
            } else {
                "does not exceed it: refused"
            }
        );
        println!(
            "    the least member: {} ({}); {} a cell uncharged; strictly below every other member: {decided}",
            runs[best].label,
            runs[best].note,
            per(&runs[best].bits, cells as u64, grain)
        );
        ordering(
            "    the least member, charged, against the ½ tree",
            &charged_bits,
            &tree_code,
            cells as u64,
            grain,
        );
        let below = charged_bits.upper < tree_code.lower;
        (exceeds && below).then_some(best)
    };
    println!("  (a) at each landmark (node-local mixing; {local_ms} ms wall):");
    for (m, (source, _)) in born.iter().enumerate() {
        let (row, _) = least(&local_runs[m * top as usize..(m + 1) * top as usize]);
        let run = &local_runs[m * top as usize + row];
        println!(
            "    {}: best {} {} a cell ({} against the tree uncharged)",
            source.label,
            run.label,
            per(&run.bits, cells as u64, grain),
            reading_of(&difference_interval(&run.bits, &tree_code), grain)
        );
    }
    let local_oracle = born_oracles
        .iter()
        .map(|gains| gains[0].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a member");
    let local_choice = decide(
        "node-local (the digit-grain oracle of the best Born member; the price its family charge)",
        &local_runs,
        local_charge,
        &local_oracle,
        &Rat::from_integer(BigInt::from(local_charge)),
    );

    // (b) The stop-weight mixture per digit tree.
    let clock = Instant::now();
    let mut stop_members: Vec<(Vec<usize>, JoinTree, String)> = Vec::new();
    for (k, law) in laws.iter().enumerate().skip(1) {
        for j in 1..=top {
            stop_members.push((
                vec![0, k],
                JoinTree::incumbent(2, j).expect("a rung"),
                format!("½ with {law} at π_½ = 1 − 2^(−{j})"),
            ));
        }
    }
    let ladder: Vec<usize> = (0..laws.len()).filter(|&k| laws[k].is_global()).collect();
    stop_members.push((
        ladder.clone(),
        JoinTree::balanced(ladder.len()).expect("a family"),
        format!("the global ladder j = 1..{top}, balanced"),
    ));
    stop_members.push((
        (0..laws.len()).collect(),
        JoinTree::balanced(laws.len()).expect("a family"),
        format!("all {} laws, balanced", laws.len()),
    ));
    let stop_runs: Vec<Member> = stop_members
        .par_iter()
        .map(|(faces, join, label)| {
            let sources: Vec<&Source> = faces.iter().map(|&k| &law_sources[k]).collect();
            Member {
                label: label.clone(),
                bits: joins_run(&digits, &sources, join.clone(), tree_widths),
                note: format!("{} faces", faces.len()),
            }
        })
        .collect();
    let stop_ms = clock.elapsed().as_millis();
    let stop_charge = family_charge(stop_runs.len());
    // The price at the dyadic-cell grain: naming the least law in every dyadic cell opened among the
    // pair (one bit a dyadic cell at π = ½) and the family's charge.
    let stop_oracle = law_rows
        .iter()
        .map(|(_, gains)| gains[2].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a law");
    println!(
        "  (b) in each digit tree (the stop-weight mixture; {} members: the ½ tree against each other law at the incumbent's rungs j = 1..{top}, and two balanced families; {stop_ms} ms wall):",
        stop_runs.len()
    );
    for index in [stop_runs.len() - 2, stop_runs.len() - 1] {
        println!(
            "    {}: {} a cell ({} against the tree uncharged)",
            stop_runs[index].label,
            per(&stop_runs[index].bits, cells as u64, grain),
            reading_of(
                &difference_interval(&stop_runs[index].bits, &tree_code),
                grain
            )
        );
    }
    let least_all = least_law[2].0.clone();
    println!(
        "    the least law in every dyadic cell: oracle {} against its naming ⌈log₂ {}⌉ = {} bits a dyadic cell over {opened} opened, {} bits: {}",
        reading_of(&least_all, grain),
        laws.len() - 1,
        family_charge(laws.len() - 1),
        family_charge(laws.len() - 1) * opened,
        if -&least_all.upper
            > Rat::from_integer(BigInt::from(family_charge(laws.len() - 1) * opened))
        {
            "exceeds it"
        } else {
            "does not exceed it: refused"
        }
    );
    let stop_price = Rat::from_integer(BigInt::from(opened + stop_charge));
    let stop_choice = decide(
        "stop mixture (the best pair's dyadic-cell oracle; the price one bit a dyadic cell opened plus the family charge)",
        &stop_runs,
        stop_charge,
        &stop_oracle,
        &stop_price,
    );

    // (c) Fixed-share across epochs: the tree's cell face against each Born member's.
    let clock = Instant::now();
    let shares = u32::try_from(ceil_log2(&BigUint::from(population))).expect("a rung");
    let tree_cells = cell_faces(&tree, &digits, cells, lattice);
    let born_cells: Vec<Vec<Rat>> = born
        .iter()
        .map(|(s, _)| cell_faces(s, &digits, cells, lattice))
        .collect();
    let switch_members: Vec<(usize, u32)> = (0..born.len())
        .flat_map(|m| (1..=shares).map(move |j| (m, j)))
        .collect();
    let switch_runs: Vec<Member> = switch_members
        .par_iter()
        .map(|&(m, j)| {
            let (bits, drift) =
                switching_run(&tree_cells, &born_cells[m], Some(j), tree_widths.carrier);
            Member {
                label: format!("α = 2^(−{j}) with {}", born[m].0.label),
                bits,
                note: format!("drift ≤ {} bits", exact(&drift)),
            }
        })
        .collect();
    let bounds: Vec<ExactInterval> = switch_members
        .par_iter()
        .map(|&(m, j)| switching_bound(&tree_units[1], &tree_totals[1], &born_units[m][1], j))
        .collect();
    let switch_ms = clock.elapsed().as_millis();
    let switch_charge = family_charge(switch_runs.len());
    println!(
        "  (c) across epochs (the switching mixture of the tree's and a Born member's cell faces at α = 2^(−j), j = 1..{shares}; {} members; {switch_ms} ms wall):",
        switch_runs.len()
    );
    for (m, (source, _)) in born.iter().enumerate() {
        let span = m * shares as usize..(m + 1) * shares as usize;
        let (row, _) = least(&switch_runs[span.clone()]);
        let best_bound = bounds[span.clone()]
            .iter()
            .min_by(|a, b| a.upper.cmp(&b.upper))
            .expect("a rate");
        let (plain, _) = switching_run(&tree_cells, &born_cells[m], None, tree_widths.carrier);
        println!(
            "    {}: best {} {} against the tree; Decision 30's plain mixture {}; the dominance bound (best switching sequence with its price) {}; the cell-grain oracle {}",
            source.label,
            switch_runs[span.start + row].label,
            reading_of(
                &difference_interval(&switch_runs[span.start + row].bits, &tree_code),
                grain
            ),
            reading_of(&difference_interval(&plain, &tree_code), grain),
            reading_of(best_bound, grain),
            reading_of(&born_oracles[m][1], grain),
        );
    }
    let switch_oracle = born_oracles
        .iter()
        .map(|gains| gains[1].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a member");
    let best_bound = bounds
        .iter()
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a bound");
    // The price at the cell grain: the best switching sequence's naming, read off its dominance
    // bound minus its oracle, with the family's charge.
    let switch_price =
        &best_bound.upper - &switch_oracle.lower + Rat::from_integer(BigInt::from(switch_charge));
    let switch_choice = decide(
        "switching (the best Born member's cell-grain oracle; the price the best switching sequence's naming plus the family charge)",
        &switch_runs,
        switch_charge,
        &switch_oracle,
        &switch_price.max(Rat::from_integer(BigInt::from(switch_charge))),
    );
    println!();

    // ---- 3. The held-out pass, once, for each law that codes below the tree.
    let chosen = [
        local_choice.map(|i| ("node-local", i)),
        stop_choice.map(|i| ("stop mixture", i)),
        switch_choice.map(|i| ("switching", i)),
    ];
    if chosen.iter().all(Option::is_none) {
        println!(
            "3. no local law codes below the ½ tree on the development cells, charged: that is the result, and no held-out cell is read"
        );
    } else {
        println!("3. the held-out pass, once, for each law that codes below the tree:");
        let letters = cell_letters(&full.cells);
        let clock = Instant::now();
        let run = prequential(&full, &letters, &declared).expect("the tree and the baselines");
        let held_cells = run.held_out.cells;
        let is_held = |position: usize| held.contains(&position);
        println!("  held out ({held_cells} cells), bits a cell at L_R = {grain}:");
        for (name, bits) in [
            ("the ½ tree", &run.held_out.tree),
            ("online order-0 KT", &run.held_out.order_zero),
            ("online order-1 KT", &run.held_out.order_one),
            ("PPM order 2, escape C", &run.held_out.ppm),
        ] {
            println!(
                "    {name}: {} (total {})",
                per(bits, held_cells, grain),
                enclosure(bits, grain)
            );
        }
        let clock_half = Instant::now();
        let mut half_tree = Landmarks::new(declared.clone()).expect("the ½ tree");
        for (position, &class) in full.cells.iter().enumerate() {
            half_tree
                .receive(&address(&full.cells, position, declared.depth), class)
                .expect("a cell");
        }
        println!(
            "    the ½ tree's whole passage: {} ms, {} nodes, {} stored bits",
            clock_half.elapsed().as_millis(),
            half_tree.nodes(),
            half_tree.bits()
        );
        for (name, index) in chosen.into_iter().flatten() {
            let clock_law = Instant::now();
            let (bits, charge) = match name {
                "node-local" => {
                    let (m, j) = local_members[index];
                    let (whole, _) = born_source(&full.cells, &born_declarations[m]);
                    let ([_, held_bits], _, _) = local_run(
                        &full.cells,
                        &is_held,
                        &declared,
                        LocalLaw::new(j).expect("a rung"),
                        &whole,
                    );
                    (held_bits, local_charge)
                }
                "stop mixture" => {
                    let (faces, join, _) = &stop_members[index];
                    let mut mixture = StopMixture::new(
                        declared.clone(),
                        faces.iter().map(|&k| laws[k].clone()).collect(),
                        join.clone(),
                    )
                    .expect("the chosen mixture");
                    let mut coders = [Coder::default(), Coder::default()];
                    for (position, &class) in full.cells.iter().enumerate() {
                        let reading = mixture
                            .receive(&address(&full.cells, position, declared.depth), class)
                            .expect("a cell");
                        coders[usize::from(is_held(position))].add(&reading.executed);
                    }
                    let [development_bits, held_bits] = coders.map(Coder::bits);
                    println!(
                        "    check: the owner's StopMixture reproduces the development code: {}",
                        development_bits == stop_runs[index].bits
                    );
                    let nodes: usize = mixture.trees().iter().map(Landmarks::nodes).sum();
                    let stored: u64 = mixture.trees().iter().map(Landmarks::bits).sum();
                    let (rebases, _) = mixture.joins().rebases();
                    println!(
                        "    the mixture's whole passage: {} ms, {nodes} nodes and {stored} stored bits in its {} trees, {} join rebases, the joins' largest drift ≤ {} bits",
                        clock_law.elapsed().as_millis(),
                        mixture.trees().len(),
                        rebases,
                        exact(&mixture.joins().drift())
                    );
                    (held_bits, stop_charge)
                }
                _ => {
                    let (m, j) = switch_members[index];
                    let (whole, _) = born_source(&full.cells, &born_declarations[m]);
                    let (whole_tree, whole_digits) = tree_source(&full.cells, &declared);
                    let n = full.cells.len();
                    let tree_faces = cell_faces(&whole_tree, &whole_digits, n, lattice);
                    let born_faces = cell_faces(&whole, &whole_digits, n, lattice);
                    let mut mixture = Mixture::switching(tree_widths.carrier, j).expect("a rate");
                    let mut bits = ExactInterval::point(Rat::zero());
                    for position in 0..n {
                        let weight = mixture.weight();
                        let face = &weight * &tree_faces[position]
                            + (Rat::one() - &weight) * &born_faces[position];
                        if is_held(position) {
                            bits = interval_sum(&bits, &code_length(&face).expect("a face"))
                                .expect("an enclosure");
                        }
                        mixture
                            .step(&MixtureStep {
                                ring: 0,
                                tree: tree_faces[position].clone(),
                                combined: born_faces[position].clone(),
                                residual: Rat::zero(),
                            })
                            .expect("a step");
                    }
                    (bits, switch_charge)
                }
            };
            println!(
                "  {name} ({}): {} a cell (total {})",
                match name {
                    "node-local" => &local_runs[index].label,
                    "stop mixture" => &stop_runs[index].label,
                    _ => &switch_runs[index].label,
                },
                per(&bits, held_cells, grain),
                enclosure(&bits, grain)
            );
            println!(
                "    {name}'s held-out pass: {} ms",
                clock_law.elapsed().as_millis()
            );
            ordering(
                &format!(
                    "  {name}, charged its family's {charge} bits, against the ½ tree (both charged the depth's {depth_bits})"
                ),
                &charged(&bits, charge),
                &run.held_out.tree,
                held_cells,
                grain,
            );
            let total = charge + depth_bits;
            for (label, against) in [
                ("online order-0 KT", &run.held_out.order_zero),
                ("online order-1 KT", &run.held_out.order_one),
                ("PPM order 2", &run.held_out.ppm),
            ] {
                ordering(
                    &format!(
                        "  {name}, charged {total} bits (its family's and the depth's), against {label}"
                    ),
                    &charged(&bits, total),
                    against,
                    held_cells,
                    grain,
                );
            }
        }
        println!(
            "  the held-out pass: {} ms wall",
            clock.elapsed().as_millis()
        );
    }
    println!();
    println!(
        "wall time (exterior): setup and reads {setup_ms} ms; the harness {} ms",
        setup.elapsed().as_millis()
    );
}

/// `a − b` of two enclosures.
fn difference_interval(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

/// A cut of the development cells alone.
fn dev_cut(cells: &[usize]) -> Cut {
    Cut {
        cells: cells.to_vec(),
        held_out: Vec::new(),
    }
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
        [key, value, mode] if key == "cut-file" && mode == "local" => {
            local_harness(value);
            return;
        }
        [key, value, mode, with]
            if key == "cut-file" && mode == "letters" && with == "contacts" =>
        {
            letters_harness(value, true);
            return;
        }
        _ => {
            println!("usage: hnn_landmark cut-file <path> [letters [contacts] | prior | local]");
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
