//! **The landmark tree on terrain a declared Holarchy made** (the record of September 27, §3.3 and
//! §5; rebuild step 4, #73): the first receipts of `holonics::holarchy::terrain`, count-only, a
//! committed command run once in release, never a test. These are **development receipts**: the
//! conversation cut stays the living substrate and the milestone (Brandon's ruling of August 26),
//! and no claim here is joined to the cut's.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_terrain -- tree 2
//! cargo run --release -p holonics --example hnn_terrain -- tree 4
//! cargo run --release -p holonics --example hnn_terrain -- moire
//! ```
//!
//! [definition; agent-inferred] **`tree d`: a tree source** (`terrain::TreeSource`), drawn from its
//! family (bits, depth `d`, faces on the grid `1/16`) by the seeded draw [`SEED`], which then emits
//! `n = 2^16` cells. The receiving tree (`compression::landmark::context`, the cell-only family,
//! the `½` stop prior, KT nodes) is declared at depth `D = d + 2` (two past the source, so the tree
//! must find where the source stops), `n* = n`, `L_R = 16`. Printed, exactly:
//! - **the truth**: the leaves with their faces and stationary weights, the rate `h` as its exact
//!   form in `log₂ p` and its enclosure, and `n·h`;
//! - **the code**: `hnn::reference::prequential` over the passage (one population), the tree and
//!   the online baselines (order-0 and order-1 KT, PPM-2);
//! - **the redundancy** `code − n·h`, and `code − code_θ(x)` against the source's own code of the
//!   realized cells (`TreeSource::passage`), each an exact enclosure;
//! - **the bound** (`TreeSource::weighting_bound`): `Γ(S′) + Σ_(n_s ≥ 1)(½ log₂ n_s + 1) + b`, plus
//!   the chart's certified drift `n · (largest per-cell residual)`, beside the headline
//!   `½|S|(|A| − 1) log₂ n + Γ(S′)`; and whether `code − code_θ(x)` is decided within it;
//! - **the recovered tree** (`TreeSource::recovery`) of the standing after the passage, against the
//!   drawn one.
//!
//! [definition; agent-inferred] **`moire`: a moiré** (`terrain::Moire`) of 3 gratings, denominators
//! up to `2^4`, drawn by [`SEED`], emitting `n = 2^14` cells as the parity color and as the sheet
//! tuple. Its truth: the gratings (the keys), the joint period and the emission's least period (as
//! integers with their factorization), the determining depth, the pairs' locks, the rate zero and
//! the key description `⌈log₂ |key space|⌉`. The receiving tree chooses its depth on the passage
//! (`choose_depth_within`, the harness's rule, within Decision 37's `D = 48`); the code in all is
//! printed at every depth to the truth's determining depth `D*` and two past it (a control past the
//! sweep). At the chosen depth, and as a control at `D*` (the truth's, never a choice), the tree
//! codes the passage (`prequential`) and each read least period (`tree_prequential` with that
//! period as the scored-apart range, every cell still scored before its own deposit: the first
//! four, then periods `7, 15, 31, …`, the last), and the periods after the first four in all and
//! a period: the zero-rate terrain's code against the key description, and the code a period as
//! the tree learns it.
//!
//! Every reading is exact (the notebook's exterior, `exterior.rs`): bits are enclosures with exact
//! endpoints read at `L_R = 16` as `n + k/16 + ε`; no decimal is printed. Each run is seconds.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, LetterFamily, StopPrior, address, cell_letters,
};
use holonics::hnn::Cut;
use holonics::hnn::reference::{Coded, choose_depth_within, prequential, tree_prequential};
use holonics::holarchy::terrain::{
    Draw, Moire, MoireClass, MoireFamily, TreeSource, TreeSourceFamily,
};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_difference, interval_sum, log2_enclosure};
use holonics::ratio::surprisal::SymbolicSurprisal;
use num_bigint::{BigInt, BigUint};

use exterior::{against, enclosure, exact, per};

/// The declared seed of every terrain here: its draw's initial configuration.
const SEED: u64 = 20_260_927;

/// The receiver's grain `L_R`.
const GRAIN: u64 = 16;

/// The tree source's passage `2^16` and its faces' grid `1/16`.
const TREE_CELLS: usize = 1 << 16;
const TREE_GRID: u64 = 16;

/// The moiré's passage `2^14`, its gratings and their greatest denominator `2^4`.
const MOIRE_CELLS: usize = 1 << 14;
const MOIRE_RINGS: usize = 3;
const MOIRE_DENOMINATOR: u64 = 16;

/// Decision 37's depth: the moiré's depth sweep stops there.
const DEEPEST: usize = 48;

/// **An integer with its factorization**, `n = p^a·q^b…` (read from `log₂ n`'s exact form).
fn factored(value: &BigUint) -> String {
    if value <= &BigUint::from(1u32) {
        return value.to_string();
    }
    let form = SymbolicSurprisal::log2_of_ratio(&Rat::from_integer(BigInt::from(value.clone())))
        .expect("a positive integer");
    let factors: Vec<String> = form
        .terms()
        .iter()
        .map(|(prime, exponent)| {
            if exponent == &Rat::from_integer(BigInt::from(1)) {
                prime.to_string()
            } else {
                format!("{prime}^{exponent}")
            }
        })
        .collect();
    format!("{value} = {}", factors.join("·"))
}

/// An enclosure held outward on the declared grid `2^(−96)` (`ratio::algebraic::LOG_OCTAVES`): still
/// an exact enclosure, with dyadic endpoints.
fn on_grid(interval: &ExactInterval) -> ExactInterval {
    interval_sum(interval, &point(0)).expect("an enclosure")
}

fn point(value: u64) -> ExactInterval {
    ExactInterval::point(Rat::from_integer(BigInt::from(value)))
}

fn declaration(alphabet: usize, depth: usize, population: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: population as u64,
        grain: GRAIN,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

fn coded_lines(coded: &Coded) {
    let cells = coded.cells;
    for (name, bits) in [
        ("tree (executed lattice face)", &coded.tree),
        ("online order-0 KT", &coded.order_zero),
        ("online order-1 KT", &coded.order_one),
        ("PPM order 2, escape C", &coded.ppm),
    ] {
        println!("  {name}: {}", enclosure(bits, GRAIN));
        println!("    a cell: {}", per(bits, cells, GRAIN));
    }
}

/// **`tree d`** (module header).
fn tree_harness(depth: usize) {
    let started = Instant::now();
    let family = TreeSourceFamily {
        alphabet: 2,
        depth,
        grid: TREE_GRID,
    };
    let mut draw = Draw::new(SEED);
    let source = TreeSource::draw(&family, &mut draw).expect("a tree source of the family");
    let cells = source.emit(TREE_CELLS, &mut draw);
    let truth = source.truth().expect("the source's truth");
    let n = TREE_CELLS as u64;
    let receiver_depth = depth + 2;
    println!(
        "hnn_terrain tree {depth}: a tree source over bits, depth d = {depth}, faces on 1/{TREE_GRID}, seed {SEED}; n = {n} = 2^16 cells"
    );
    println!(
        "the truth: |S| = {} leaves (shift-closed: {}), depth {}",
        truth.leaves.len(),
        source.tree().is_shift_closed(),
        source.tree().depth()
    );
    for ((leaf, face), weight) in truth.leaves.iter().zip(&truth.faces).zip(&truth.stationary) {
        let context: String = leaf.iter().map(ToString::to_string).collect();
        let face: Vec<String> = face.iter().map(exact).collect();
        println!(
            "  leaf [{context}] (newest first): face ({}), stationary weight {}",
            face.join(", "),
            exact(weight)
        );
    }
    let terms: Vec<String> = truth
        .rate
        .terms()
        .iter()
        .map(|(prime, coefficient)| format!("({}) log₂ {prime}", exact(coefficient)))
        .collect();
    println!("  rate h = {} bits a cell, exactly", terms.join(" + "));
    println!("    {}", enclosure(&on_grid(&truth.rate_bits), GRAIN));
    let total_rate = on_grid(
        &truth
            .rate
            .scaled(&Rat::from_integer(BigInt::from(n)))
            .enclosure()
            .expect("an enclosure"),
    );
    println!("  n·h: {}", enclosure(&total_rate, GRAIN));

    let declared = declaration(2, receiver_depth, TREE_CELLS);
    let cut = Cut {
        cells: cells.clone(),
        held_out: Vec::new(),
    };
    let letters = cell_letters(&cells);
    let run = prequential(&cut, &letters, &declared).expect("the prequential run");
    println!(
        "the code: the ½ tree at D = d + 2 = {receiver_depth}, n* = {n}, L_R = {GRAIN}, prequential over the passage"
    );
    coded_lines(&run.development);
    let code = &run.development.tree;

    let passage = source.passage(&cells).expect("the passage");
    let own = on_grid(&passage.code.enclosure().expect("an enclosure"));
    println!("the source's own code of the realized cells: {}", enclosure(&own, GRAIN));
    let redundancy = interval_difference(code, &total_rate).expect("a difference");
    println!("the redundancy code − n·h: {}", enclosure(&redundancy, GRAIN));
    let pointwise = interval_difference(code, &own).expect("a difference");
    println!(
        "the redundancy against the source's own code, code − code_θ(x): {}",
        enclosure(&pointwise, GRAIN)
    );

    let bound = source
        .weighting_bound(&cells, receiver_depth)
        .expect("the binary weighting bound");
    let drift = ExactInterval::point(
        &run.run.largest_residual * Rat::from_integer(BigInt::from(n)),
    );
    let total = interval_sum(&bound.total, &drift).expect("a sum");
    let visits: Vec<String> = bound.visits.iter().map(ToString::to_string).collect();
    println!(
        "the bound at D = {receiver_depth}: Γ(S′) = {} bits, boundary cells b = {}, leaf arrivals n_s = ({})",
        bound.model,
        bound.boundary,
        visits.join(", ")
    );
    println!(
        "  Σ_(n_s ≥ 1)(½ log₂ n_s + 1): {}",
        enclosure(&bound.parameters, GRAIN)
    );
    println!(
        "  the chart's certified drift n · {} (the largest per-cell residual): {} bits",
        exact(&run.run.largest_residual),
        exact(&drift.lower)
    );
    println!(
        "  the weighting bound (the ideal tree's): {}",
        enclosure(&bound.total, GRAIN)
    );
    println!(
        "  code − code_θ(x) against the ideal tree's bound: {}",
        against(&pointwise, &bound.total)
    );
    println!("  the bound in all, with the drift: {}", enclosure(&total, GRAIN));
    let leaves = truth.leaves.len() as u64;
    let log_n = log2_enclosure(&Rat::from_integer(BigInt::from(n))).expect("log₂ n");
    let half_leaves = Rat::new(BigInt::from(leaves), BigInt::from(2));
    let headline = interval_sum(
        &ExactInterval {
            lower: &log_n.lower * &half_leaves,
            upper: &log_n.upper * &half_leaves,
        },
        &point(bound.model),
    )
    .expect("a sum");
    println!(
        "  the headline ½|S|(|A| − 1) log₂ n + Γ(S′) = ½·{leaves}·16 + {}: {}",
        bound.model,
        enclosure(&headline, GRAIN)
    );
    println!(
        "  code − code_θ(x) against the bound in all: {}",
        against(&pointwise, &total)
    );

    let mut standing = Landmarks::new(declared).expect("a declared tree");
    for (position, &cell) in cells.iter().enumerate() {
        standing
            .deposit(&address(&cells, position, receiver_depth), cell)
            .expect("a deposit");
    }
    let recovery = source.recovery(&standing).expect("the recovered tree");
    let show = |leaves: &[Vec<usize>]| -> String {
        leaves
            .iter()
            .map(|leaf| format!("[{}]", leaf.iter().map(ToString::to_string).collect::<String>()))
            .collect::<Vec<_>>()
            .join(" ")
    };
    println!(
        "the recovered tree (posterior stop weight above ½ along each path of the standing after the passage):"
    );
    println!("  drawn     ({} leaves): {}", recovery.drawn.len(), show(&recovery.drawn));
    println!(
        "  minimal   ({} leaves): {} (the coarsest tree reading the same faces)",
        recovery.minimal.len(),
        show(&recovery.minimal)
    );
    println!(
        "  recovered ({} leaves): {}",
        recovery.recovered.len(),
        show(&recovery.recovered)
    );
    println!(
        "  addresses of depth {receiver_depth}: {}, unvisited {}; agreeing with the drawn tree {} (exact: {}), with the minimal tree {} (exact: {})",
        recovery.addresses,
        recovery.unvisited,
        recovery.agree,
        recovery.exact,
        recovery.agree_minimal,
        recovery.exact_minimal
    );
    println!(
        "wall (exterior): {} ms",
        started.elapsed().as_millis()
    );
}

/// The periods read one by one: the first four, then doubling, and the last whole period.
fn read_periods(periods: usize) -> Vec<usize> {
    let mut read: Vec<usize> = (0..periods.min(4)).collect();
    let mut k = 7;
    while k < periods {
        read.push(k);
        k = 2 * k + 1;
    }
    if periods > 4 && read.last() != Some(&(periods - 1)) {
        read.push(periods - 1);
    }
    read
}

/// One declared depth's passage on a moiré class (module header): the code with the baselines, the
/// code against the key description, the code of the read periods, and the code after the first
/// four periods in all and a period.
fn moire_depth(label: &str, cells: &[usize], alphabet: usize, depth: usize, period: usize, key_bits: u64) {
    let cut = Cut {
        cells: cells.to_vec(),
        held_out: Vec::new(),
    };
    let letters = cell_letters(cells);
    let declared = declaration(alphabet, depth, cells.len());
    let run = prequential(&cut, &letters, &declared).expect("the prequential run");
    println!("  {label}, D = {depth}: the passage");
    coded_lines(&run.development);
    let code = &run.development.tree;
    println!(
        "    code − the key description ({key_bits} bits): {}",
        enclosure(
            &interval_difference(code, &point(key_bits)).expect("a difference"),
            GRAIN
        )
    );
    let periods = cells.len() / period;
    let scored = |range: std::ops::Range<usize>| {
        let apart = Cut {
            cells: cells.to_vec(),
            held_out: vec![range],
        };
        let ([_, bits], _) =
            tree_prequential(&apart, &letters, &declared).expect("the scored-apart code");
        bits
    };
    println!(
        "    the code of a least period ({period} cells, {periods} whole periods), every cell scored before its own deposit:"
    );
    for k in read_periods(periods) {
        println!(
            "      period {k}: {}",
            enclosure(&scored(k * period..(k + 1) * period), GRAIN)
        );
    }
    if periods > 4 {
        let after = scored(4 * period..periods * period);
        println!(
            "      periods 4 to {}: {}",
            periods - 1,
            enclosure(&after, GRAIN)
        );
        println!(
            "        a period: {}",
            per(&after, (periods - 4) as u64, GRAIN)
        );
    }
}

/// One moiré class's receipts (module header).
fn moire_run(moire: &Moire, family: &MoireFamily) {
    let started = Instant::now();
    let truth = moire.truth(family).expect("the moiré's truth");
    let alphabet = moire.alphabet();
    let label = match moire.class() {
        MoireClass::Parity => "the parity color Σ s_i mod 2",
        MoireClass::Sheets => "the sheet tuple Σ s_i 2^i",
    };
    println!("the class: {label}, |A| = {alphabet}");
    println!(
        "  the emission's least period {} (divides the joint period); its determining depth D* = {}",
        factored(&BigUint::from(truth.least_period)),
        truth.depth
    );
    let cells = moire.emit(MOIRE_CELLS);
    let cut = Cut {
        cells: cells.clone(),
        held_out: Vec::new(),
    };
    let letters = cell_letters(&cells);
    let base = declaration(alphabet, 1, MOIRE_CELLS);
    let sweep = choose_depth_within(&cut, &letters, &base, DEEPEST).expect("the depth sweep");
    println!(
        "  the harness's depth sweep on the passage (choose_depth_within, D ≤ {DEEPEST}): chosen D = {} of {} tried (charged ⌈log₂ {}⌉ = {} bits)",
        sweep.chosen,
        sweep.tried.len(),
        sweep.tried.len(),
        sweep.description_bits
    );
    let reach = sweep.tried.len().max(truth.depth + 2);
    println!("  the code in all by depth, the sweep's depths and on to D* + 2 (a control past the sweep):");
    for depth in 1..=reach {
        let bits = match sweep.tried.iter().find(|(d, _)| *d == depth) {
            Some((_, bits)) => bits.clone(),
            None => {
                let declared = declaration(alphabet, depth, MOIRE_CELLS);
                tree_prequential(&cut, &letters, &declared)
                    .expect("the depth's code")
                    .0[0]
                    .clone()
            }
        };
        println!(
            "    D = {depth}: {}; a cell {}",
            enclosure(&bits, GRAIN),
            per(&bits, MOIRE_CELLS as u64, GRAIN)
        );
    }
    moire_depth(
        "the harness's choice",
        &cells,
        alphabet,
        sweep.chosen,
        truth.least_period,
        truth.key_bits,
    );
    moire_depth(
        "the control at the truth's determining depth D* (not a choice)",
        &cells,
        alphabet,
        truth.depth,
        truth.least_period,
        truth.key_bits,
    );
    println!("  wall (exterior): {} ms", started.elapsed().as_millis());
}

/// **`moire`** (module header).
fn moire_harness() {
    let family = MoireFamily {
        rings: MOIRE_RINGS,
        denominator: MOIRE_DENOMINATOR,
    };
    let parity =
        Moire::draw(&family, MoireClass::Parity, &mut Draw::new(SEED)).expect("a drawn moiré");
    let truth = parity.truth(&family).expect("the moiré's truth");
    println!(
        "hnn_terrain moire: {MOIRE_RINGS} gratings, denominators up to {MOIRE_DENOMINATOR} = 2^4, seed {SEED}; n = {MOIRE_CELLS} = 2^14 cells"
    );
    println!("the truth (the keys, rate p/q and phase c/q):");
    for (i, grating) in truth.gratings.iter().enumerate() {
        println!(
            "  grating {i}: rate {}/{}, phase {}/{}",
            grating.numerator(),
            grating.denominator(),
            grating.phase(),
            grating.denominator()
        );
    }
    println!(
        "  the joint period lcm(q_i): {}",
        factored(&truth.joint_period)
    );
    for lock in &truth.locks {
        let reading = match &lock.reading {
            holonics::hnn::contact::ContactLock::Unlocked => "Unlocked".to_string(),
            holonics::hnn::contact::ContactLock::Locked {
                numerator,
                denominator,
            } => format!("{numerator}/{denominator}"),
        };
        println!(
            "  pair {:?}: rate ratio {} (lock period {}, Stern–Brocot depth {}); over one joint period the windings ({}, {}) read the contact's lock {reading}",
            lock.rings,
            exact(&lock.ratio),
            lock.period,
            lock.address.depth(),
            lock.windings.0,
            lock.windings.1
        );
    }
    println!(
        "  the rate: {} bits a cell (periodic); the key space N_16^3 = {}, the key description ⌈log₂⌉ = {} bits",
        exact(&truth.rate.lower),
        factored(&truth.key_space),
        truth.key_bits
    );
    moire_run(&parity, &family);
    let sheets = Moire::new(parity.gratings().to_vec(), MoireClass::Sheets).expect("the tuple");
    moire_run(&sheets, &family);
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["tree", depth] => tree_harness(depth.parse().expect("a depth")),
        ["moire"] => moire_harness(),
        _ => println!("usage: hnn_terrain -- tree <d> | moire"),
    }
}
