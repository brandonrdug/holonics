//! **Campaign 1's exposure in the exact host reference** (rebuild step 4, #73,
//! campaign 1; design "Step 4 design: the HNN law", (d) the exposure protocol and (f) Measurement):
//! the notebook's receipt of `Reference::campaign_one().expose(&field, &cut)`, a committed command run
//! once in release, never a test.
//!
//! ```sh
//! # campaign 1's exposure: the standing real cut (THE_REBUILD Decision 23), written by standing_cut.py
//! cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all
//! cargo run --release -p holonics --example hnn_exposure -- windows 8   # the development control: a smoke
//! cargo run --release -p holonics --example hnn_exposure                # the development control at n*
//! cargo run --release -p holonics --example hnn_exposure -- cells all   # the whole public control text
//! ```
//!
//! [definition] **The standing real cut** (`cut-file <path>`) is campaign 1's exposure (Decisions 16
//! and 23): its held-out range is read from the manifest beside the cut (`<path>` with `.json`), and
//! the file's length must equal the manifest's population.
//!
//! [definition] **The development control** is `docs/plans/THE_REBUILD.md` at [`CUT_COMMIT`] as UTF-8 bytes
//! (171,754 bytes). It is read by `git show`, as `hnn_lattice_growth` reads it, never from the live
//! file.
//! - `cells N` exposes the cut's first `N` cells on campaign 1's field declared at that population
//!   (`FieldDeclaration::campaign_one(N)`: the population is the cut's length, and
//!   `Field::declare` refuses one below `n*`).
//! - The default is `N = n* = 6,148`, 3,074 windows, which `hnn_lattice_growth growth campaign 40
//!   declared` projects to `334,451 rem 8 over 40` ms at its means (the notebook README's receipt):
//!   the control at the standing cut's population.
//! - `cells all` is the whole cut: 85,877 windows, `9,343,417 rem 24 over 40` ms at those means.
//!
//! [definition; agent-inferred] **The held-out part** is the cut's tail of [`HELD_OUT`] cells. That
//! is one mean aeon of campaign 1's joint clock on uniform bytes, `⌈1,281,280/1,077⌉ = 1,190` cells
//! (design (d), "Locks"), and a whole number of receiving windows. It is declared from the field's
//! clock, not from the cut, and never tuned on held-out bits. `held-out H` declares a tail of `H`
//! cells instead. Prequential (Decision 29): its targets are compared at the standing before their
//! own deposit and then deposited, as every baseline counts them after scoring; "held out" means
//! that no design choice was made on them, and no crib reads them (review D1).
//!
//! [definition] **The deadline** `windows K` ends the reading after `K` receiving windows
//! (`Reference::with_deadline`). The cut is still the whole declared population, so the `n*` guard
//! holds, and the run is reported incomplete at the cell it stopped at: a smoke, or a run cut short
//! at its deadline.
//!
//! [definition] **The realization** `realization <host|card>` (default `host`): the same exposure
//! protocol (`holonics::hnn::reference::expose`) through the host reference, or through the device
//! port resident on the card (`holonics_cuda::hnn::Resident`, rebuild step 5, Decision 25), whose
//! every return is the reference's. `holonics` does not depend on the device crate, so this file is
//! also an example of `holonics-cuda`, whose build declares `cfg(holonics_card)`; `realization card`
//! runs only there:
//!
//! ```sh
//! cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all realization card
//! ```
//!
//! The card's readout is the host's line for line but for the realization's line, the wall times
//! and, beside them, what crossed the bus (`holonics_cuda::hnn::Traffic`).
//!
//! [established-bounded; measured] **The readout** is the complete `Exposure`, with every quantity
//! design (f) names:
//! - the executed word (Decision 24): the declared precisions, the charts' refinements (their starts,
//!   the rounded Newton–Schulz steps, the largest certificate against the target), the remainders
//!   the words and their returns released, and the tick balances' residuals against their bounds;
//! - the bits on the training and the held-out targets against each online baseline (uniform,
//!   order-0 and order-1 Krichevsky–Trofimov, PPM of order 2), and the verdict against order-0;
//!   beside the model's, the landmark tree's face alone (Decision 28: the receiving parametron's
//!   tree at each cell's causal address read at the grain, no wave, at the model's constitution and
//!   address; the compare's receipt), each baseline against it, and the model against it: the
//!   wave's contribution;
//! - `Kt` with the published keys, against the literal over the cells read;
//! - each key location with its fibres per ring;
//! - each aeon's boundary: its length and lift points, readings, collapse, first law (exchange plus
//!   deposition, telescoping to the change of code length), and the face against the literal;
//! - the state and constitution bits against the source, with and without the collapse;
//! - the constitution's curve, one point per commit;
//! - the budget stop or deadline, the work counted, and the wall time: the exposure's, and the
//!   host's by phase (`Exposure::wall`: refine read, release, compare read, tree read, holon and
//!   covector, `pull_back`, `compose`, `deposited`, re-read and ingest), with the rest of the
//!   exposure, and the host's tree read per window against the word's (the refine read, the word
//!   executed and read: on the card, the card's word with its host readout).
//!
//! [definition] **Every reading is exact; no decimal is printed** (a decimal is a collapse, CLAUDE.md's
//! exact-arithmetic law). Integers print as integers and rationals as `n/d` (`n/2^e` or
//! `n/(2^e·m)` on a wide denominator with a power-of-two factor).
//! - Bits are enclosures with exact endpoints, each also read at the receiver's grain
//!   `L_R = ⌈1/ε_bits⌉` (16 in campaign 1) through `GrainCell::of`: `n + k/L_R + ε`, the carry
//!   `n`, the phase class `k` and the exact fibre `0 ≤ ε < 1/L_R`. Bits a cell are the exact
//!   ratios, read the same way.
//! - A comparison is the exact ordering of two enclosures with their exact difference, an
//!   enclosure `[a.lower − b.upper, a.upper − b.lower]`, read at the grain; a certificate or a
//!   residual is ordered against its bound with the exact margin.
//! - A ratio (bits per source bit) is reduced, with its integer quotient and remainder.
//! - Wall time is an exterior face in integer milliseconds; a per-window mean is the integer
//!   quotient with its remainder over the windows (`q rem r over N`).

// `cfg(holonics_card)` is declared by `holonics-cuda`'s build only (module header).
#![allow(unexpected_cfgs)]

#[path = "exterior.rs"]
mod exterior;

use std::fmt::Display;
use std::time::Instant;

use holonics::aeon::{EnclosedBalance, LiteralComparison};
use holonics::compression::cost::ceil_log2;
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::port::{ExecutionPort, ReceiptDetail};
use holonics::hnn::reference::{Bits, KeyReport, PPM_ORDER};
use holonics::hnn::{AeonBoundary, Cut, Exposure, Field, FieldDeclaration, Reference, Steps};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::reception::Component;
use num_bigint::{BigInt, BigUint};
use num_traits::One;

use exterior::{
    against, difference, enclosure, exact, per, ratio, read_cut, reading, receiver_grain,
};

/// **The pinned campaign cut**: the commit whose `docs/plans/THE_REBUILD.md` is the campaign
/// field's cut (as `hnn_lattice_growth`).
const CUT_COMMIT: &str = "fed5488ce70eb5ffbc90f2f03d23638be9d69189";
const CUT_PATH: &str = "docs/plans/THE_REBUILD.md";

/// [agent-inferred] **The declared held-out tail**: one mean aeon of the joint clock on uniform
/// bytes, `⌈5·7·11·13·256 / (52 + 5·37 + 35·24)⌉ = ⌈1,281,280/1,077⌉` cells (module header).
const HELD_OUT: usize = 1_190;

/// The pinned cut's bytes, read from the repository's history at [`CUT_COMMIT`]. The notebook's
/// exterior boundary reads it (guard 7 bans a file or a process inside the machinery, never at an
/// exterior reader).
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn pinned_cut() -> Vec<u8> {
    let output = std::process::Command::new("git")
        .args(["show", &format!("{CUT_COMMIT}:{CUT_PATH}")])
        .output()
        .expect("run from the repository: git show reads the pinned cut");
    assert!(output.status.success(), "git show {CUT_COMMIT}:{CUT_PATH}");
    output.stdout
}

/// Where an exact value lies against its bound, with the exact margin `bound − value`.
fn within(value: &Rat, bound: &Rat) -> String {
    let side = if value <= bound {
        "at or below"
    } else {
        "ABOVE"
    };
    format!("{side} it (bound − value = {})", exact(&(bound - value)))
}

/// A per-window mean of a whole count: its integer quotient and remainder, `q rem r over N`.
fn mean(total: u128, count: u128) -> String {
    if count == 0 {
        return "-".to_string();
    }
    format!("{} rem {} over {count}", total / count, total % count)
}

/// Entry `g` of a per-ring vector, or `-` where the report has none.
fn at<T: Display>(values: &[T], g: usize) -> String {
    values.get(g).map_or_else(|| "-".to_string(), T::to_string)
}

fn component<T>(value: &Component<T>, present: impl Fn(&T) -> String) -> String {
    match value {
        Component::Present(value) => present(value),
        Component::Absent(reason) => format!("absent: {reason}"),
    }
}

// -------------------------------------------------------------------------------------------
// the run

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let (mut cells, mut held_out, mut deadline): (Option<String>, usize, Option<u64>) =
        (None, HELD_OUT, None);
    let mut cut_file: Option<String> = None;
    let mut realization = String::from("host");
    for pair in arguments.chunks(2) {
        match pair {
            [key, value] if key == "cells" => cells = Some(value.clone()),
            [key, value] if key == "held-out" => {
                held_out = value.parse().expect("a held-out tail in cells");
            }
            [key, value] if key == "cut-file" => cut_file = Some(value.clone()),
            [key, value] if key == "windows" => {
                deadline = Some(value.parse().expect("a deadline in windows"));
            }
            [key, value] if key == "realization" && (value == "host" || value == "card") => {
                realization = value.clone();
            }
            _ => {
                println!(
                    "usage: hnn_exposure [cut-file <path>] [cells <N|all>] [held-out <cells>] [windows <deadline>] [realization <host|card>]"
                );
                return;
            }
        }
    }

    let setup = Instant::now();
    let (text, source) = match cut_file.as_deref() {
        Some(path) => {
            let (text, _, range) = read_cut(path);
            held_out = range.end - range.start;
            (
                text,
                format!("the cut file {path} (held out {range:?} from its manifest)"),
            )
        }
        None => (pinned_cut(), format!("{CUT_COMMIT}:{CUT_PATH}")),
    };
    let n_star = Field::declare(FieldDeclaration::campaign_one(text.len() as u64))
        .expect("campaign 1's declared field over the whole cut")
        .capacity()
        .n_star() as usize;
    let length = match cells.as_deref() {
        None => n_star,
        Some("all") => text.len(),
        Some(count) => count.parse().expect("a cell count, or all"),
    };
    assert!(
        length <= text.len(),
        "the pinned cut has {} cells",
        text.len()
    );
    let field = Field::declare(FieldDeclaration::campaign_one(length as u64))
        .expect("campaign 1's declared field (refused below n*)");
    let tail = length.saturating_sub(held_out)..length;
    let cut = Cut {
        cells: text[..length]
            .iter()
            .map(|&byte| usize::from(byte))
            .collect(),
        held_out: vec![tail.clone()],
    };
    let reference = match deadline {
        Some(windows) => Reference::campaign_one().with_deadline(windows),
        None => Reference::campaign_one(),
    };
    let setup = setup.elapsed().as_millis();

    let aperture = field.receivers()[0].aperture;
    let steps = Steps::campaign_one();
    println!("hnn_exposure: campaign 1's declared field over {source}");
    println!(
        "cut: the first {length} of the pinned cut's {} bytes (the declared population; n* = {n_star}); {} receiving windows of A = {aperture} cells",
        text.len(),
        length.div_ceil(aperture)
    );
    println!(
        "held out: cells {}..{} ({} cells, the declared tail); training: cells 0..{}",
        tail.start,
        tail.end,
        tail.len(),
        tail.start
    );
    println!(
        "reference: campaign 1 (gamma_U = {}, eta_x = {}, B_Theta = 2^{} bits, pending capacity {}); deadline: {}",
        exact(&steps.proxy),
        exact(&steps.factor),
        CAMPAIGN_ONE_BUDGET.trailing_zeros(),
        reference.census().pending_capacity,
        deadline.map_or("none".to_string(), |windows| format!("{windows} windows"))
    );
    println!(
        "carrier lattices L: {}",
        field
            .lattices()
            .iter()
            .map(|(locus, lattice)| format!("{locus:?} {}", lattice.exponent()))
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!("setup (cut read, fields declared): {setup} ms wall");

    if realization == "card" {
        println!("realization: {}", card_realization());
    } else {
        println!("realization: the host reference (holonics::hnn::Reference)");
    }
    let clock = Instant::now();
    let (exposure, traffic) = if realization == "card" {
        card_exposure(deadline, &field, &cut)
    } else {
        (reference.expose(&field, &cut).expect("the exposure"), None)
    };
    let wall = clock.elapsed().as_millis();
    report(&field, &exposure);
    println!();
    phases(&exposure, wall);
    if let Some(traffic) = traffic {
        println!("{traffic}");
    }
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; exposure {wall} ms over {} windows (per window {}, in ms)",
        exposure.compares,
        mean(wall, u128::from(exposure.compares))
    );
}

/// The card the device port runs on: its name and capability, read off its census.
#[cfg(holonics_card)]
fn card_realization() -> String {
    let card =
        holonics_cuda::hnn::Card::open(0).expect("a CUDA card at ordinal 0 with its kernels");
    let census = card.census();
    format!(
        "the device port resident on the card (holonics_cuda::hnn::Resident) on {} (compute {}.{}, {} multiprocessors)",
        census.name,
        census.compute_capability.0,
        census.compute_capability.1,
        census.multiprocessors
    )
}

#[cfg(not(holonics_card))]
fn card_realization() -> String {
    panic!(
        "realization card runs as the device crate's example: cargo run --release -p holonics-cuda --example hnn_exposure -- … realization card"
    )
}

/// **Campaign 1's exposure on the card** (`holonics_cuda::hnn::Resident::expose`, the reference's
/// protocol over the device port), with what crossed the bus beside it (exterior).
#[cfg(holonics_card)]
fn card_exposure(deadline: Option<u64>, field: &Field, cut: &Cut) -> (Exposure, Option<String>) {
    let card =
        holonics_cuda::hnn::Card::open(0).expect("a CUDA card at ordinal 0 with its kernels");
    let port = holonics_cuda::hnn::Resident::campaign_one(&card);
    let port = match deadline {
        Some(windows) => port.with_deadline(windows),
        None => port,
    };
    let exposure = port.expose(field, cut).expect("the exposure on the card");
    let traffic = port.traffic();
    let windows = u128::from(exposure.compares);
    let per_window = |octets: u64| mean(u128::from(octets), windows);
    let realized = port.word_layouts().map_or_else(
        || "no word ran".to_string(),
        |(forward, reverse)| {
            format!(
                "the word {:?} (grid {}, block {}), its return {:?} (grid {}, block {})",
                forward.realization,
                forward.grid.x,
                forward.block.x,
                reverse.realization,
                reverse.grid.x,
                reverse.block.x
            )
        },
    );
    let line = format!(
        "== across the bus (exterior: octets, both directions; per window as quotient rem remainder over {} windows) ==\n\
         words (plans, operands, records, certificates, moved charts): {} ({} a window, {} words)\n\
         returns (carried reads and records): {} ({} a window, {} returns)\n\
         publications (the loci's moved words): {} ({} a window)\n\
         ingests (cells and receipts): {} ({} a window)\n\
         realization (the hardware law's report): {realized}",
        exposure.compares,
        traffic.words,
        per_window(traffic.words),
        traffic.word_count,
        traffic.returns,
        per_window(traffic.returns),
        traffic.return_count,
        traffic.publications,
        per_window(traffic.publications),
        traffic.ingest,
        per_window(traffic.ingest)
    );
    (exposure, Some(line))
}

#[cfg(not(holonics_card))]
fn card_exposure(_: Option<u64>, _: &Field, _: &Cut) -> (Exposure, Option<String>) {
    unreachable!("card_realization refused first")
}

/// **The wall time by phase** (`Exposure::wall`, exterior): each phase's milliseconds over the run
/// and per receiving window (the integer quotient with its remainder over the windows), the phases'
/// sum, and the rest of the exposure's wall time (key location, the aeon boundaries, the baselines
/// and the bookkeeping).
fn phases(exposure: &Exposure, wall: u128) {
    let windows = u128::from(exposure.compares);
    println!(
        "== wall time by phase (exterior: the host's wall clock, milliseconds; per window as quotient rem remainder over {} windows) ==",
        exposure.compares
    );
    println!("{:<20}\t{:>10}\t{:>12}", "phase", "total ms", "per window");
    let row = |name: &str, ms: u128| {
        let per = match (ms.checked_div(windows), ms.checked_rem(windows)) {
            (Some(quotient), Some(remainder)) => format!("{quotient} rem {remainder}"),
            _ => "-".to_string(),
        };
        println!("{name:<20}\t{ms:>10}\t{per:>12}");
    };
    for (name, time) in exposure.wall.phases() {
        row(name, time.as_millis());
    }
    let sum = exposure.wall.total().as_millis();
    row("phases' sum", sum);
    row("rest of exposure", wall.saturating_sub(sum));
    // The host's tree read against the word, per window in microseconds (Decision 28: the tree's
    // card port is a #76 debt only if its read is not small against the word).
    let micros = |time: std::time::Duration| time.as_micros();
    let (tree, word) = (
        micros(exposure.wall.tree_read),
        micros(exposure.wall.refine_read),
    );
    println!(
        "the host's tree read per window: {} us; the word (refine read) per window: {} us; tree read over word: {}",
        mean(tree, windows),
        mean(word, windows),
        if word == 0 {
            "-".to_string()
        } else {
            format!("{} rem {} over {word}", tree / word, tree % word)
        }
    );
}

// -------------------------------------------------------------------------------------------
// the readout

/// **The complete readout** of an exposure (design (f)).
fn report(field: &Field, exposure: &Exposure) {
    println!();
    println!("== the run ==");
    let state = if exposure.complete {
        "complete: the whole cut read, no budget stop".to_string()
    } else {
        let mut causes = Vec::new();
        if let Some((stop, cell)) = &exposure.stop {
            causes.push(format!(
                "budget stop at cell {cell}: the successor's {} bits exceed B_Theta = {}; commit {} stays published; the loci that grew most: {:?}",
                stop.bits, stop.budget, stop.commit, stop.loci
            ));
        }
        if let Some(cell) = exposure.deadline {
            causes.push(format!("deadline reached at cell {cell}"));
        }
        format!("INCOMPLETE: {}", causes.join("; "))
    };
    println!("{state}");
    println!(
        "receiving windows read: {} (compares {}, deposits {}); the source-to-receiver path open at the cut of {} of the {} windows; peak bits of the change inside a word: {}",
        exposure.windows,
        exposure.compares,
        exposure.deposits,
        exposure.open_windows,
        exposure.windows,
        exposure.peak_word_bits
    );

    println!();
    println!("== the executed word (Decision 24) ==");
    match field.word_lattice() {
        Some(lattice) => println!(
            "declared precisions: charts on 2^-{}Z, certificate target 2^-{}, transients on 2^-{}Z",
            lattice.chart_exponent(),
            lattice.target_exponent(),
            lattice.transient_exponent()
        ),
        None => println!("declared precisions: none (the exact law)"),
    }
    let word = &exposure.word;
    println!(
        "charts: {} refinements read ({} cold from the scaled transpose, {} from one exact inverse, {} rounded Newton-Schulz steps); the largest certificate ||1 - A X||_inf = {} against the target {}: {}",
        word.charts.reads,
        word.charts.cold,
        word.charts.seeded,
        word.charts.steps,
        exact(&word.charts.largest),
        exact(&word.charts.target),
        within(&word.charts.largest, &word.charts.target)
    );
    for (label, released) in [
        ("the words' released remainders (forward)", &word.forward),
        ("the returns' released remainders (adjoint)", &word.adjoint),
    ] {
        println!(
            "{label}: {} nonzero, the largest {}, l1 sum {}, {} exact bits",
            released.entries,
            exact(&released.largest),
            exact(&released.total),
            released.bits
        );
    }
    println!(
        "tick balances: {} read, every one closed up to its residual within its certified bound: {}; the largest residual {} against its bound {}: {}",
        word.balances,
        word.closed,
        exact(&word.largest_residual),
        exact(&word.residual_bound),
        within(&word.largest_residual, &word.residual_bound)
    );

    let grain = receiver_grain(field);
    println!();
    println!(
        "== bits against the baselines (online, on the same stream; read at the receiver's grain L_R = {grain} as n + k/{grain} + ε: carry n, phase class k, fibre 0 ≤ ε < 1/{grain}) =="
    );
    bits("training", &exposure.training, false, grain);
    bits("held out", &exposure.held_out, true, grain);
    match &exposure.mixture {
        Some(mixture) => println!(
            "the receiver's mixture at the end (ruling A): log2 beta {} (beta = W_tree/W_combined), carried at W = {}, {} rebases, certified drift {} bits",
            enclosure(&mixture.log2_beta, grain),
            mixture.width,
            mixture.rebases,
            exact(&mixture.drift)
        ),
        None => println!("the receiver's mixture: none"),
    }

    println!();
    println!("== cost against the literal ==");
    let work_bits = ceil_log2(&exposure.work.entries_written.clone().max(BigUint::one()));
    println!(
        "Kt = |Field::describe| {} + located keys {} + L_target|model + ceil(log2 ExactWork) {} = {}",
        exposure.description_bits,
        exposure.key_bits,
        work_bits,
        enclosure(&exposure.kt, grain)
    );
    let literal = ExactInterval::point(Rat::from_integer(BigInt::from(exposure.literal_bits)));
    println!(
        "literal ceil(log2|A|)·n over the cells read: {} bits; Kt is {} the literal{}; Kt − literal: {}",
        exposure.literal_bits,
        against(&exposure.kt, &literal),
        if exposure.kt.upper < literal.lower {
            " (the pivot pays off)"
        } else {
            ""
        },
        difference(&exposure.kt, &literal, grain)
    );

    println!();
    println!(
        "== key locations ({}, on the crib that closed each aeon) ==",
        exposure.keys.len()
    );
    for report in &exposure.keys {
        keys(field, report);
    }

    println!();
    println!(
        "== aeons ({} boundaries at the joint clock's carry-out) ==",
        exposure.aeons.len()
    );
    for (index, boundary) in exposure.aeons.iter().enumerate() {
        aeon(index, boundary, grain);
    }

    println!();
    println!("== state against the source ==");
    let state = &exposure.state;
    let over_source = |bits: u64| {
        if state.source_bits == 0 {
            "-".to_string()
        } else {
            ratio(&Rat::new(
                BigInt::from(bits),
                BigInt::from(state.source_bits),
            ))
        }
    };
    println!(
        "source: {} bits ({} cells ingested, n* = {})",
        state.source_bits,
        state.source_bits / ceil_log2(&BigUint::from(field.alphabet())).max(1),
        state.n_star
    );
    println!("lift point: {} bits", state.lift_bits);
    println!(
        "moment: dense {} bits, per source bit {}; counted state ceil(log2 N(n)) {} bits, per source bit {}",
        state.moment_bits,
        over_source(state.moment_bits),
        state.moment_state_bits,
        over_source(state.moment_state_bits)
    );
    println!(
        "constitution: {} bits, per source bit {}",
        state.constitution_bits,
        over_source(state.constitution_bits)
    );
    println!(
        "resident: {} bits with the collapse, per source bit {}; {} bits without it, per source bit {}",
        state.resident_bits,
        over_source(state.resident_bits),
        state.resident_bits_without_collapse,
        over_source(state.resident_bits_without_collapse)
    );

    println!();
    println!(
        "== the constitution's curve ({} points, one per published commit) ==",
        exposure.constitution_curve.len()
    );
    println!("commit\tbits\tentries\tremainders\tsolved\treleased_bits\tstepped");
    for point in &exposure.constitution_curve {
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}",
            point.commit,
            point.bits.total(),
            point.bits.entries,
            point.bits.remainders,
            point.bits.solved,
            point.released_bits,
            point.stepped
        );
    }

    println!();
    println!("== work counted (ExactWork, over every refine, compare and deposit) ==");
    let work = &exposure.work;
    println!(
        "additions {}; multiplications {}; divisions {}; entries written {}; cumulative bits {}; peak bits {}; resident entries {}; dependency span {}",
        work.additions,
        work.multiplications,
        work.divisions,
        work.entries_written,
        work.cumulative_bits,
        work.peak_bits,
        work.resident_entries,
        work.dependency_span
    );
    println!(
        "unknown (no receiver counted them): energy in joules, device power, bits per joule, occupancy"
    );
}

/// One population's bits against the baselines, each comparison with its exact difference, and the
/// verdict against online order-0: on the held-out targets, the campaign's criterion (design (f):
/// not beating it is a failure).
fn bits(label: &str, bits: &Bits, criterion: bool, grain: u64) {
    println!("{label}: {} targets", bits.cells);
    if bits.cells == 0 {
        println!("  no targets read");
        return;
    }
    let ppm = format!("PPM order {PPM_ORDER}");
    let rows = [
        ("model q", &bits.model),
        ("tree face", &bits.tree),
        ("combined", &bits.combined),
        ("uniform", &bits.uniform),
        ("order-0 KT", &bits.order_zero),
        ("order-1 KT", &bits.order_one),
        (ppm.as_str(), &bits.ppm),
    ];
    for (name, interval) in rows {
        println!(
            "  {name:<11} {}; per cell at L_R = {grain}: {}",
            enclosure(interval, grain),
            per(interval, bits.cells, grain)
        );
    }
    for (name, baseline) in &rows[1..] {
        println!(
            "  the model is {} {name}; model − {name}: {}",
            against(&bits.model, baseline),
            difference(&bits.model, baseline, grain)
        );
    }
    for (name, baseline) in &rows[3..] {
        println!(
            "  the tree face alone is {} {name}; tree − {name}: {}",
            against(&bits.tree, baseline),
            difference(&bits.tree, baseline, grain)
        );
    }
    println!(
        "  the combined face (tree + wave) is {} the tree face; combined − tree: {}",
        against(&bits.combined, &bits.tree),
        difference(&bits.combined, &bits.tree, grain)
    );
    println!(
        "  against online order-0: {}",
        match (against(&bits.model, &bits.order_zero), criterion) {
            ("below", _) => "the model beats it",
            ("above", true) => "FAILURE: the model does not beat it (design (f))",
            ("above", false) => "the model does not beat it",
            _ => "undecided: the enclosures overlap",
        }
    );
    println!(
        "  the wave's contribution (the combined face against the tree face alone): {}",
        match against(&bits.combined, &bits.tree) {
            "below" => "the wave lowers the code length",
            "above" => "the wave raises the code length",
            _ => "undecided: the enclosures overlap",
        }
    );
    println!(
        "  the mixture (ruling A: the model against the tree face alone): {}",
        match against(&bits.model, &bits.tree) {
            "below" => "the mixture codes below the tree",
            "above" => "the mixture codes above the tree",
            _ => "undecided: the enclosures overlap",
        }
    );
}

/// One key location: per ring, its fibre, orbits, publication or fallback, failing loop,
/// candidates, propagation work and re-keying jump.
fn keys(field: &Field, report: &KeyReport) {
    let ReceiptDetail::Keys {
        fibres,
        orbits,
        fell_back,
        failing_loops,
        candidates,
        work,
        jumps,
    } = &report.detail
    else {
        println!("at cell {}: {:?}", report.cell, report.detail);
        return;
    };
    println!("at cell {}:", report.cell);
    for (g, ring) in field.rings().iter().enumerate() {
        let publication = match fell_back.get(g) {
            Some(true) => "fell back",
            Some(false) => "published",
            None => "-",
        };
        let failing = match failing_loops.get(g) {
            Some(Some(cycle)) => format!("{cycle:?}"),
            Some(None) => "none".to_string(),
            None => "-".to_string(),
        };
        println!(
            "  ring {g} (d = {}): fibre {} in {} orbits, {publication}; failing loop {failing}; candidates {}; propagation work {}; re-keying jump {}",
            ring.period(),
            at(fibres, g),
            at(orbits, g),
            at(candidates, g),
            at(work, g),
            at(jumps, g)
        );
    }
}

/// One aeon boundary: its length, lift points, readings, collapse, first law and the face against
/// the literal.
fn aeon(index: usize, boundary: &AeonBoundary, grain: u64) {
    println!("aeon {index}: {} cells", boundary.cells);
    let lift = |points: &[BigInt]| {
        points
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    };
    println!(
        "  lift point: opening ({}), carry-out ({})",
        lift(&boundary.opening),
        lift(&boundary.carry_out)
    );
    println!(
        "  readings per ring (windings + open phase, in turns): {}",
        boundary
            .readings
            .iter()
            .map(|reading| format!("{} + {}", reading.windings(), exact(reading.phase())))
            .collect::<Vec<_>>()
            .join("; ")
    );
    println!("  epochs per ring: {}", lift(&boundary.epochs));
    println!(
        "  closing on the last ring's clock: {}",
        component(&boundary.closing, |reading| format!(
            "a cycle of {} whole windings",
            reading.windings()
        ))
    );
    let collapse = &boundary.collapse;
    println!(
        "  collapse onto {} admitted receivers: retained {} loci, released {:?} ({} of {} entries, {} carried remainders); constitution bits {} -> {}",
        boundary.admitted.len(),
        collapse.retained.len(),
        collapse.released,
        collapse.released_entries,
        collapse.total_entries,
        collapse.released_remainders.len(),
        collapse.bits[0],
        collapse.bits[1]
    );
    println!(
        "  value kernel: {}; view: {}",
        component(&boundary.value_kernel, |()| "present".to_string()),
        component(&boundary.view, |counts| format!("{} counts", counts.len()))
    );
    println!(
        "  pending ratios carried {}, refused {}; staged deposits refused {}; state bits {} -> {}",
        boundary.carried.len(),
        boundary.refused.len(),
        boundary.refused_staged.len(),
        boundary.state_bits[0],
        boundary.state_bits[1]
    );
    first_law(&boundary.first_law, grain);
    literal(&boundary.literal, grain);
}

/// The first law over the aeon: exchange plus deposition, telescoping to its change of code length.
fn first_law(law: &EnclosedBalance, grain: u64) {
    let (total, change) = (law.total(), law.change());
    let telescopes = total.lower == &change.lower - &law.widening
        && total.upper == &change.upper + &law.widening;
    let enclosed = |interval: &ExactInterval| enclosure(interval, grain);
    println!(
        "  first law: {} arrivals over {} cells; {} exchange steps, {} deposition steps",
        law.arrivals, law.cells, law.exchanges, law.depositions
    );
    println!("    exchange   {}", enclosed(&law.exchange));
    println!("    deposition {}", enclosed(&law.deposition));
    println!("    total      {}", enclosed(&total));
    println!(
        "    change C(closing) - C(opening) {}; widening {} bits (at L_R = {grain}: {})",
        enclosed(&change),
        exact(&law.widening),
        reading(&law.widening, grain)
    );
    println!(
        "    opening {}; closing {}",
        law.opening.as_ref().map_or("-".to_string(), enclosed),
        law.closing.as_ref().map_or("-".to_string(), enclosed)
    );
    println!("    telescopes exactly (total = change widened by the widening): {telescopes}");
}

/// The face against the literal over the aeon: `Σ ℓ + Σ g = n·log₂|A|`.
fn literal(face: &LiteralComparison, grain: u64) {
    let balances = face.code.lower.clone() + &face.gain.upper == face.literal.upper
        && face.code.upper.clone() + &face.gain.lower == face.literal.lower;
    println!(
        "  the face against the literal over {} cells (a reading, not a budget):",
        face.cells
    );
    println!("    code (sum of l)  {}", enclosure(&face.code, grain));
    println!("    gain (sum of g)  {}", enclosure(&face.gain, grain));
    println!("    literal n·log2|A| {}", enclosure(&face.literal, grain));
    println!("    code + gain = literal on the enclosures' endpoints: {balances}");
}
