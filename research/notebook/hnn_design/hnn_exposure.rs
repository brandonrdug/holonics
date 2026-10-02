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
//! and 23): its held-out range is the manifest's `held_out_range` itself (the manifest beside the
//! cut, `<path>` with `.json`), the file's length must equal the manifest's population, and the
//! cells read must close at the range's end (`cells all`), so the range is the cut's own.
//!
//! [definition] **The development control** is `docs/plans/THE_REBUILD.md` at [`CUT_COMMIT`] as UTF-8 bytes
//! (171,754 bytes). It is read by `git show`, never from the live file.
//! - `cells N` exposes the cut's first `N` cells on campaign 1's field declared at that population
//!   (`FieldDeclaration::campaign_one(N)`: the population is the cut's length, and
//!   `Field::declare` refuses one below `n*`).
//! - The default is `N = n* = 6,148`, 3,074 windows, which the retired `hnn_lattice_growth growth
//!   campaign 40 declared` projected to `334,451 rem 8 over 40` ms at its means (the notebook
//!   README's receipt):
//!   the control at the standing cut's population.
//! - `cells all` is the whole cut: 85,877 windows, `9,343,417 rem 24 over 40` ms at those means.
//!
//! [definition; agent-inferred] **The held-out part** of the pinned cut is its tail of [`HELD_OUT`]
//! cells. That is one mean aeon of campaign 1's joint clock on uniform bytes,
//! `⌈1,281,280/1,077⌉ = 1,190` cells (design (d), "Locks"), and a whole number of receiving
//! windows. It is declared from the field's clock, not from the cut, and never tuned on held-out
//! bits; `held-out H` declares a tail of `H` cells instead. A cut file's is its manifest's range
//! (above). Prequential (Decision 29): its targets are compared at the standing before their
//! own deposit and then deposited, as every baseline counts them after scoring; "held out" means
//! their score precedes their own deposit. This development cut has been reused for design;
//! the separate evaluation partition remains unspent. A crib reads only cells already scored.
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
//! Decision 38 adds `resonator source`: one predeclared loaded resonator on source ring 0,
//! with its unit parametron's C/K, the campaign's passive rate D=I/4, no pump and all scalar
//! amplitudes initially 1. `resonator none` is the default. Both paths use the same exposure
//! protocol and charge the initial material declaration.
//!
//! The card's readout is the host's line for line but for the realization's line, the wall times
//! and, beside them, what crossed the bus (`holonics_cuda::hnn::Traffic`).
//!
//! [definition; agent-inferred] **F2's adoption gate** (`gate f2`; THE_REBUILD F2, the pins of
//! September 28): after the exposure, the same cells it scored are read once more by the
//! population over the tree alone, one family at prior one (`PortPopulation::new(&[0])`), its faces
//! the receiver's tree's executed faces at the same causal addresses (`Landmarks::receive` over the
//! cell letters), each scored before its own deposit. The gate block prints the charged code of the
//! held-out (validation) cells with the field (the receiver's population, the tree and `q_C` at
//! `½/½`, the exposure's model) and without it, whether the first is strictly shorter on the
//! enclosures, the two readings of the tree against each other, the whole-passage telescopes, the
//! field's own face, the posterior at the join and at the end, work and memory with and without
//! (the field's part separately), and the budgets: the probe passage (ten minutes, 20 GB), the warm
//! response (60 s for the declared validation passage's longest agent response, at the run's mean a
//! window) and the declared validation passage (ten minutes, at the same mean), the last two read
//! from the cut's manifest (`declared_validation_cells`, `longest_agent_response`, written by
//! `f2_capacity_probe.py`, retired September 30 and at commit `d4596102`). The card's memory is read
//! outside the process.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_exposure -- held-out 6132 windows 16 gate f2   # the smoke, public
//! cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/f2v2-gate-probe.bin cells all realization card gate f2
//! ```
//!
//! [established-bounded; measured] **The readout** is the complete `Exposure`, with every quantity
//! design (f) names:
//! - the executed word (Decision 24): the declared precisions, the charts' refinements (their starts,
//!   the rounded Newton–Schulz steps, the largest certificate against the target), the remainders
//!   the words and their returns released, the tick balances' residuals against their bounds, and
//!   every word's whole balance carried across its commit (campaign 2: the count, whether every
//!   one closed, the largest residual, the resonators' chart and split included, against its
//!   bound, the deposition work and the interconnection's defect, which is zero by construction
//!   for a loaded port); with `resonator source`, the final gain amplitudes and their carried
//!   remainders;
//! - the bits on the training and the held-out targets against each online baseline (uniform,
//!   order-0 and order-1 Krichevsky–Trofimov, PPM of order 2), and the verdict against order-0;
//!   the model's face is the mixture of the tree's face and the combined face (the primary's ruling
//!   A); beside it, the landmark tree's executed face alone (Decision 28: the receiving parametron's
//!   tree at each cell's causal address, at the standing after every earlier cell, no wave: the face
//!   `q_T` the mixture weighs; the compare's receipt), the same tree's face at the grain (its grain
//!   logits alone, the face the combined read opens at when the wave reads zero) and the combined
//!   face alone (tree plus wave); each baseline against them, `L_C − L_T` (the wave's contribution
//!   against the tree's executed face, the population's log-odds) and `L_model − L_T` (what the
//!   receiver's population keeps of it), the tree at the grain against the tree (the grain's
//!   rounding), the course by aeon, and the population's end (its telescoped code, each family's
//!   code and their log-odds; THE_REBUILD U1);
//! - `Kt` with the published keys, against the literal over the cells read;
//! - each key location with its fibres per ring;
//! - each aeon's boundary: its length and lift points, readings, collapse, first law (exchange plus
//!   deposition, telescoping to the change of code length), and the face against the literal;
//! - the state and constitution bits against the source, with and without the collapse;
//! - the constitution's curve, one point per commit, with the contact-kind census over its commits
//!   (campaign 2: each contact's kinds, the five proved cases, and its modes by kind);
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
use holonics::compression::landmark::context::baseline::PPM_ORDER;
use holonics::compression::landmark::context::{Landmarks, cell_letters, letter_address};
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::port::{ExecutionPort, ReceiptDetail};
use holonics::hnn::receiving::landmark_declaration;
use holonics::hnn::reference::{Bits, KeyReport};
use holonics::hnn::{
    AeonBoundary, Constitution, Cut, Exposure, Field, FieldDeclaration, Reference,
    ResonatorMaterial,
};
use holonics::ratio::algebraic::{ExactInterval, interval_sum};
use holonics::ratio::{Rat, rat};
use holonics::receiver::population::PortPopulation;
use holonics::receiver::reception::Component;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use exterior::{
    against, difference, enclosure, exact, manifest_number, per, ratio, read_cut, reading,
    receiver_grain,
};

/// **The pinned campaign cut**: the commit whose `docs/plans/THE_REBUILD.md` is the campaign
/// field's cut.
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
    let arguments: Vec<String> = exterior::admit_reserve_flag(std::env::args().skip(1).collect());
    let (mut cells, mut held_out, mut deadline): (Option<String>, Option<usize>, Option<u64>) =
        (None, None, None);
    let mut cut_file: Option<String> = None;
    let mut realization = String::from("host");
    let mut loaded = false;
    let mut gate = false;
    let mut ablation: Option<usize> = None;
    let mut information = 0usize;
    let mut descent = false;
    let mut samples_out: Option<String> = None;
    for pair in arguments.chunks(2) {
        match pair {
            [key, value] if key == "cells" => cells = Some(value.clone()),
            [key, value] if key == "held-out" => {
                held_out = Some(value.parse().expect("a held-out tail in cells"));
            }
            [key, value] if key == "cut-file" => cut_file = Some(value.clone()),
            [key, value] if key == "resonator" && (value == "source" || value == "none") => {
                loaded = value == "source";
            }
            [key, value] if key == "windows" => {
                deadline = Some(value.parse().expect("a deadline in windows"));
            }
            [key, value] if key == "realization" && (value == "host" || value == "card") => {
                realization = value.clone();
            }
            [key, value] if key == "gate" && value == "f2" => gate = true,
            [key, value] if key == "ablation" => {
                ablation = Some(value.parse().expect("a count of windows"));
            }
            [key, value] if key == "information" => {
                information = value.parse().expect("a count of frozen windows");
            }
            [key, value] if key == "descent" => descent = value == "on",
            [key, value] if key == "samples" => samples_out = Some(value.clone()),
            _ => {
                println!(
                    "usage: hnn_exposure [cut-file <path>] [cells <N|all>] [held-out <cells>] [windows <deadline>] [realization <host|card>] [resonator <none|source>] [gate f2]"
                );
                return;
            }
        }
    }

    let setup = Instant::now();
    let (text, source, manifest) = match cut_file.as_deref() {
        Some(path) => {
            let (text, _, range) = read_cut(path);
            (
                text,
                format!("the cut file {path} (held out {range:?} from its manifest)"),
                Some(range),
            )
        }
        None => (pinned_cut(), format!("{CUT_COMMIT}:{CUT_PATH}"), None),
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
    // With a cut file the held-out range is the manifest's own, which must close the cells read;
    // otherwise the declared tail.
    let tail = match manifest {
        Some(range) => {
            assert!(
                held_out.is_none(),
                "a cut file's held-out range is its manifest's; held-out declares the pinned cut's tail"
            );
            assert_eq!(
                range.end, length,
                "the manifest's held-out range closes the cut: read it whole (cells all)"
            );
            range
        }
        None => length.saturating_sub(held_out.unwrap_or(HELD_OUT))..length,
    };
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
    let constitution = loaded.then(|| loaded_constitution(&field));
    let setup = setup.elapsed().as_millis();
    let aperture = field.receivers()[0].aperture;
    println!("hnn_exposure: campaign 1's declared field over {source}");
    println!(
        "resonator: {}",
        if loaded {
            "Decision 38: source ring 0; C/K from its unit parametron, D = I/4 as the initial passive rate; no pump; learned scalar amplitudes initially 1"
        } else {
            "none (campaign 1)"
        }
    );
    if let Some(initial) = &constitution {
        println!(
            "additional declared material: {} bits (charged by the exposure)",
            initial.describe_physics().len()
        );
    }
    println!(
        "cut: the first {length} of the pinned cut's {} bytes (the declared population; n* = {n_star}); {} receiving windows of A = {aperture} cells",
        text.len(),
        length.div_ceil(aperture)
    );
    println!(
        "held out: cells {}..{} ({} cells, the manifest's range or the declared tail); training: cells 0..{}",
        tail.start,
        tail.end,
        tail.len(),
        tail.start
    );
    println!(
        "reference: campaign 1 (every locus's certified step, the normal laws' and the factor families', B_Theta = 2^{} bits, pending capacity {}); deadline: {}",
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
    if let Some(count) = ablation {
        contact_ablation_run(&field, &cut, count, information, descent, samples_out.as_deref());
        return;
    }

    if realization == "card" {
        println!("realization: {}", card_realization());
    } else {
        println!("realization: the host reference (holonics::hnn::Reference)");
    }
    let clock = Instant::now();
    let (exposure, traffic) = if realization == "card" {
        card_exposure(deadline, &field, &cut, constitution)
    } else {
        let exposure = match constitution {
            Some(initial) => reference.expose_with(&field, &cut, initial),
            None => reference.expose(&field, &cut),
        }
        .expect("the exposure");
        (exposure, None)
    };
    let wall = clock.elapsed().as_millis();
    report(&field, &exposure);
    if !exposure.resonator_gains.is_empty() {
        println!();
        println!("== final resonator scalar amplitudes (forms use their squares) ==");
        for (ring, gains) in &exposure.resonator_gains {
            println!(
                "ring {ring}: C {}, K {}, D {}, pump {}",
                exact(&gains[0]),
                exact(&gains[1]),
                exact(&gains[2]),
                exact(&gains[3])
            );
        }
        println!(
            "== their carried remainders (what reached each family below its lattice's unit) =="
        );
        for (ring, remainders) in &exposure.resonator_remainders {
            println!(
                "ring {ring}: C {}, K {}, D {}, pump {}",
                exact(&remainders[0]),
                exact(&remainders[1]),
                exact(&remainders[2]),
                exact(&remainders[3])
            );
        }
    }
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
    if let Some((now, peak)) = exterior::resident_set() {
        println!("resident set (exterior, /proc/self/status): now {now} bytes, peak {peak} bytes");
    }
    if gate {
        f2_gate(&field, &cut, &exposure, setup + wall, cut_file.as_deref());
    }
}

/// Decision 38's one predeclared loaded comparison. The source ring is the smallest ring in the
/// existing causal diamond whose returned wave can reach the second receiving epoch. Its C/K
/// forms are the ring's unit parametron's, and D is the campaign's initial passive rate. No pump,
/// width, gain or material is selected on the cut. The owner retains the initial forms and learns
/// their scalar amplitudes through the reached comparison covector.
fn loaded_constitution(field: &Field) -> Constitution {
    let material = ResonatorMaterial::of_parametron(field.ring(0).parametron(), &rat(1, 4), None)
        .expect("the declared source parametron");
    Constitution::initial(field, CAMPAIGN_ONE_BUDGET)
        .expect("the initial constitution")
        .with_ring_resonator(field, 0, material)
        .expect("the source resonator's certified phases")
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
fn card_exposure(
    deadline: Option<u64>,
    field: &Field,
    cut: &Cut,
    constitution: Option<Constitution>,
) -> (Exposure, Option<String>) {
    let card =
        holonics_cuda::hnn::Card::open(0).expect("a CUDA card at ordinal 0 with its kernels");
    let port = holonics_cuda::hnn::Resident::campaign_one(&card);
    let port = match deadline {
        Some(windows) => port.with_deadline(windows),
        None => port,
    };
    let exposure = match constitution {
        Some(initial) => port.expose_with(field, cut, initial),
        None => port.expose(field, cut),
    }
    .expect("the exposure on the card");
    let traffic = port.traffic();
    let tree = port.tree_times();
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
         realization (the hardware law's report): {realized}\n\
         the landmark tree on the card (campaign 2; exterior wall time, µs, per window as quotient rem remainder): {} phases read, {} cells deposited; transfers {} a window, the card's reads {} a window, the host's class faces from the splits {} a window, the combined faces {} a window, the deposits' updates {} a window\n\
         the resonators' ticks: {} µs a window; the normal-law mirror is off the exposure's path (the GPU suite's parity test): {} µs a window",
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
        per_window(traffic.ingest),
        tree.reads,
        tree.deposits,
        mean(tree.transfer.as_micros(), windows),
        mean(tree.read.as_micros(), windows),
        mean(tree.complete.as_micros(), windows),
        mean(tree.combine.as_micros(), windows),
        mean(tree.deposit.as_micros(), windows),
        mean(exposure.wall.resonators.as_micros(), windows),
        mean(exposure.wall.normal_deposit.as_micros(), windows)
    );
    (exposure, Some(line))
}

#[cfg(not(holonics_card))]
fn card_exposure(
    _: Option<u64>,
    _: &Field,
    _: &Cut,
    _: Option<Constitution>,
) -> (Exposure, Option<String>) {
    unreachable!("card_realization refused first")
}

/// **The wall time by phase** (`Exposure::wall`, exterior): each phase's milliseconds over the run
/// and per receiving window (the integer quotient with its remainder over the windows), the phases'
/// sum, the exposure's own readings (the word balances and the kind census, `Exposure::readout`),
/// and the rest of the exposure's wall time (key location, the aeon boundaries, the baselines and
/// the bookkeeping).
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
    let (balance, census) = (
        exposure.readout.balance.as_millis(),
        exposure.readout.census.as_millis(),
    );
    row("word balances", balance);
    row("kind census", census);
    println!(
        "(word balances: the power forms read before and after each deposit and the commit's deposition work; kind census: the contacts' site readings at every commit; both the exposure's own readings)"
    );
    row(
        "rest of exposure",
        wall.saturating_sub(sum).saturating_sub(balance + census),
    );
    // The tree read against the word, per window in microseconds (Decision 28; campaign 2: on the
    // card, the mirror's launches and the host's completion of the class faces, the transfers and
    // the deposits' updates apart).
    let micros = |time: std::time::Duration| time.as_micros();
    let (tree, word) = (
        micros(exposure.wall.tree_read),
        micros(exposure.wall.refine_read),
    );
    println!(
        "the tree read per window: {} us; the word (refine read) per window: {} us; tree read over word: {}",
        mean(tree, windows),
        mean(word, windows),
        if word == 0 {
            "-".to_string()
        } else {
            format!("{} rem {} over {word}", tree / word, tree % word)
        }
    );
    println!(
        "the tree's transfers per window: {} us; its deposits' updates per window: {} us; the compare phase (holon and covector) per window: {} us; the host's deposit (deposited) per window: {} us",
        mean(micros(exposure.wall.tree_transfer), windows),
        mean(micros(exposure.wall.tree_deposit), windows),
        mean(micros(exposure.wall.holon), windows),
        mean(micros(exposure.wall.deposited), windows)
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
    let words = &word.words;
    println!(
        "word balances (campaign 2, WordBalance::closes: the field and its resonators in one identity with the deposition work at the commit, and the executed residual within its certified bound): {} formed, {} carried across a commit, every one closed: {}; the largest executed residual (defects, the last junction's, and the resonators' chart and split) {} against its bound {}: {}; the deposition work summed over the commits {} (the largest in magnitude {}); the interconnection's defect summed {} (zero by construction for a loaded port: the field's term is the negative of the resonator's port work)",
        words.formed,
        words.committed,
        words.closed,
        exact(&words.largest_residual),
        exact(&words.residual_bound),
        within(&words.largest_residual, &words.residual_bound),
        exact(&words.deposition),
        exact(&words.largest_deposition),
        exact(&words.interconnection)
    );

    let grain = receiver_grain(field);
    println!();
    println!(
        "== bits against the baselines (online, on the same stream; read at the receiver's grain L_R = {grain} as n + k/{grain} + ε: carry n, phase class k, fibre 0 ≤ ε < 1/{grain}) =="
    );
    bits("training", &exposure.training, false, grain);
    bits("held out", &exposure.held_out, true, grain);
    println!();
    println!(
        "== the receiving face's course by aeon (ruling A: each aeon's cells under the model, the tree's executed face alone and the combined face alone; the population's log-odds log2(L_T/L_C) at its boundary) =="
    );
    for (index, leg) in exposure.course.iter().enumerate() {
        println!(
            "aeon {index}: closed at cell {}, {} cells; model {} (a cell {}); tree {} (a cell {}); combined {} (a cell {}); L_C − L_T {}; L_model − L_T {}; log2(L_T/L_C) {}",
            leg.cell,
            leg.cells,
            per(&leg.model, 1, grain),
            per(&leg.model, leg.cells, grain),
            per(&leg.tree, 1, grain),
            per(&leg.tree, leg.cells, grain),
            per(&leg.combined, 1, grain),
            per(&leg.combined, leg.cells, grain),
            difference(&leg.combined, &leg.tree, grain),
            difference(&leg.model, &leg.tree, grain),
            leg.odds
                .as_ref()
                .map_or_else(|| "-".to_string(), |log| per(log, 1, grain))
        );
    }
    match &exposure.population {
        Some(population) => println!(
            "the receiver's population at the end (ruling A, THE_REBUILD U1): code −log2(½ L_T + ½ L_C) {} (the telescope); the tree alone {}; the combined face alone {}; log2(L_T/L_C) {}; {} cells; {} bits",
            enclosure(&population.code, grain),
            population
                .tree
                .as_ref()
                .map_or_else(|| "none".to_string(), |code| enclosure(code, grain)),
            population
                .combined
                .as_ref()
                .map_or_else(|| "none".to_string(), |code| enclosure(code, grain)),
            population
                .odds
                .as_ref()
                .map_or_else(|| "none".to_string(), |odds| enclosure(odds, grain)),
            population.cells,
            population.bits
        ),
        None => println!("the receiver's population: none"),
    }

    println!();
    println!("== cost against the literal ==");
    let work_bits = ceil_log2(&exposure.work.entries_written.clone().max(BigUint::one()));
    println!(
        "Kt = |field + initial material description| {} + located keys {} + L_target|model + ceil(log2 ExactWork) {} = {}",
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
    census(field, exposure);
    rounding(exposure);
    // The certified steps (September 29): each family's least and largest exponent `k` over the
    // curve (the step `2^k`), by locus, and the certified storage growth's product and extremes.
    let mut exponents: std::collections::BTreeMap<String, (i64, i64, u64)> =
        std::collections::BTreeMap::new();
    let mut product = Rat::one();
    let mut growths: Option<(Rat, Rat)> = None;
    for point in exposure.constitution_curve.iter().skip(1) {
        for (locus, family, k) in &point.steps {
            let entry = exponents
                .entry(format!("{locus:?} {family:?}"))
                .or_insert((*k, *k, 0));
            entry.0 = entry.0.min(*k);
            entry.1 = entry.1.max(*k);
            entry.2 += 1;
        }
        product *= Rat::one() + &point.storage_growth;
        let extremes =
            growths.get_or_insert((point.storage_growth.clone(), point.storage_growth.clone()));
        if point.storage_growth < extremes.0 {
            extremes.0 = point.storage_growth.clone();
        }
        if point.storage_growth > extremes.1 {
            extremes.1 = point.storage_growth.clone();
        }
    }
    for (locus, (least, largest, count)) in &exponents {
        println!(
            "the certified steps at {locus}: 2^k for k from {least} to {largest}, over {count} deposits"
        );
    }
    if let Some((least, largest)) = &growths {
        println!(
            "the certified storage growth ε_k of one deposit: from {least} to {largest}; the product ∏(1 + ε_k) since the mount {product}"
        );
    }
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

/// **The contact-kind census** (campaign 2, `hnn::contact::site_readings`, the constitution curve's
/// site readings at every commit, certified from the factors in one prime chart and read exactly
/// otherwise): per contact, the commits at which it read each of the five proved
/// kinds (rotation, null shear, boost, reflection, degenerate), and its modes by kind summed over
/// the commits (the inertia of `K` under `C ≻ 0`). A boost needs a declared stiffness signature: a
/// constitution without one (`K = b bᵀ ⪰ 0`) reads rotations and null shears only.
fn census(field: &Field, exposure: &Exposure) {
    use holonics::navigator::trace::SiteKind;
    let commits = exposure.constitution_curve.len();
    println!(
        "the contact-kind census over {commits} commits (the kinds at each commit; the modes by kind summed over the commits):"
    );
    for contact in 0..field.contacts().len() {
        let (mut kinds, mut modes) = ([0u64; 5], [0u64; 3]);
        for point in &exposure.constitution_curve {
            let reading = &point.contacts[contact];
            kinds[match reading.kind {
                SiteKind::Rotation => 0,
                SiteKind::Null => 1,
                SiteKind::Boost => 2,
                SiteKind::Reflection => 3,
                SiteKind::Degenerate => 4,
            }] += 1;
            modes[0] += reading.census.rotation as u64;
            modes[1] += reading.census.null as u64;
            modes[2] += reading.census.boost as u64;
        }
        let (from, to) = field.contact(contact).ends();
        println!(
            "  contact {contact} ({from} → {to}): rotation {}, null shear {}, boost {}, reflection {}, degenerate {} commits; modes: rotation {}, null {}, boost {}",
            kinds[0], kinds[1], kinds[2], kinds[3], kinds[4], modes[0], modes[1], modes[2]
        );
    }
}

/// [measured-diagnostic; agent-inferred, October 2; the
/// [contact loop record](../../records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)]
/// **The rounding census**: for every family certified at some deposit, the deposits that certified
/// it and the deposits at which it moved a lattice coordinate (not named in the deposit's
/// rounding refusals), with its least and largest certified step exponent.
fn rounding(exposure: &Exposure) {
    use std::collections::BTreeMap;
    let mut families: BTreeMap<String, (u64, u64, i64, i64)> = BTreeMap::new();
    for point in exposure.constitution_curve.iter().skip(1) {
        for (locus, family, exponent) in &point.steps {
            let entry = families
                .entry(format!("{locus:?} {family:?}"))
                .or_insert((0, 0, *exponent, *exponent));
            entry.0 += 1;
            if !point.vanished.contains(&(*locus, *family)) {
                entry.1 += 1;
            }
            entry.2 = entry.2.min(*exponent);
            entry.3 = entry.3.max(*exponent);
        }
    }
    println!("the rounding census over {} deposits:", exposure.constitution_curve.len() - 1);
    for (family, (certified, moved, least, largest)) in &families {
        println!("  {family}: moved at {moved} of {certified} certified deposits; steps 2^{least}..2^{largest}");
    }
}

/// The receiving map's inputs and targets, and `R` at each close, written for the exterior fitted
/// receiver (`receiver_oracle.py`): one line a sample (aeon, target, the input's exact entries), then
/// one line a map (its index, rows, columns, entries). Rewritten whole at each close; the file lives
/// under `.local` (private).
fn write_samples(
    path: &str,
    samples: &[(usize, Vec<Rat>, usize)],
    maps: &[holonics::ratio::linear::ExactRatMatrix],
) {
    let mut text = String::new();
    for (aeon, z, target) in samples {
        text.push_str(&format!("sample {aeon} {target}"));
        for x in z {
            text.push_str(&format!(" {x}"));
        }
        text.push('\n');
    }
    for (index, map) in maps.iter().enumerate() {
        text.push_str(&format!("map {index} {} {}", map.rows(), map.columns()));
        for x in map.entries() {
            text.push_str(&format!(" {x}"));
        }
        text.push('\n');
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(path, text).expect("write the samples");
    println!("  samples written: {} inputs, {} maps", samples.len(), maps.len());
}

/// [measured-diagnostic; agent-inferred, October 2; the contact loop record §7] **The contact loop
/// on the cut** (`ablation <windows>`): `holonics::hnn::reference::contact_ablation` over the first
/// windows; per window the contact families its return moved when deposited alone, the deposition
/// work of that commit on the window's end change, and the next window's code at the predecessor
/// and at the contacts-only successor, with their exact order. One line per window with its
/// elapsed milliseconds.
fn contact_ablation_run(
    field: &Field,
    cut: &Cut,
    windows: usize,
    information: usize,
    descent: bool,
    samples_out: Option<&str>,
) {
    use holonics::hnn::reference::contact_ablation;
    let clock = Instant::now();
    use holonics::hnn::reference::{ContactAblation, CumulativeContacts, ReceiverStep};
    use num_traits::Signed;
    // One aeon's summary: the receiver's exponent span, one deposit's contact change, the
    // contacts-only commits (families certified and vanished, the return's size `a`) and R's steps.
    let aeon_line = |a: usize, readings: &[ContactAblation], receiver: &[ReceiverStep]| {
        let here: Vec<&ContactAblation> = readings.iter().filter(|r| r.aeon == a).collect();
        let largest = here.iter().map(|r| r.exponent_spread.clone()).max().unwrap_or_else(Rat::zero);
        let single = here.iter().map(|r| r.exponent_shift.clone()).max().unwrap_or_else(Rat::zero);
        let families: usize = here.iter().map(|r| r.contact_families).sum();
        let vanished: usize = here.iter().map(|r| r.contact_vanished).sum();
        let total: Rat = here.iter().map(|r| r.contact_alignment.clone()).sum();
        let mut aligns: Vec<Rat> = here.iter().map(|r| r.contact_alignment.clone()).collect();
        aligns.sort();
        let median = aligns.get(aligns.len() / 2).cloned().unwrap_or_else(Rat::zero);
        let steps: Vec<&ReceiverStep> = receiver.iter().filter(|s| s.aeon == a).collect();
        let r_moved = steps.iter().filter(|s| s.moved).count();
        let mut r_aligns: Vec<Rat> = steps.iter().map(|s| s.alignment.clone()).collect();
        r_aligns.sort();
        let r_median = r_aligns.get(r_aligns.len() / 2).cloned().unwrap_or_else(Rat::zero);
        let mut r_steps: Vec<Rat> = steps.iter().map(|s| s.step.clone()).collect();
        r_steps.sort();
        let r_step = r_steps.get(r_steps.len() / 2).cloned().unwrap_or_else(Rat::zero);
        let held = |x: &Rat| holonics::holon::deposition::significant(x, 24, false);
        println!(
            "  aeon {a}: the receiver's exponent span, largest {largest} bits; one deposit's contact change, largest {single} bits; contacts-only commits {}: channel families certified {families}, vanished {vanished}; the contacts' return a, median {}, total {} (24 bits); R's steps {}: moved {r_moved}, its a median {} (24 bits), its step median {r_step}; {} ms",
            here.len(),
            held(&median),
            held(&total),
            steps.len(),
            held(&r_median),
            clock.elapsed().as_millis()
        );
    };
    let cumulative_line = |c: &CumulativeContacts| {
        println!(
            "  after aeon {} (window at {}): the contacts' cumulative change {} bits at an exponent span of {} bits; over {} readings frozen: sum Var_p(delta) {} bits^2 (24 bits); code (opening's contacts less learned) summed [{}, {}) bits, better {}, worse {}, undecided {}; R's largest entry {}, its largest change since the last close over it {} (24 bits); {} ms",
            c.aeon,
            c.position,
            c.exponent_shift,
            c.spread,
            c.readings,
            holonics::holon::deposition::significant(&c.variance, 24, false),
            c.code_difference.lower,
            c.code_difference.upper,
            c.better,
            c.worse,
            c.undecided,
            holonics::holon::deposition::significant(&c.receiving_largest, 24, false),
            holonics::holon::deposition::significant(&c.receiving_change, 24, false),
            clock.elapsed().as_millis()
        );
    };
    let run = contact_ablation(
        &Reference::campaign_one(),
        field,
        &cut.cells,
        windows,
        holonics::hnn::reference::AblationOptions { information, descent, samples: samples_out.is_some() },
        &mut |c, readings, receiver, samples, maps| {
            aeon_line(c.aeon - 1, readings, receiver);
            cumulative_line(c);
            if let Some(path) = samples_out {
                write_samples(path, samples, maps);
            }
        },
    )
    .expect("the contact ablation");
    let (readings, receiver) = (&run.windows, &run.receiver);
    if let Some(path) = samples_out {
        write_samples(path, &run.samples, &run.receiving_maps);
    }
    if let Some(last) = readings.iter().map(|r| r.aeon).max() {
        aeon_line(last, readings, receiver);
    }
    // Each deposit's realized descent, split (the contact loop record §15).
    {
        let mut ratios: Vec<Rat> = run
            .descents
            .iter()
            .filter(|d| d.a_plus.is_positive())
            .map(|d| &d.a_minus / &d.a_plus)
            .collect();
        ratios.sort();
        let n = ratios.len();
        let pick = |q: usize| ratios.get(q.min(n.saturating_sub(1))).cloned().unwrap_or_else(Rat::zero);
        let bound = Rat::new(5.into(), 9.into());
        let past = ratios.iter().filter(|r| **r > bound).count();
        let (mut fell, mut rose, mut undecided) = (0, 0, 0);
        let (mut fell_past, mut rose_past) = (0, 0);
        for d in &run.descents {
            let failing = d.a_plus.is_positive() && &d.a_minus / &d.a_plus > bound || !d.a_plus.is_positive();
            if d.after.upper < d.before.lower {
                fell += 1;
                fell_past += usize::from(failing);
            } else if d.before.upper < d.after.lower {
                rose += 1;
                rose_past += usize::from(failing);
            } else {
                undecided += 1;
            }
        }
        let held = |x: &Rat| holonics::holon::deposition::significant(x, 24, false);
        println!(
            "  deposits {}: A-/A+ median {}, upper quartile {}, largest {} (24 bits); past 5/9 at {past} of {n} (A+ zero at {}); the window's own code fell at {fell}, rose at {rose}, undecided {undecided}; of those past 5/9 or with A+ zero: fell {fell_past}, rose {rose_past}",
            run.descents.len(),
            held(&pick(n / 2)),
            held(&pick(3 * n / 4)),
            held(&pick(n.saturating_sub(1))),
            run.descents.len() - n,
        );
    }
    // The released residuals' coherence per contact: |sum| over the sum of magnitudes, entries
    // pooled; and per entry the statistic Z = S/sqrt(Q), coherent at alpha = 1/20 when
    // Z^2 > 2 ln 40, decided exactly by Z^2 = S^2/Q against the enclosure ln 40 in (3688/1000, 3689/1000).
    {
        use std::collections::BTreeMap;
        let threshold_low = Rat::new(BigInt::from(2 * 3688), BigInt::from(1000));
        let threshold_high = Rat::new(BigInt::from(2 * 3689), BigInt::from(1000));
        let mut pooled: BTreeMap<String, (Rat, Rat, usize, usize, usize, usize)> = BTreeMap::new();
        for ((locus, _, _), r) in &run.released {
            let slot = pooled
                .entry(format!("{locus:?}"))
                .or_insert((Rat::zero(), Rat::zero(), 0, 0, 0, 0));
            slot.0 += r.sum.abs();
            slot.1 += &r.magnitude;
            slot.2 += r.count;
            slot.3 += 1;
            if r.squares.is_positive() {
                let z2 = &r.sum * &r.sum / &r.squares;
                if z2 > threshold_high {
                    slot.4 += 1;
                } else if z2 <= threshold_low {
                    slot.5 += 1;
                }
            }
        }
        for (locus, (net, magnitude, count, entries, coherent, not)) in &pooled {
            let ratio = if magnitude.is_positive() { net / magnitude } else { Rat::zero() };
            println!(
                "  released at {locus}: {count} residuals over {entries} entries; |sum| over magnitudes pooled {} (24 bits); entries coherent at alpha 1/20 (Z^2 > 2 ln 40): {coherent}, not: {not}, of {entries}",
                holonics::holon::deposition::significant(&ratio, 24, false),
            );
        }
    }
    let (mut lower, mut higher, mut equal, mut overlap, mut moved) = (0, 0, 0, 0, 0);
    let (mut states, mut logits, mut faces) = (0, 0, 0);
    let (mut c_anchors, mut c_logits, mut c_faces) = (0, 0, 0);
    let (mut cells, mut c_cells) = (0, 0);
    let mut shifts: Vec<Rat> = Vec::new();
    let mut c_shifts: Vec<Rat> = Vec::new();
    let mut changes: Vec<Rat> = Vec::new();
    let mut anchors: Vec<Rat> = Vec::new();
    let mut spreads: Vec<Rat> = Vec::new();
    for r in readings {
        let order = if r.contacts.upper < r.held.lower {
            lower += 1;
            "strictly lower"
        } else if r.held.upper < r.contacts.lower {
            higher += 1;
            "strictly higher"
        } else if r.contacts == r.held {
            equal += 1;
            "equal"
        } else {
            overlap += 1;
            "overlapping"
        };
        moved += usize::from(!r.moved.is_empty());
        states += usize::from(r.states_differ);
        logits += usize::from(r.logits_differ);
        faces += usize::from(r.faces_differ);
        c_anchors += usize::from(r.continued_anchors_differ);
        c_logits += usize::from(r.continued_logits_differ);
        c_faces += usize::from(r.continued_faces_differ);
        cells += usize::from(r.cells_differ);
        c_cells += usize::from(r.continued_cells_differ);
        shifts.push(r.exponent_shift.clone());
        c_shifts.push(r.continued_exponent_shift.clone());
        changes.push(r.factor_change.clone());
        anchors.push(r.anchor_change.clone());
        spreads.push(r.exponent_spread.clone());
        println!(
            "  window at {}: contacts moved {:?}; work {}; next window's contact states differ {}, logits {}, grain faces {}; continued anchors {}, logits {}, grain faces {}; code held [{}, {}) contacts [{}, {}): {order}; {} ms",
            r.position,
            r.moved,
            r.work,
            r.states_differ,
            r.logits_differ,
            r.faces_differ,
            r.continued_anchors_differ,
            r.continued_logits_differ,
            r.continued_faces_differ,
            r.held.lower,
            r.held.upper,
            r.contacts.lower,
            r.contacts.upper,
            clock.elapsed().as_millis()
        );
    }
    // The exponent spread by quarter of the windows, in window order (the receiver's gain over the
    // exposure): each quarter's largest.
    {
        let quarter = spreads.len().div_ceil(4).max(1);
        let by: Vec<String> = spreads
            .chunks(quarter)
            .map(|chunk| chunk.iter().max().cloned().unwrap_or_else(Rat::zero).to_string())
            .collect();
        println!("  exponent spread by quarter of the windows (largest each): {}", by.join(", "));
    }
    // The exponent shifts against two grains: the declared tolerance 1/16 bit and 1/21 bit (below
    // the derived resolution, the contact loop record §11).
    for (label, values) in [("fresh", &mut shifts), ("continued", &mut c_shifts), ("relative factor change", &mut changes), ("relative anchor change (continued)", &mut anchors), ("exponent spread (continued, held)", &mut spreads)] {
        values.sort();
        let at = |q: usize| values.get(values.len().saturating_sub(1).min(q)).cloned().unwrap_or_else(Rat::zero);
        let n = values.len();
        let above = |grain: Rat| values.iter().filter(|v| **v >= grain).count();
        println!(
            "  {label} exponent shift (bits): median {}, upper quartile {}, largest {}; at least 1/16 at {}, at least 1/21 at {} of {n}",
            at(n / 2),
            at(3 * n / 4),
            at(n.saturating_sub(1)),
            above(Rat::new(1.into(), 16.into())),
            above(Rat::new(1.into(), 21.into())),
        );
    }
    println!(
        "contact ablation: {} windows read; a contact moved at {moved}; the next window's contact states differ at {states}, its logits at {logits}, its grain faces at {faces} (above the fibre at {cells}); continued from the window's own change: anchors at {c_anchors}, logits at {c_logits}, grain faces at {c_faces} (above the fibre at {c_cells}); the next window's code strictly lower {lower}, strictly higher {higher}, equal {equal}, overlapping {overlap}; {} ms; resident {}",
        readings.len(),
        clock.elapsed().as_millis(),
        exterior::resident_set().map_or_else(|| "unread".to_string(), |(now, peak)| format!("{now} now, {peak} peak"))
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
        ("tree", &bits.tree),
        ("tree at the grain", &bits.tree_grain),
        ("combined", &bits.combined),
        ("uniform", &bits.uniform),
        ("order-0 KT", &bits.order_zero),
        ("order-1 KT", &bits.order_one),
        (ppm.as_str(), &bits.ppm),
    ];
    for (name, interval) in rows {
        println!(
            "  {name:<17} {}; per cell at L_R = {grain}: {}",
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
    for (name, baseline) in &rows[4..] {
        println!(
            "  the tree's executed face alone is {} {name}; tree − {name}: {}",
            against(&bits.tree, baseline),
            difference(&bits.tree, baseline, grain)
        );
    }
    println!(
        "  L_C − L_T, the combined face (tree + wave) against the tree's executed face: {} it; {}",
        against(&bits.combined, &bits.tree),
        difference(&bits.combined, &bits.tree, grain)
    );
    println!(
        "  L_model − L_T, the mixture against the tree's executed face: {} it; {}",
        against(&bits.model, &bits.tree),
        difference(&bits.model, &bits.tree, grain)
    );
    println!(
        "  the grain's rounding, the tree at the grain against the tree: {} it; {}",
        against(&bits.tree_grain, &bits.tree),
        difference(&bits.tree_grain, &bits.tree, grain)
    );
    println!(
        "  L_C − L_T at the grain, the combined face against the tree at the grain: {} it; {}",
        against(&bits.combined, &bits.tree_grain),
        difference(&bits.combined, &bits.tree_grain, grain)
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
        "  the wave's contribution (the combined face against the tree's executed face): {}",
        match against(&bits.combined, &bits.tree) {
            "below" => "the wave lowers the code length",
            "above" => "the wave raises the code length",
            _ => "undecided: the enclosures overlap",
        }
    );
    println!(
        "  the mixture (ruling A: the model against the tree's executed face): {}",
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

// -------------------------------------------------------------------------------------------
// F2's adoption gate

/// The probe passage's budget: ten minutes, in milliseconds (the protocol).
const PASSAGE_MS: u128 = 600_000;

/// The warm response's budget: one minute, in milliseconds (F2's pin of September 27).
const RESPONSE_MS: u128 = 60_000;

/// The host memory admitted: 20 GB of resident set, in bytes (the protocol).
const HOST_BYTES: u128 = 20_000_000_000;

/// **The population over the tree alone** (`gate f2`, module header): its code on the training
/// and the held-out cells (each cell's code read before the cell is received, summed as the
/// exposure sums its model's), its telescope over the cells read, and its state: the tree's nodes
/// and bits and the population's bits.
struct TreeAlone {
    training: ExactInterval,
    held_out: ExactInterval,
    telescope: ExactInterval,
    nodes: usize,
    tree_bits: u64,
    population_bits: u64,
}

/// Read the cut's first `scored` cells with the population over the receiver's tree alone: one
/// family at prior one (`PortPopulation::new(&[0])`), its face of each cell the tree's executed
/// face at the cell's causal address over the cell letters, read before the cell's own deposit.
fn tree_alone(field: &Field, cut: &Cut, scored: usize) -> TreeAlone {
    let declaration =
        landmark_declaration(field, &field.receivers()[0]).expect("the receiver's declared tree");
    let depth = declaration.depth;
    let cells = &cut.cells[..scored];
    let letters = cell_letters(cells);
    let mut tree = Landmarks::new(declaration).expect("the receiver's tree");
    let mut population = PortPopulation::new(&[0]).expect("one family at prior one");
    let zero = ExactInterval::point(Rat::zero());
    let (mut training, mut held_out) = (zero.clone(), zero);
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree
            .receive(&letter_address(&letters, position, depth), class)
            .expect("the tree receives the cell");
        let face = [ExactInterval::point(reading.executed)];
        let code = population
            .code_of(&face)
            .expect("a positive executed face has a code");
        let sum = if cut.held_out(position) {
            &mut held_out
        } else {
            &mut training
        };
        *sum = interval_sum(sum, &code).expect("an ordered sum");
        population
            .receive(&face)
            .expect("the population receives the cell");
    }
    TreeAlone {
        training,
        held_out,
        telescope: population.code().expect("the population's telescope"),
        nodes: tree.nodes(),
        tree_bits: tree.bits(),
        population_bits: population.bits(),
    }
}

/// Whether two enclosures share a point (two readings of one exact value must).
fn intersect(a: &ExactInterval, b: &ExactInterval) -> bool {
    a.lower <= b.upper && b.lower <= a.upper
}

/// `value` against `bound`, exactly: within or past it, with the exact margin.
fn budget(value: u128, bound: u128) -> String {
    if value <= bound {
        format!("within it (margin {})", bound - value)
    } else {
        format!("PAST it (by {})", value - bound)
    }
}

/// **F2's adoption gate** (module header; THE_REBUILD F2, the pins of September 28): the charged
/// code of the validation cells with and without the field, the work and memory of each, and the
/// budgets, with the adoption rule's verdict.
fn f2_gate(field: &Field, cut: &Cut, exposure: &Exposure, run: u128, cut_file: Option<&str>) {
    let grain = receiver_grain(field);
    let scored = usize::try_from(exposure.training.cells + exposure.held_out.cells)
        .expect("the cells scored fit the address space");
    let clock = Instant::now();
    let alone = tree_alone(field, cut, scored);
    let alone_wall = clock.elapsed().as_millis();

    println!();
    println!("== F2's adoption gate (THE_REBUILD F2, the pins of September 28) ==");
    println!(
        "without the field: the population over the tree alone (one family at prior one; the receiver's tree at each cell's causal address, each cell scored before its own deposit), read after the exposure over the {scored} cells it scored: {alone_wall} ms wall"
    );
    let agree = [
        intersect(&alone.training, &exposure.training.tree),
        intersect(&alone.held_out, &exposure.held_out.tree),
    ];
    println!(
        "the two readings of the tree (the population over it alone; the exposure's tree column, the face the receiver's population weighs) intersect: training {}, held out {}",
        agree[0], agree[1]
    );

    let held = exposure.held_out.cells;
    let (with, without) = (&exposure.held_out.model, &alone.held_out);
    let shorter = with.upper < without.lower;
    println!("the charged code of the held-out (validation) cells, {held} cells:");
    println!(
        "  with the field (the receiver's population: the tree and q_C at ½/½, the field's declaration charged once, in the prior): {}",
        enclosure(with, grain)
    );
    println!(
        "  without it (the population over the tree alone): {}",
        enclosure(without, grain)
    );
    println!(
        "  with − without: {}; with is {} without; strictly shorter (with.upper < without.lower): {shorter}",
        difference(with, without, grain),
        against(with, without)
    );
    println!(
        "  a cell: with {}; without {}",
        per(with, held, grain),
        per(without, held, grain)
    );
    println!(
        "  the field's own face q_C on them: {}; L_C − L_T: {}",
        enclosure(&exposure.held_out.combined, grain),
        difference(&exposure.held_out.combined, &exposure.held_out.tree, grain)
    );
    println!(
        "the training (choosing) cells, {} cells: with {}; without {}; with − without {}; L_C − L_T {}",
        exposure.training.cells,
        enclosure(&exposure.training.model, grain),
        enclosure(&alone.training, grain),
        difference(&exposure.training.model, &alone.training, grain),
        difference(&exposure.training.combined, &exposure.training.tree, grain)
    );
    match &exposure.population {
        Some(population) => {
            println!(
                "the whole passage, each population's telescope (the field's one bit paid once, in the prior): with −log2(½ L_T + ½ L_C) {}; without −log2 L_T {}; with − without {}",
                enclosure(&population.code, grain),
                enclosure(&alone.telescope, grain),
                difference(&population.code, &alone.telescope, grain)
            );
            println!(
                "the posterior's log-odds log2(L_T/L_C) = L_C − L_T: at the join (after the training cells) {}; at the end {}",
                difference(&exposure.training.combined, &exposure.training.tree, grain),
                population
                    .odds
                    .as_ref()
                    .map_or_else(|| "none".to_string(), |odds| enclosure(odds, grain))
            );
        }
        None => println!("the receiver's population: none"),
    }
    println!(
        "the field's declared description (Kt's term; the gate charges the prior's one bit, not this): {} bits",
        exposure.description_bits
    );

    // Work and memory, the field's part apart.
    let windows = u128::from(exposure.compares);
    let wall = &exposure.wall;
    let tree_ms = (wall.tree_read + wall.tree_transfer + wall.tree_deposit).as_millis();
    let phases_ms = wall.total().as_millis();
    println!(
        "work with the field: the run {run} ms (setup and exposure) over {windows} windows ({} ms a window); of the phases' {phases_ms} ms, the tree's read, transfers and deposit updates {tree_ms} ms and the rest {} ms (the field's word and wave, both populations' scoring inside the compare, and the host's deposit, which on the host also moves the tree)",
        mean(run, windows),
        phases_ms.saturating_sub(tree_ms)
    );
    println!("work without it: the population over the tree alone {alone_wall} ms");
    let resident = exposure.state.resident_bits;
    let population_bits = exposure.population.as_ref().map_or(0, |p| p.bits);
    let peak = exterior::resident_set().map(|(_, peak)| peak);
    println!(
        "memory with the field: the resident's state {resident} bits, of which the tree {} and the population {population_bits}, so the field's part {} bits; the process's peak resident set {} bytes",
        alone.tree_bits,
        resident.saturating_sub(alone.tree_bits + population_bits),
        peak.map_or_else(|| "unread".to_string(), |bytes| bytes.to_string())
    );
    println!(
        "memory without it: the tree {} bits ({} nodes) and the population {} bits, {} bits in all",
        alone.tree_bits,
        alone.nodes,
        alone.population_bits,
        alone.tree_bits + alone.population_bits
    );

    // The budgets.
    let passage_ok = run <= PASSAGE_MS;
    let memory_ok = peak.is_some_and(|bytes| bytes <= HOST_BYTES);
    println!(
        "budget (a), the probe passage: {run} ms against {PASSAGE_MS}: {}; the peak resident set against {HOST_BYTES} bytes: {} (the card's memory is read outside the process)",
        budget(run, PASSAGE_MS),
        peak.map_or_else(|| "unread".to_string(), |bytes| budget(bytes, HOST_BYTES))
    );
    let declared = cut_file.map(|path| {
        (
            manifest_number(path, "\"longest_agent_response\":") as u128,
            manifest_number(path, "\"declared_validation_cells\":") as u128,
        )
    });
    let (response_ok, declared_ok) = match declared {
        Some((response, cells)) if windows > 0 => {
            // A span of `c` cells occupies ⌈c/2⌉ two-cell windows, each at the run's mean.
            let at_mean = |cells: u128| (cells.div_ceil(2) * run).div_ceil(windows);
            let (response_ms, passage_ms) = (at_mean(response), at_mean(cells));
            println!(
                "budget (b), the warm response: the declared validation passage's longest agent response, {response} cells, {} windows at the run's mean: {response_ms} ms (rounded up) against {RESPONSE_MS}: {}; the budget admits {} windows at the mean (the request's own reception excluded, so this reading can refuse the budget and cannot alone admit it)",
                response.div_ceil(2),
                budget(response_ms, RESPONSE_MS),
                RESPONSE_MS * windows / run.max(1)
            );
            println!(
                "budget (c), the declared validation passage: {cells} byte cells, {} windows at the run's mean: {passage_ms} ms (rounded up) against {PASSAGE_MS}: {}; ten minutes admit {} windows at the mean",
                cells.div_ceil(2),
                budget(passage_ms, PASSAGE_MS),
                PASSAGE_MS * windows / run.max(1)
            );
            (response_ms <= RESPONSE_MS, passage_ms <= PASSAGE_MS)
        }
        _ => {
            println!(
                "budgets (b) and (c): unread (no cut file with the declared validation passage's counts, or no window read)"
            );
            (false, false)
        }
    };
    let consistent = agree[0] && agree[1];
    let adopted = consistent && shorter && passage_ok && memory_ok && response_ok && declared_ok;
    let mut terms = Vec::new();
    if !consistent {
        terms.push("the two readings of the tree disagree: the run is refused as inconsistent");
    }
    if !shorter {
        terms.push("the code: with the field is not strictly shorter on the validation cells");
    }
    if !passage_ok {
        terms.push("the probe passage's time");
    }
    if !memory_ok {
        terms.push("the host memory (past the budget or unread)");
    }
    if !response_ok {
        terms.push("the warm response (past the budget or unread)");
    }
    if !declared_ok {
        terms.push("the declared validation passage (past the budget or unread)");
    }
    println!(
        "verdict (host and process; the card's memory is read outside): {}",
        if adopted {
            "every clause holds (adopted for text if the card's memory is within 16 GiB)"
                .to_string()
        } else {
            format!("NOT ADOPTED; the separating terms: {}", terms.join("; "))
        }
    );
}
