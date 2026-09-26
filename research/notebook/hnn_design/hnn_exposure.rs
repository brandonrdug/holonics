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
//!   declared` projects to about 6 h: the control at the standing cut's population.
//! - `cells all` is the whole cut: 85,877 windows, about a week at those means.
//!
//! [definition; agent-inferred] **The held-out part** is the cut's tail of [`HELD_OUT`] cells. That
//! is one mean aeon of campaign 1's joint clock on uniform bytes, `⌈1,281,280/1,077⌉ = 1,190` cells
//! (design (d), "Locks"), and a whole number of receiving windows. It is declared from the field's
//! clock, not from the cut, and never tuned on held-out bits. `held-out H` declares a tail of `H`
//! cells instead. Its targets are compared and reported, never deposited, and no crib reads them
//! (review D1).
//!
//! [definition] **The deadline** `windows K` ends the reading after `K` receiving windows
//! (`Reference::with_deadline`). The cut is still the whole declared population, so the `n*` guard
//! holds, and the run is reported incomplete at the cell it stopped at: a smoke, or a run cut short
//! at its deadline.
//!
//! [established-bounded; measured] **The readout** is the complete `Exposure`, with every quantity
//! design (f) names:
//! - the bits on the training and the held-out targets against each online baseline (uniform,
//!   order-0 and order-1 Krichevsky–Trofimov, PPM of order 2), and the verdict against order-0;
//! - `Kt` with the published keys, against the literal over the cells read;
//! - each key location with its fibres per ring;
//! - each aeon's boundary: its length and lift points, readings, collapse, first law (exchange plus
//!   deposition, telescoping to the change of code length), and the face against the literal;
//! - the state and constitution bits against the source, with and without the collapse;
//! - the constitution's curve, one point per commit;
//! - the budget stop or deadline, the work counted, and the wall time: the exposure's, and the
//!   host's by phase (`Exposure::wall`: refine read, release, compare read, holon and covector,
//!   `pull_back`, `compose`, `deposited`, re-read and ingest), with the rest of the exposure.
//!
//! Every value is exact: integers print as integers and rationals as `n/d` (`n/2^e` on a dyadic
//! denominator), and bits are enclosures with exact endpoints. A decimal appears only at the print,
//! labelled, rounded outward. Wall time is an exterior face, in milliseconds.

use std::fmt::Display;
use std::ops::Range;
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
use num_traits::{One, Signed};

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

/// A pinned cut file (the standing real cut in `.local/cuts/`, written by `standing_cut.py`), read
/// whole at the notebook's exterior boundary. Only its scope and counts are printed.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn read_cut_file(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|error| panic!("read the cut file {path}: {error}"))
}

/// The manifest beside a cut file (`standing_cut.py`): its population and held-out range, read by
/// the numbers after their keys (the manifest is exterior JSON; no parser enters the crate).
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn read_cut_manifest(path: &str) -> (usize, Range<usize>) {
    let manifest_path = path.strip_suffix(".bin").map_or_else(|| format!("{path}.json"), |stem| format!("{stem}.json"));
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|error| panic!("read the cut manifest {manifest_path}: {error}"));
    let numbers_after = |key: &str| -> Vec<usize> {
        let start = manifest.find(key).unwrap_or_else(|| panic!("the manifest names {key}")) + key.len();
        let rest = manifest[start..].trim_start();
        let value = if rest.starts_with('[') {
            &rest[..rest.find(']').expect("a closed list")]
        } else {
            &rest[..rest.find([',', '\n', '}']).unwrap_or(rest.len())]
        };
        value
            .split(|c: char| !c.is_ascii_digit())
            .filter(|piece| !piece.is_empty())
            .map(|piece| piece.parse().expect("a count"))
            .collect()
    };
    let population = numbers_after("\"population\":")[0];
    let range = numbers_after("\"held_out_range\":");
    (population, range[0]..range[1])
}

// -------------------------------------------------------------------------------------------
// presentation (exterior: for a person)

/// An exact rational as a decimal to six places, rounded down or up: a presentation, computed in ℚ.
fn decimal(value: &Rat, up: bool) -> String {
    let million = BigInt::from(1_000_000);
    let scaled = value * Rat::from_integer(million.clone());
    let scaled = if up { scaled.ceil() } else { scaled.floor() }.to_integer();
    let sign = if scaled.is_negative() { "-" } else { "" };
    let magnitude = scaled.abs();
    format!(
        "{sign}{}.{:0>6}",
        &magnitude / &million,
        &magnitude % &million
    )
}

/// An exact rational: an integer, `n/2^e` on a wide dyadic denominator, or `n/d`.
fn exact(value: &Rat) -> String {
    let denominator = value.denom();
    if denominator.is_one() {
        value.numer().to_string()
    } else if denominator.bits() > 16 && denominator.magnitude().count_ones() == 1 {
        format!("{}/2^{}", value.numer(), denominator.bits() - 1)
    } else {
        format!("{}/{}", value.numer(), denominator)
    }
}

/// An exact rational with its decimal beside it.
fn ratio(value: &Rat) -> String {
    format!("{} (decimal {})", exact(value), decimal(value, false))
}

/// An enclosure of bits: its decimal enclosure, rounded outward, then its exact endpoints.
fn enclosure(interval: &ExactInterval) -> String {
    format!(
        "[{}, {}] bits (decimal, outward); exact [{}, {}]",
        decimal(&interval.lower, false),
        decimal(&interval.upper, true),
        exact(&interval.lower),
        exact(&interval.upper)
    )
}

/// An enclosure divided by a count, as a decimal enclosure.
fn per(interval: &ExactInterval, count: u64) -> String {
    if count == 0 {
        return "-".to_string();
    }
    let count = Rat::from_integer(BigInt::from(count));
    format!(
        "[{}, {}]",
        decimal(&(&interval.lower / &count), false),
        decimal(&(&interval.upper / &count), true)
    )
}

/// Where enclosure `a` lies against `b`, exactly.
fn against(a: &ExactInterval, b: &ExactInterval) -> &'static str {
    if a.upper < b.lower {
        "below"
    } else if a.lower > b.upper {
        "above"
    } else {
        "undecided (the enclosures overlap)"
    }
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
            _ => {
                println!(
                    "usage: hnn_exposure [cut-file <path>] [cells <N|all>] [held-out <cells>] [windows <deadline>]"
                );
                return;
            }
        }
    }

    let setup = Instant::now();
    let (text, source) = match cut_file.as_deref() {
        Some(path) => {
            let text = read_cut_file(path);
            let (population, range) = read_cut_manifest(path);
            assert_eq!(text.len(), population, "the cut file's length is the manifest's population");
            assert_eq!(range.end, population, "the held-out range closes the cut");
            held_out = range.end - range.start;
            (text, format!("the cut file {path} (held out {range:?} from its manifest)"))
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

    let clock = Instant::now();
    let exposure = reference.expose(&field, &cut).expect("the exposure");
    let wall = clock.elapsed().as_millis();
    report(&field, &exposure);
    println!();
    phases(&exposure, wall);
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; exposure {wall} ms over {} windows ({} ms a window)",
        exposure.compares,
        wall.checked_div(u128::from(exposure.compares)).unwrap_or(0)
    );
}

/// **The wall time by phase** (`Exposure::wall`, exterior): each phase's milliseconds over the run
/// and per receiving window (integer division, rounded down), the phases' sum, and the rest of the
/// exposure's wall time (key location, the aeon boundaries, the baselines and the bookkeeping).
fn phases(exposure: &Exposure, wall: u128) {
    let windows = u128::from(exposure.compares.max(1));
    println!(
        "== wall time by phase (exterior: the host's wall clock, milliseconds; per window over {} windows) ==",
        exposure.compares
    );
    println!("{:<20}\t{:>10}\t{:>10}", "phase", "total ms", "per window");
    for (name, time) in exposure.wall.phases() {
        let ms = time.as_millis();
        println!("{name:<20}\t{ms:>10}\t{:>10}", ms / windows);
    }
    let sum = exposure.wall.total().as_millis();
    println!("{:<20}\t{sum:>10}\t{:>10}", "phases' sum", sum / windows);
    let rest = wall.saturating_sub(sum);
    println!(
        "{:<20}\t{rest:>10}\t{:>10}",
        "rest of exposure",
        rest / windows
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
    println!("== bits against the baselines (online, on the same stream) ==");
    bits("training", &exposure.training, false);
    bits("held out", &exposure.held_out, true);

    println!();
    println!("== cost against the literal ==");
    let work_bits = ceil_log2(&exposure.work.entries_written.clone().max(BigUint::one()));
    println!(
        "Kt = |Field::describe| {} + located keys {} + L_target|model + ceil(log2 ExactWork) {} = {}",
        exposure.description_bits,
        exposure.key_bits,
        work_bits,
        enclosure(&exposure.kt)
    );
    println!(
        "literal ceil(log2|A|)·n over the cells read: {} bits; Kt is {} the literal{}",
        exposure.literal_bits,
        against(
            &exposure.kt,
            &ExactInterval::point(Rat::from_integer(BigInt::from(exposure.literal_bits)))
        ),
        if exposure.kt.upper < Rat::from_integer(BigInt::from(exposure.literal_bits)) {
            " (the pivot pays off)"
        } else {
            ""
        }
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
        aeon(index, boundary);
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

/// One population's bits against the baselines, and the verdict against online order-0: on the
/// held-out targets, the campaign's criterion (design (f): not beating it is a failure).
fn bits(label: &str, bits: &Bits, criterion: bool) {
    println!("{label}: {} targets", bits.cells);
    if bits.cells == 0 {
        println!("  no targets read");
        return;
    }
    let ppm = format!("PPM order {PPM_ORDER}");
    let rows = [
        ("model p^", &bits.model),
        ("uniform", &bits.uniform),
        ("order-0 KT", &bits.order_zero),
        ("order-1 KT", &bits.order_one),
        (ppm.as_str(), &bits.ppm),
    ];
    for (name, interval) in rows {
        println!(
            "  {name:<11} {}; per cell {}",
            enclosure(interval),
            per(interval, bits.cells)
        );
    }
    for (name, baseline) in &rows[1..] {
        println!("  the model is {} {name}", against(&bits.model, baseline));
    }
    println!(
        "  against online order-0: {}",
        match (against(&bits.model, &bits.order_zero), criterion) {
            ("below", _) => "the model beats it",
            ("above", true) => "FAILURE: the model does not beat it (design (f))",
            ("above", false) => "the model does not beat it",
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
fn aeon(index: usize, boundary: &AeonBoundary) {
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
    first_law(&boundary.first_law);
    literal(&boundary.literal);
}

/// The first law over the aeon: exchange plus deposition, telescoping to its change of code length.
fn first_law(law: &EnclosedBalance) {
    let (total, change) = (law.total(), law.change());
    let telescopes = total.lower == &change.lower - &law.widening
        && total.upper == &change.upper + &law.widening;
    println!(
        "  first law: {} arrivals over {} cells; {} exchange steps, {} deposition steps",
        law.arrivals, law.cells, law.exchanges, law.depositions
    );
    println!("    exchange   {}", enclosure(&law.exchange));
    println!("    deposition {}", enclosure(&law.deposition));
    println!("    total      {}", enclosure(&total));
    println!(
        "    change C(closing) - C(opening) {}; widening {}",
        enclosure(&change),
        ratio(&law.widening)
    );
    println!(
        "    opening {}; closing {}",
        law.opening.as_ref().map_or("-".to_string(), enclosure),
        law.closing.as_ref().map_or("-".to_string(), enclosure)
    );
    println!("    telescopes exactly (total = change widened by the widening): {telescopes}");
}

/// The face against the literal over the aeon: `Σ ℓ + Σ g = n·log₂|A|`.
fn literal(face: &LiteralComparison) {
    let balances = face.code.lower.clone() + &face.gain.upper == face.literal.upper
        && face.code.upper.clone() + &face.gain.lower == face.literal.lower;
    println!(
        "  the face against the literal over {} cells (a reading, not a budget):",
        face.cells
    );
    println!("    code (sum of l)  {}", enclosure(&face.code));
    println!("    gain (sum of g)  {}", enclosure(&face.gain));
    println!("    literal n·log2|A| {}", enclosure(&face.literal));
    println!("    code + gain = literal on the enclosures' endpoints: {balances}");
}
