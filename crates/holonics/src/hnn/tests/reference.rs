//! The exposure protocol on small synthetic cuts: a refine and compare per receiving window,
//! deposits on the training part only, aeon boundaries at the joint clock's carry-out, keys located
//! on the crib that closed each aeon (past cells only, never a held-out one), the budget stop, the
//! cut checked against the declared population, and design (f)'s readout with `Kt` charging the
//! located keys.
//!
//! [measured] Under the exact law the constitution's exact bits multiplied per deposit on the chain
//! control (1,126 → 10,883 → 623,415 at the declared steps; 1,126 → 7,053 → 311,864 → 2,224,183
//! with the factor steps off). On the carrier lattice with the refining remainder (Decision 22) the
//! entries and remainders grow logarithmically, while the solved charts `H⁻¹` still grow with the
//! carried Grams (`research/notebook/hnn_design/hnn_lattice_growth.rs`). These cuts run on the
//! exposure's chain (no pair offset, so its capacity and cut are 17 and 18 cells: one aeon, nine
//! receiving windows), declare a budget two deposits pass, which is the stop rule's own case and
//! keeps the exact deposits few, and the rest of the cut runs on the last published constitution.
//!
//! [measured] Under Decision 26 (the receiving map's `B` and the bound harmonic coordinate carried)
//! the chain's constitution reads 973 bits at the mount, 976, 1,050 and 1,723 after one, two and
//! three deposits of this cut: [`CHAIN_BUDGET`] = 1,100 passes two.

use super::learning::{chain, chain_of};
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::Steps;
use crate::hnn::field::Current;
use crate::hnn::port::{ExecutionPort, ReceiptDetail};
use crate::hnn::reference::{Cut, Exposure, Reference, WallTimes, one_hot};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::reception::Component;

/// The chain cut's declared budget: two deposits pass, the third is refused (module header).
const CHAIN_BUDGET: u64 = 1_100;

fn ordered(interval: &crate::ratio::algebraic::ExactInterval) -> bool {
    interval.lower <= interval.upper
}

/// A periodic source with a little noise over four classes: the baselines have something to learn.
fn source(length: usize, seed: u64) -> Vec<usize> {
    let mut draw = Draw::new(seed);
    (0..length)
        .map(|k| {
            if draw.below(8) == 0 {
                draw.below(4)
            } else {
                [0, 1, 2, 1][k % 4]
            }
        })
        .collect()
}

/// The readout's shape, whatever the budget did.
fn read_out(exposure: &Exposure, cells: u64, held_out: u64) {
    assert_eq!(exposure.training.cells + exposure.held_out.cells, cells);
    assert_eq!(exposure.held_out.cells, held_out);
    assert_eq!(exposure.compares, cells / 2);
    for bits in [&exposure.training, &exposure.held_out] {
        for interval in [
            &bits.model,
            &bits.uniform,
            &bits.order_zero,
            &bits.order_one,
            &bits.ppm,
        ] {
            assert!(ordered(interval) && interval.lower > Rat::from_integer(0.into()));
        }
        assert_eq!(
            bits.uniform.lower,
            Rat::from_integer((2 * bits.cells).into())
        );
    }
    assert!(!exposure.aeons.is_empty());
    // Keys are located only at boundaries, on the crib that closed each aeon.
    assert!(!exposure.keys.is_empty() && exposure.keys.len() <= exposure.aeons.len());
    let mut key_bits = 0;
    for report in &exposure.keys {
        let ReceiptDetail::Keys {
            fibres,
            jumps,
            fell_back,
            ..
        } = &report.detail
        else {
            panic!("a key report");
        };
        assert_eq!((fibres.len(), jumps.len()), (3, 3));
        // ⌈log₂ d_g⌉ for each published key of the rings of periods 2, 3, 2.
        key_bits += fell_back
            .iter()
            .zip([1, 2, 1])
            .filter(|(fell, _)| !**fell)
            .map(|(_, bits)| bits)
            .sum::<u64>();
    }
    assert_eq!(exposure.key_bits, key_bits);
    let mut arrived = 0;
    for (index, boundary) in exposure.aeons.iter().enumerate() {
        let law = &boundary.first_law;
        assert!(ordered(&law.exchange) && ordered(&law.deposition));
        assert!(boundary.cells > 0);
        // The declared field lies inside one diamond: the collapse releases no locus and no
        // carried remainder (Decision 22), so the constitution's bits are unchanged.
        assert!(boundary.collapse.released.is_empty());
        assert_eq!(boundary.collapse.bits[0], boundary.collapse.bits[1]);
        // The ledger telescopes to the aeon's change of code length, exactly on the enclosures'
        // endpoints (Lean `FirstLaw.enclosed_telescopes`), and each aeon opens where the last closed.
        let (total, change) = (law.total(), law.change());
        assert_eq!(total.lower, &change.lower - &law.widening);
        assert_eq!(total.upper, &change.upper + &law.widening);
        if index > 0 {
            assert_eq!(law.opening, exposure.aeons[index - 1].first_law.closing);
        }
        // The face against the literal: Σ ℓ + Σ g = n·log₂|A|, two bits a cell (|A| = 4).
        let literal = &boundary.literal;
        assert_eq!(literal.cells, law.cells);
        assert_eq!(
            literal.literal,
            ExactInterval::point(Rat::from_integer((2 * literal.cells).into()))
        );
        assert_eq!(
            literal.gain.lower,
            &literal.literal.lower - &literal.code.upper
        );
        assert_eq!(
            literal.gain.upper,
            &literal.literal.upper - &literal.code.lower
        );
        arrived += law.cells;
        // The aeon's readings through the aeon owners: each ring's displacement in turns, its
        // epochs the flux through its section, and the last ring crosses its section exactly once.
        assert_eq!((boundary.readings.len(), boundary.epochs.len()), (3, 3));
        for (ring, period) in [2u64, 3, 2].into_iter().enumerate() {
            let turns = Rat::new(
                &boundary.carry_out[ring] - &boundary.opening[ring],
                period.into(),
            );
            assert_eq!(boundary.readings[ring].turns(), turns);
        }
        assert_eq!(boundary.epochs[2], 1.into());
        // The last ring steps only by carry: opened on its section, the aeon read on its clock is a
        // cycle of one whole winding; opened off it by a published key, it is not.
        let on_section = &boundary.opening[2] % 2 == 0.into();
        match &boundary.closing {
            Component::Present(reading) => {
                assert!(on_section && reading.is_whole() && reading.windings() == &1.into());
            }
            Component::Absent(_) => assert!(!on_section),
        }
        assert!(matches!(boundary.view, Component::Absent(_)));
    }
    assert!(arrived <= cells);
    // The first aeon opens at rest, on the last ring's section: its carry-out closes a cycle.
    assert!(exposure.aeons[0].closing.present().is_some());
    assert_eq!(exposure.literal_bits, 2 * cells);
    assert!(
        exposure.kt.lower
            > Rat::from_integer((exposure.description_bits + exposure.key_bits).into())
    );
    assert_eq!(exposure.state.source_bits, 2 * cells);
    assert!(exposure.state.resident_bits >= exposure.state.constitution_bits);
    // No locus was released, so the state's bits with and without the collapse agree (review D6).
    assert_eq!(
        exposure.state.resident_bits_without_collapse,
        exposure.state.resident_bits
    );
    assert!(exposure.work.entries_written > 0u32.into());
}

/// The stop's shape: its commit is the last published one, every published deposit is on the
/// curve, and the refused successor exceeds the budget.
fn stopped(exposure: &Exposure) {
    assert!(!exposure.complete);
    let (stop, cell) = exposure.stop.as_ref().unwrap();
    assert!(stop.bits > stop.budget && !stop.loci.is_empty());
    assert_eq!(stop.commit, exposure.deposits);
    assert_eq!(
        exposure.constitution_curve.len() as u64,
        exposure.deposits + 1
    );
    // One point per commit: the collapse releases no carried remainder (Decision 22), so no
    // boundary adds a point.
    assert!(
        exposure
            .constitution_curve
            .windows(2)
            .all(|pair| pair[1].commit == pair[0].commit + 1)
    );
    // Each published deposit's point reads its carriers and what it released and stepped.
    assert!(
        exposure.constitution_curve[1..]
            .iter()
            .any(|point| point.stepped > 0)
    );
    assert!(
        exposure.constitution_curve[1..]
            .iter()
            .all(|point| point.bits.entries > 0 && point.bits.solved > 0)
    );
    // The receiving map's prior weight (Decision 26) is 1 at the mount.
    assert_eq!(
        exposure.constitution_curve[0].prior,
        Some(crate::ratio::integer(1))
    );
    assert!(*cell < exposure.training.cells + exposure.held_out.cells);
}

/// The chain's cut length: its capacity `n*`, rounded up to a whole receiving window.
fn cut_length() -> usize {
    let n_star = chain_of(1 << 20).capacity().n_star() as usize;
    n_star + n_star % 2
}

/// Design (d), campaign 1's exposure protocol at the declared steps, with a budget two deposits
/// pass: every training window before the stop deposits and the held-out window among them does
/// not; the stop is reported with its commit and cell, no deposit is admitted after it, and the whole
/// cut (its held-out tail included) is still read, compared and measured on the last published
/// constitution; the run is reported incomplete, its curve rising, and the first aeon's first law
/// counts its depositions among its arrivals.
#[test]
fn the_exposure_deposits_on_its_training_part_until_its_budget_stop_and_runs_to_the_end() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: source(length, 81),
        held_out: vec![2..4, length - 4..length],
    };
    let exposure = Reference::new(64, Steps::campaign_one(), CHAIN_BUDGET)
        .expose(&field, &cut)
        .unwrap();
    read_out(&exposure, length as u64, 6);
    stopped(&exposure);
    assert!(exposure.deposits >= 2);
    let (_, stop) = exposure.stop.as_ref().unwrap();
    let training_windows = (0..*stop as usize)
        .step_by(2)
        .filter(|window| !cut.held_out.iter().any(|range| range.contains(window)))
        .count() as u64;
    assert!(*stop > 4);
    assert_eq!(exposure.deposits, training_windows);
    let (first, last) = (
        exposure.constitution_curve[0].bits.total(),
        exposure.constitution_curve.last().unwrap().bits.total(),
    );
    assert!(last > first);
    // Every receiving window is read by a refine and reports its path at the cut.
    assert_eq!(exposure.windows, exposure.compares);
    assert!(exposure.open_windows <= exposure.windows);
    assert!(exposure.peak_word_bits > 0);
    let aeon = &exposure.aeons[0].first_law;
    assert!(aeon.depositions >= 1 && aeon.arrivals > aeon.depositions);
}

/// Design (d): a timeout is an unfinished run at its deadline. Under a deadline of `k` receiving
/// windows the exposure reads exactly the cut's first `k` windows and stops, reported incomplete at
/// the cell it stopped at, with its literal over the cells read. The deadline changes nothing it
/// read: a shorter deadline's readout is the longer one's prefix, exactly.
#[test]
fn the_exposure_stops_at_its_deadline_and_changes_nothing_it_read() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: source(length, 81),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, Steps::campaign_one(), CHAIN_BUDGET);
    let run = |windows: u64| {
        reference
            .clone()
            .with_deadline(windows)
            .expose(&field, &cut)
            .unwrap()
    };
    let (three, two, none) = (run(3), run(2), run(0));
    for (exposure, windows, deposits) in [(&three, 3, 2), (&two, 2, 1), (&none, 0, 0)] {
        assert!(!exposure.complete && exposure.stop.is_none());
        assert_eq!(exposure.deadline, Some(2 * windows));
        assert_eq!((exposure.windows, exposure.compares), (windows, windows));
        assert_eq!(
            exposure.training.cells + exposure.held_out.cells,
            2 * windows
        );
        assert_eq!(exposure.literal_bits, 4 * windows);
        assert_eq!(exposure.state.source_bits, 4 * windows);
        // Windows 0 and 4 deposit; window 2 is held out.
        assert_eq!(exposure.deposits, deposits);
        assert_eq!(
            exposure.constitution_curve.len() as u64,
            exposure.deposits + 1
        );
    }
    assert_eq!(
        (
            three.held_out.cells,
            two.held_out.cells,
            none.held_out.cells
        ),
        (2, 2, 0)
    );
    // The two-window run is the three-window run's prefix: its curve, and its held-out bits,
    // since the third window is a training one.
    assert_eq!(two.constitution_curve[..], three.constitution_curve[..2]);
    assert_eq!(two.held_out, three.held_out);
}

/// Review D2, D1: the exposure refuses a cut that is not exactly the declared population (so the
/// `n*` guard of `Field::declare` cannot be bypassed), and the crib that closes an aeon reads only
/// cells before the boundary, from the aeon's own opening, and never a held-out cell.
#[test]
fn the_exposure_reads_its_declared_population_and_a_past_crib() {
    let length = cut_length();
    let field = chain_of(length as u64);
    for cells in [length - 2, length + 2] {
        let cut = Cut {
            cells: source(cells, 5),
            held_out: Vec::new(),
        };
        assert!(matches!(
            Reference::campaign_one().expose(&field, &cut),
            Err(HnnError::Shape { .. })
        ));
    }
    let cut = Cut {
        cells: source(length, 5),
        held_out: vec![10..14, 30..31],
    };
    assert_eq!(cut.closing_crib(0, 40, 16), 31..40);
    assert_eq!(cut.closing_crib(0, 30, 16), 14..30);
    assert_eq!(cut.closing_crib(20, 29, 16), 20..29);
    assert_eq!(cut.closing_crib(0, 12, 16), 12..12);
    assert_eq!(cut.closing_crib(0, 64, 16), 48..64);
}

/// The kept read (the reference's header): a refine keeps its word and faces for the compare at
/// the commit it read them at, and that compare returns exactly what a compare that reads again
/// returns (a clone of the resident drops the kept reads). A deposit publishes a successor and
/// drops every kept read, so a pending ratio refined before it is read again at the contemporary
/// constitution, and returns what a fresh read returns.
#[test]
fn a_compare_returns_the_same_with_and_without_the_refines_kept_read() {
    let field = chain();
    let reference = Reference::new(4, Steps::campaign_one(), 1 << 40);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[1, 2, 0, 3, 1]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (first, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (second, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    assert!(resident.holds_kept_read(&first) && resident.holds_kept_read(&second));
    let mut fresh = resident.clone();
    assert!(!fresh.holds_kept_read(&first) && !fresh.holds_kept_read(&second));
    let (staged, kept) = reference
        .compare(&mut resident, first, &one_hot(&[1, 0]))
        .unwrap();
    let (_, read) = reference
        .compare(&mut fresh, first, &one_hot(&[1, 0]))
        .unwrap();
    assert_eq!(kept, read);
    assert!(resident.wall().compare_read.is_zero());
    let before = resident.constitution().commit();
    reference.deposit(&mut resident, staged).unwrap();
    assert_eq!(resident.constitution().commit(), before + 1);
    assert!(!resident.holds_kept_read(&second));
    let mut fresh = resident.clone();
    let (_, delayed) = reference
        .compare(&mut resident, second, &one_hot(&[2, 3]))
        .unwrap();
    let (_, again) = reference
        .compare(&mut fresh, second, &one_hot(&[2, 3]))
        .unwrap();
    assert_eq!(delayed, again);
}

/// The host realization (the reference's header): the regions that run together write only their
/// own slots, collected in index order and reduced in a fixed order, so every exact value of the
/// exposure on one worker (the serial realization of the same code) and on several is the same,
/// bit for bit; only the host's wall times differ.
#[test]
fn one_worker_and_many_return_the_same_values() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: source(length, 81),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, Steps::campaign_one(), CHAIN_BUDGET).with_deadline(4);
    let run = |workers: usize| {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let mut exposure = pool.install(|| reference.expose(&field, &cut)).unwrap();
        exposure.wall = WallTimes::default();
        exposure
    };
    let (serial, parallel) = (run(1), run(4));
    assert!(serial.deposits >= 2 && serial.compares == 4);
    assert_eq!(serial, parallel);
}
