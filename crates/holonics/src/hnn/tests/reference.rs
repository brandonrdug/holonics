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

use super::learning::chain_of;
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::Steps;
use crate::hnn::port::ReceiptDetail;
use crate::hnn::reference::{Cut, Exposure, Reference};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::reception::Component;

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
    let exposure = Reference::new(64, Steps::campaign_one(), 1_000)
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
