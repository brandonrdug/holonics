//! The exposure protocol on small synthetic cuts: a refine and compare per receiving window, each
//! then deposited, held-out windows included (prequential scoring), aeon boundaries at the
//! joint clock's carry-out, keys located
//! on the crib that closed each aeon (past cells only, never a held-out one), the budget stop, the
//! cut checked against the declared population, and design (f)'s readout with `Kt` charging the
//! located keys; and the landmark tree's prequential measurement on a cut.
//!
//! [measured] Under the exact law the constitution's exact bits multiplied per deposit on the chain
//! control (1,126 → 10,883 → 623,415 at the declared steps; 1,126 → 7,053 → 311,864 → 2,224,183
//! with the factor steps off). On the carrier lattice with the refining remainder (the lattice deposit) the
//! entries and remainders grow logarithmically, while the solved charts `H⁻¹` still grow with the
//! carried Grams (the notebook's `hnn_lattice_growth`, retired at `2d34b819`). These cuts run on the
//! exposure's chain (no pair offset, so its capacity and cut are both 28 cells: one aeon, fourteen
//! receiving windows of aperture 2; the moment's capacity law gives `N(27) ≥ 4^27` and
//! `N(28) < 4^28` on periods 4, 3 and 2, and [`cut_length`] reads it from the field), declare a budget two deposits pass (read off the unbudgeted run's curve at
//! its second commit, [`two_deposits`]), which is the stop rule's own case and keeps the exact
//! deposits few, and the rest of the cut runs on the last published constitution.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::{OPEN_BUDGET, chain, chain_of};
use crate::hnn::tests::support::encoded;
use super::support::Draw;
use crate::compression::landmark::context::{
    Capacity, ContextError, LandmarkDeclaration, Landmarks, LetterFamily, StopPrior, address, cell_letters,
    code_length,
};
use crate::hnn::HnnError;
use crate::hnn::field::Current;
use crate::hnn::port::{ExecutionPort, ReceiptDetail};
use crate::hnn::Absorption;
use crate::hnn::reference::{
    Cut, Exposure, ReadoutWall, Reception, Reference, WallTimes, prequential,
};
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
        // ⌈log₂ d_g⌉ for each published key of the rings of periods 4, 3, 2.
        key_bits += fell_back
            .iter()
            .zip([2, 2, 1])
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
        // carried remainder (the lattice deposit), so the constitution's bits are unchanged.
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
        for (ring, period) in [4u64, 3, 2].into_iter().enumerate() {
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
    // One point per commit: the collapse releases no carried remainder (the lattice deposit), so no
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

/// **A budget two deposits pass**: the constitution's exact bits at the unbudgeted run's second
/// commit. Each deposit grows the constitution (the tree founds nodes on every deposit), so the
/// third deposit's successor exceeds it.
fn two_deposits(field: &crate::hnn::Field, cut: &Cut) -> u64 {
    let open = Reference::new(64, OPEN_BUDGET)
        .with_deadline(3)
        .expose(field, cut)
        .unwrap();
    let curve = &open.constitution_curve;
    assert!(curve[3].bits.total() > curve[2].bits.total());
    curve[2].bits.total()
}

/// Design (d), campaign 1's exposure protocol at the declared steps under prequential scoring, with a
/// budget two deposits pass: every window before the stop deposits, the held-out window among them
/// included; the stop is reported with its commit and cell, no deposit is admitted after it, and
/// the whole cut (its held-out tail included) is still read, compared and measured on the last
/// published constitution; the run is reported incomplete, its curve rising, and the first aeon's
/// first law counts its depositions among its arrivals.
#[test]
fn the_exposure_deposits_every_window_until_its_budget_stop_and_runs_to_the_end() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let exposure = Reference::new(64, two_deposits(&field, &cut))
        .expose(&field, &cut)
        .unwrap();
    read_out(&exposure, length as u64, 6);
    stopped(&exposure);
    assert_eq!(exposure.deposits, 2);
    let (_, stop) = exposure.stop.as_ref().unwrap();
    // The third window's deposit is refused: windows 0 and 2 (held out) deposited.
    assert_eq!(*stop, 4);
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
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET);
    let run = |windows: u64| {
        reference
            .clone()
            .with_deadline(windows)
            .expose(&field, &cut)
            .unwrap()
    };
    let (three, two, none) = (run(3), run(2), run(0));
    for (exposure, windows, deposits) in [(&three, 3, 3), (&two, 2, 2), (&none, 0, 0)] {
        assert!(!exposure.complete && exposure.stop.is_none());
        assert_eq!(exposure.deadline, Some(2 * windows));
        assert_eq!((exposure.windows, exposure.compares), (windows, windows));
        assert_eq!(
            exposure.training.cells + exposure.held_out.cells,
            2 * windows
        );
        assert_eq!(exposure.literal_bits, 4 * windows);
        assert_eq!(exposure.state.source_bits, 4 * windows);
        // Every window deposits, the held-out window 2 included (prequential scoring).
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
    assert_eq!(two.constitution_curve[..], three.constitution_curve[..3]);
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
            cells: encoded(&field, &source(cells, 5)),
            held_out: Vec::new(),
        };
        assert!(matches!(
            Reference::campaign_one().expose(&field, &cut),
            Err(HnnError::Shape { .. })
        ));
    }
    let cut = Cut {
        cells: encoded(&field, &source(length, 5)),
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
    let reference = Reference::new(4, 1 << 40);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &[1, 2, 0, 3, 1]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (first, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (second, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    assert!(resident.holds_kept_read(&first) && resident.holds_kept_read(&second));
    let mut fresh = resident.clone();
    assert!(!fresh.holds_kept_read(&first) && !fresh.holds_kept_read(&second));
    let (staged, kept) = reference
        .compare(&mut resident, first, &encoded(&field, &[1, 0]))
        .unwrap();
    let (_, read) = reference
        .compare(&mut fresh, first, &encoded(&field, &[1, 0]))
        .unwrap();
    assert_eq!(kept, read);
    assert!(resident.wall().compare_read.is_zero());
    let before = resident.constitution().commit();
    reference.deposit(&mut resident, staged).unwrap();
    assert_eq!(resident.constitution().commit(), before + 1);
    assert!(!resident.holds_kept_read(&second));
    let mut fresh = resident.clone();
    let (_, delayed) = reference
        .compare(&mut resident, second, &encoded(&field, &[2, 3]))
        .unwrap();
    let (_, again) = reference
        .compare(&mut fresh, second, &encoded(&field, &[2, 3]))
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
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, two_deposits(&field, &cut)).with_deadline(4);
    let run = |workers: usize| {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let mut exposure = pool.install(|| reference.expose(&field, &cut)).unwrap();
        exposure.wall = WallTimes::default();
        exposure.readout = ReadoutWall::default();
        exposure
    };
    let (serial, parallel) = (run(1), run(4));
    assert!(serial.deposits >= 2 && serial.compares == 4);
    assert_eq!(serial, parallel);
}

// -------------------------------------------------------------------------------------------
// the landmark tree's prequential measurement on a cut

/// A cell-only tree declaration at the grain 16 under the `½` stop prior.
fn tree_declaration(alphabet: usize, depth: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: 64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
        mass: 1,
        base: crate::compression::landmark::context::BaseMeasure::Even,
    }
}

/// **The prequential measurement**: the development and held-out sums are the replay's per-cell
/// code lengths of the executed faces.
#[test]
fn landmark_prequential_partitions_the_cut() {
    let cells: Vec<usize> = (0..48u64).map(|t| ((t * 3 + t / 5) % 4) as usize).collect();
    let tail = 36..48;
    let cut = Cut {
        cells: super::support::encoded_classes(4, &cells),
        held_out: vec![tail],
    };
    let declared = tree_declaration(4, 2);
    let run = prequential(&cut, &cell_letters(&cells), &declared).unwrap();
    assert_eq!(run.development.cells, 36);
    assert_eq!(run.held_out.cells, 12);
    let mut tree = Landmarks::new(declared.clone()).unwrap();
    let mut sums = [Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero()];
    let mut products = [Rat::one(), Rat::one()];
    for (position, &cell) in cells.iter().enumerate() {
        let reading = tree.receive(&address(&cells, position, 2), cell).unwrap();
        let length = code_length(&reading.executed).unwrap();
        let part = 2 * usize::from(position >= 36);
        sums[part] += length.lower;
        sums[part + 1] += length.upper;
        products[part / 2] *= &reading.executed;
    }
    // The run encloses the faces' product (`PassageCode`): it meets the per-cell sum and the
    // product's own code length, within `2^(−80)` bits.
    for (part, coded) in [&run.development.tree, &run.held_out.tree]
        .into_iter()
        .enumerate()
    {
        let whole = code_length(&products[part]).unwrap();
        assert!(coded.lower <= sums[2 * part + 1] && sums[2 * part] <= coded.upper);
        assert!(coded.lower <= whole.upper && whole.lower <= coded.upper);
        assert!(&coded.upper - &coded.lower <= Rat::new(BigInt::one(), BigInt::one() << 80usize));
    }
    assert_eq!(run.run.nodes, tree.nodes());
    assert_eq!(run.run.bits, tree.bits());
    assert!(run.run.largest_residual <= run.run.face_rule);
}

/// The reference fixture of the contact loop: the chain on a generic constitution, mounted, one word
/// read and compared against its targets; the resident and the compare's deposit.
fn reached_contacts(
    reference: &Reference,
    field: &crate::hnn::Field,
) -> (crate::hnn::reference::Resident, crate::hnn::port::Deposit, crate::hnn::port::StagedId) {
    let mut resident = reference
        .mount_with(field, &Current::at_rest(field), super::learning::generic(field, 301))
        .unwrap();
    let (moment, _) = reference.ingest(&mut resident, None, &encoded(&field, &[1, 0, 0, 1, 1])).unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (staged, compared) = reference.compare(&mut resident, pending, &encoded(&field, &[1, 0])).unwrap();
    match compared.deposit {
        Component::Present(deposit) => (resident, deposit, staged),
        other => panic!("the compare's deposit: {other:?}"),
    }
}

/// [definition; agent-inferred, October 2; the
/// [contact loop record](../../../../../research/records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)]
/// **A reached contact family moves or is named as a rounding refusal** (Astra's smallest unit):
/// the word's return reaches every contact's three factor families with a certified step `η > 0`;
/// deposited whole, and then each family alone with every other locus frozen, a family's factor
/// moves exactly when the deposit does not name it in [`DepositReading::vanished`]. Under the same
/// later drive the predecessor and the whole successor read differently.
#[test]
fn a_reached_contact_family_moves_or_is_named_a_rounding_refusal() {
    use crate::hnn::constitution::{Family, Locus};
    use crate::hnn::field::ConstitutionRead;
    use crate::hnn::port::Deposit;
    let field = super::learning::chain_two();
    let reference = Reference::new(4, 1 << 40);
    let (mut post, deposit, staged) = reached_contacts(&reference, &field);
    let mut pre = post.clone();
    let theta = pre.constitution().clone();
    let moved = |a: usize, family: usize, next: &crate::hnn::Constitution| match family {
        0 => theta.contact_storage(a) != next.contact_storage(a),
        1 => theta.contact_stiffness(a) != next.contact_stiffness(a),
        _ => theta.contact_dissipation(a) != next.contact_dissipation(a),
    };
    let whole = match reference.deposit(&mut post, staged).unwrap().deposit {
        Component::Present(reading) => reading,
        other => panic!("the deposit's reading: {other:?}"),
    };
    let reach = deposit.reach().unwrap().clone();
    for a in 0..field.contacts().len() {
        for family in 0..3 {
            let key = (Locus::Channel(a), Family::Factor(family));
            let certified: Vec<_> = whole.steps.iter().filter(|(l, s)| *l == key.0 && s.family == key.1).collect();
            assert_eq!(certified.len(), 1, "the return reaches contact {a}'s family {family}");
            assert!(certified[0].1.step.step > Rat::zero());
            assert_eq!(moved(a, family, post.constitution()), !whole.vanished.contains(&key));
            let step = deposit
                .factors()
                .iter()
                .find(|s| s.gradient.locus() == key.0 && s.gradient.family() == key.1)
                .unwrap()
                .clone();
            let alone = Deposit::new(deposit.commit(), Vec::new(), vec![step], vec![key.0])
                .with_reach(reach.clone());
            let (next, reading) = theta.deposited(&alone).unwrap();
            assert_eq!(moved(a, family, &next), !reading.vanished.contains(&key));
        }
    }
    let later = |resident: &mut crate::hnn::reference::Resident| {
        let (moment, _) = reference.ingest(resident, None, &encoded(&field, &[0, 1, 1, 0, 0])).unwrap();
        let phases = resident.admitted()[0].clone();
        let (pending, _) = reference.refine(resident, &moment, &phases).unwrap();
        let (_, compared) = reference.compare(resident, pending, &encoded(&field, &[0, 1])).unwrap();
        format!("{:?}", compared.forward)
    };
    assert_ne!(later(&mut pre), later(&mut post));
}

/// The refining grain's dyadic exponent is the least `k` with `2^k ≥ L(N) = ⌈√(N ln 2/2)⌉`:
/// `L(1) = 1`, `L(3) = 2`, `L(6144) = 47`.
#[test]
fn the_refining_grain_exponent_reads_the_least_dyadic_cover_of_the_grain() {
    use crate::hnn::reference::refining_grain_exponent;
    assert_eq!(refining_grain_exponent(1).unwrap(), 0);
    assert_eq!(refining_grain_exponent(3).unwrap(), 1);
    assert_eq!(refining_grain_exponent(6144).unwrap(), 6);
    // Monotone over a campaign's counts, growing by at most one level a step of two readings.
    let mut last = 0;
    for n in (2..8000u64).step_by(2) {
        let k = refining_grain_exponent(n).unwrap();
        assert!(k == last || k == last + 1, "{n}: {last} -> {k}");
        last = k;
    }
}

// -------------------------------------------------------------------------------------------
// the reception carry (the record of October 3, "The reception carries the interior change")

/// An exposure with its wall times cleared: the one field two runs of one cut do not share.
fn without_wall(mut exposure: Exposure) -> Exposure {
    exposure.wall = WallTimes::default();
    exposure.readout = ReadoutWall::default();
    exposure
}

/// The reception carry §2.2 and §4: at complete absorption (`A = I`) the carry path is today's
/// reception exactly on a field with no declared resonator. The prequential exposure under
/// `Carry(Complete)` returns every reading, deposit, balance and curve point of the exposure at rest,
/// bit for bit; the carried state at `A = I` is the field's elapsed tick alone, so only the
/// resident's state bits read more.
#[test]
fn the_carry_at_complete_absorption_is_todays_reception_exactly() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET)
        .with_deadline(6)
        .with_reception(Reception::Rest);
    let rest = without_wall(reference.clone().expose(&field, &cut).unwrap());
    let mut carried = without_wall(
        reference
            .with_reception(Reception::Carry(Absorption::Complete))
            .expose(&field, &cut)
            .unwrap(),
    );
    assert_eq!(rest.compares, 6);
    assert!(carried.state.resident_bits > rest.state.resident_bits);
    carried.state = rest.state.clone();
    // The carried end at `A = I` is that elapsed tick; at rest none is carried.
    assert!(rest.carried.is_none() && carried.carried.is_some());
    carried.carried = None;
    // At `A = I` the carried change is the rest; a chained balance is read only where a word ended
    // exactly at rest, and then nothing was carried, so no work was done on it.
    let chained = &carried.word.chained;
    assert!(chained.closed && chained.dissipative == chained.read);
    assert!(chained.work.is_zero() && chained.excess.is_zero());
    carried.word.chained = rest.word.chained.clone();
    for (a, b) in carried.aeons.iter_mut().zip(&rest.aeons) {
        a.state_bits = b.state_bits;
    }
    assert_eq!(carried, rest);
}

/// **The exposure returns its state** (October 4): the constitution the receiver's own chain
/// retained, whose commit and carrier bits are the curve's last point, and the carried end, `None` at
/// rest. The exposure reads its field's one declared population: a second exposure of the same cut
/// on the retained constitution is refused by the receiving ring's landmark tree, which has passed
/// cells of that population already, so the retained constitution continues the passage where it
/// stopped (its saved state, [`crate::hnn::constitution::ContinuingState`]) and never re-reads it.
#[test]
fn the_exposure_returns_its_retained_constitution_and_carried_end() {
    use crate::hnn::constitution::Constitution;
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET).with_deadline(6);
    let exposure = reference.clone().expose(&field, &cut).unwrap();
    assert_eq!(exposure.deposits, 6);
    let last = exposure.constitution_curve.last().unwrap();
    assert_eq!(exposure.retained.commit(), last.commit);
    assert_eq!(exposure.retained.carrier_bits(), last.bits);
    let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    assert_ne!(exposure.retained, opening, "the receiver's chain moved its constitution");
    assert!(exposure.carried.is_some(), "the default reception carries its end");
    let rest = reference
        .clone()
        .with_reception(Reception::Rest)
        .expose(&field, &cut)
        .unwrap();
    assert!(rest.carried.is_none());
    // The retained tree read over the whole cut again passes its declared population.
    assert!(matches!(
        Reference::new(64, OPEN_BUDGET).expose_with(&field, &cut, exposure.retained.clone()),
        Err(HnnError::Context(ContextError::PopulationReached { .. }))
    ));
}

/// **The exposure's retained state saves and restores whole** (the reception carry §9): the
/// receiver's own chain moved the constitution beyond the source port and the receiving maps (the
/// receiving ring's landmark tree and population at least), and the complete continuing state
/// carries all of it with the carried end, reads back equal from its text, and mounts on the
/// declared opening as the retained constitution with the same carried end, so the next reception
/// meets what the uninterrupted resident would.
#[test]
fn the_exposures_retained_state_saves_and_restores_whole() {
    use crate::hnn::constitution::{Constitution, ContinuingState};
    use crate::hnn::field::ConstitutionRead;
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET).with_deadline(6);
    let exposure = reference.clone().expose(&field, &cut).unwrap();
    let retained = &exposure.retained;
    let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let rings = 0..field.rings().len();
    let receiving = rings.clone().find(|&g| opening.landmarks(g).is_some()).unwrap();
    assert_ne!(retained.landmarks(receiving), opening.landmarks(receiving));
    assert_ne!(retained.population(receiving), opening.population(receiving));
    let ring = rings.clone().find(|&g| field.is_source(g)).unwrap();
    let state = retained
        .continuing_state(ring)
        .unwrap()
        .with_carry(exposure.carried.clone());
    let text = state.to_text();
    let read = ContinuingState::from_text(&text).unwrap();
    assert_eq!(read, state);
    assert_eq!(opening.clone().continued(&read).unwrap(), *retained);
    let current = Current::at_rest(&field);
    let resumed = reference
        .mount_continued(&field, &current, opening, &read)
        .unwrap();
    assert_eq!(resumed.constitution(), retained);
    assert_eq!(resumed.carried(), exposure.carried.as_ref());
    // A constitution's state alone opens a new moment at cell zero, past the tree's population; the
    // passage continues only with the resident's passage (§10).
    assert!(matches!(
        Reference::new(64, OPEN_BUDGET).expose_with(&field, &cut, resumed.constitution().clone()),
        Err(HnnError::Context(ContextError::PopulationReached { .. }))
    ));
}

/// The reception carry §2.3, §2.3a and §8: under the default reception, the carry at `A = 0`
/// (`Carry(Nothing)`, declared nowhere in the test), the chained balance closes exactly
/// at every reception of a prequential exposure on one baseline (the source rings' end storage
/// subtracted once, the opening's lattice split read exactly), and the chain is dissipative with
/// respect to its declared supply at every reception. Each carried wave crosses the lift's move of
/// its conductance at the junction's reference change, `a′ = (1 + Γ) a`, so the lift only emits at
/// every reception (`ingest = −reflected`, the reflected power positive).
///
/// [agent-inferred, October 5; THE_MACHINE guard 9] Restated. On the folded chain (four classes on
/// a period-2 source ring through `c mod 2`) no deposit moved a contact's storage, so the work
/// between the words, `deposition + ingest`, was the lift's alone, and the test also asserted
/// `work = −reflected` and the stronger reading (the work within the next word's certified loss,
/// read, not asserted, by [`crate::hnn::reference::ChainedBalances`]) at all eight receptions. Both
/// were facts of that fixture's zero deposition, not laws: on the fold-free chain (its source ring of
/// period 4) the deposits move the contacts' storage, and the work carries their deposition.
#[test]
fn the_chained_balance_closes_and_the_chain_is_dissipative() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET).with_deadline(24);
    assert_eq!(reference.reception(), Reception::Carry(Absorption::Nothing));
    let exposure = reference.expose(&field, &cut).unwrap();
    let chained = &exposure.word.chained;
    assert!(exposure.word.words.closed && exposure.word.closed);
    assert_eq!(chained.read, exposure.compares - 1);
    assert_eq!(chained.read, 13);
    assert!(chained.closed);
    assert_eq!(chained.dissipative, chained.read);
    assert_eq!(chained.lift_emits, chained.read);
    assert!(chained.reflected > Rat::zero(), "the lift moves a carried wave's reference");
    assert!(!chained.split.is_zero(), "a transmitted wave is split at the word's lattice");
}

/// The reception carry §2.4 on a pumped field: with a resonator declared on every ring the carry
/// is accepted, each resonator crosses the deposit at held momentum, and the chained balance still
/// closes and is dissipative at every reception, with the carried resonator storage on its right.
#[test]
fn the_chained_balance_closes_on_a_pumped_field() {
    use crate::hnn::constitution::Constitution;
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET)
        .with_deadline(24)
        .with_reception(Reception::Carry(Absorption::Nothing));
    let theta = super::prediction::resonant(
        &field,
        Constitution::initial(&field, OPEN_BUDGET).unwrap(),
    );
    let exposure = reference.expose_with(&field, &cut, theta).unwrap();
    let chained = &exposure.word.chained;
    assert!(exposure.word.words.closed && exposure.word.closed);
    assert_eq!(chained.read, exposure.compares - 1);
    assert!(chained.read > 0);
    assert!(chained.closed);
    assert_eq!(chained.dissipative, chained.read);
    assert!(chained.excess.is_zero() && chained.largest_excess.is_zero());
}

/// The reception carry §2.1, §2.6 and §8: under `Carry(Nothing)` every refine writes its word's end
/// as the resident's one carried change, at the field's elapsed ticks (the hops every earlier word
/// ran, §2.4), its compare leaves it, and the next reception's word opens on its interior with the
/// source rings imposed by the moment: the refine's faces are the read on that opening, and they
/// differ from the read at rest.
///
/// [agent-inferred, October 5; the lattice word, `hnn::reference`'s header] A word is a function of
/// the pending ratio's operands, the published constitution **and the kept charts**, so the read
/// that reproduces the refine opens on the carry and the kept charts, each as saved and read back
/// (the carry in the state's carry line, the charts in its passage, §10). The carry alone is not the
/// state the word opens on. A read on fresh charts (`Charts::new()`) is another certified
/// representative: where a deposit moved an operator and its kept chart still certifies within the
/// target, the warm start keeps it (no step), and the cold start reaches another lattice point at
/// the same target. The read takes the carried representatives, so a fresh read separates exactly
/// where some split straddles a tie of the transients' lattice; `chart::witness` constructs one,
/// which is what keeps the charts in the retained quotient. On this fold-free chain the release law
/// separated at window 6 (receipts of October 5: face 0, cell 0, fibre `4177/2^19` against
/// `4181/2^19`); under the exact carry no window straddles a tie (v122), and the count is printed.
#[test]
fn the_carry_passes_each_receptions_end_to_the_next() {
    use crate::hnn::{Absorption, Charts, PendingRatio, WordOpening};
    let length = cut_length();
    let field = chain_of(length as u64);
    let cells = source(length, 81);
    let reference =
        Reference::new(64, OPEN_BUDGET).with_reception(Reception::Carry(Absorption::Nothing));
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let phases = resident.admitted()[0].clone();
    let steps = phases.junction_steps();
    let (moment, _) = reference.ingest(&mut resident, None, &encoded(&field, &[])).unwrap();
    assert!(resident.carried().is_none());
    let mut position = 0;
    let (mut receptions, mut moved, mut separated) = (0, 0, 0);
    for span in phases.windows(cells.len()).unwrap().into_iter().take(24) {
        let window = &cells[span.clone()];
        if window.len() == phases.aperture() {
            let before = resident.carried().cloned();
            // The opening is read from the carry as saved and read back (§2.4), and the kept charts
            // from their own saved text (§10): together with the constitution they are the operands
            // the word reads, so the word they open is the uninterrupted chain's exactly.
            let kept = {
                let mut text = String::new();
                resident.charts().write(&mut text);
                let mut lines = text.lines();
                let head = lines.next().unwrap();
                let kept = Charts::read(head, &mut |what| {
                    lines.next().ok_or(HnnError::ContinuingState { what })
                })
                .unwrap();
                assert_eq!(&kept, resident.charts());
                assert!(lines.next().is_none());
                kept
            };
            let opening = match &before {
                Some(carry) => {
                    let mut text = String::new();
                    carry.write(&mut text);
                    let mut lines = text.lines();
                    let head = lines.next().unwrap();
                    let restored = crate::hnn::ReceptionCarry::read(head, &mut |what| {
                        lines.next().ok_or(HnnError::ContinuingState { what })
                    })
                    .unwrap();
                    assert_eq!(&restored, carry);
                    assert!(lines.next().is_none());
                    WordOpening::Received {
                        carry: restored,
                        absorption: Absorption::Nothing,
                    }
                }
                None => WordOpening::Rest,
            };
            let ratio = PendingRatio::produce(
                resident.current(),
                resident.moment(&moment).unwrap(),
                resident.address(),
                &phases,
                resident.constitution().commit(),
            )
            .unwrap();
            let (pending, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
            let faces = refined.forward.into_present().unwrap();
            let theta = resident.constitution().clone();
            let mut charts = kept.clone();
            let (_, on) = ratio.read_on(&field, &theta, &mut charts, &opening).unwrap();
            assert_eq!(faces, on);
            assert_eq!(&charts, resident.charts(), "the read keeps the refine's charts");
            let mut fresh_charts = Charts::new();
            let (_, fresh) = ratio
                .read_on(&field, &theta, &mut fresh_charts, &opening)
                .unwrap();
            separated += usize::from(fresh != faces);
            // Diagnosis only: whether the kept charts differ from cold ones at all.
            eprintln!("carry-chain charts window={} kept_equals_fresh={}", receptions + 1, charts == fresh_charts);
            let moving = |carry: &crate::hnn::ReceptionCarry| {
                let change = &carry.change;
                change
                    .storage
                    .iter()
                    .chain(change.arrivals.iter().flatten())
                    .chain(change.states.iter().flatten())
                    .flatten()
                    .any(|x| !x.is_zero())
            };
            if before.as_ref().is_some_and(moving) {
                // At rest on the same kept charts, so a difference is the carry's motion alone.
                let (_, at_rest) = ratio
                    .read_on(&field, &theta, &mut kept.clone(), &WordOpening::Rest)
                    .unwrap();
                moved += usize::from(faces != at_rest);
            }
            receptions += 1;
            let carry = resident.carried().cloned().expect("the refine writes the carry");
            // Each word's motion stands at its last crossing, whose hop has not run (§2.4).
            assert_eq!(carry.ticks, receptions * (steps - 1));
            // The compare reads the word; the motion already carried at its refine (§8).
            let (staged, _) = reference
                .compare(&mut resident, pending, &encoded(&field, window))
                .unwrap();
            assert_eq!(resident.carried(), Some(&carry));
            let deposited = reference.deposit(&mut resident, staged).unwrap();
            let reading = deposited.deposit.present().unwrap();
            // Progress and diagnosis only (no assertion): what each deposit moved, per window.
            eprintln!(
                "carry-chain window={receptions} separated={separated} stepped={} vanished={:?} unresolved={} loci={:?}",
                reading.stepped,
                reading.vanished,
                reading.unresolved_contact_material.len(),
                reading.steps.iter().map(|(locus, _)| *locus).collect::<Vec<_>>()
            );
        }
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &encoded(&field, &window[fed..]))
                .unwrap();
            let ingested = ingested.forward.into_present().unwrap();
            fed += ingested.cells;
            if ingested.carry_out {
                let family = resident.admitted().to_vec();
                reference.close_aeon(&mut resident, &family).unwrap();
            }
        }
        position = span.end;
    }
    // The carried interior moves the read once the constitution reads the receiving ring.
    assert!(moved >= 1 && position > 0);
    // The kept charts are a retained operand: the read takes the junction's carried
    // representatives, and two certified charts of one operator can split one image differently
    // (`chart::witness`), so the quotient must not merge two residents that differ only in them.
    // Whether this chain's images straddle a tie is a reading, not the law: under the release law
    // (receipts of October 5) the fresh read separated at window 6; under the exact carry
    // (cacb0d037) the measured chain reads the kept and fresh charts equal in all fourteen windows
    // (v122), with no straddled tie (October 8 trace; the former failure receipts are kept).
    eprintln!("carry-chain separations by fresh charts: {separated} of {receptions}");
    // The carry mounts beside a declared constitution (§2.4), and only under a carrying reception:
    // the rest limit refuses it. That mount is the narrower remount: it holds no kept chart, so its
    // next word is the uninterrupted chain's only where the kept charts are their operators' cold
    // charts; the whole continuation is `mount_continued` on the resident's state (its passage).
    let carry = resident.carried().cloned().expect("the chain carries");
    let mounted = reference
        .mount_carried(&field, resident.current(), resident.constitution().clone(), carry.clone())
        .unwrap();
    assert_eq!(mounted.carried(), Some(&carry));
    assert!(mounted.charts().is_empty() && !resident.charts().is_empty());
    assert!(matches!(
        Reference::new(64, OPEN_BUDGET)
            .with_reception(Reception::Rest)
            .mount_carried(
                &field,
                resident.current(),
                resident.constitution().clone(),
                carry
            ),
        Err(HnnError::ContinuingState { .. })
    ));
}

/// [agent-inferred, October 5; the reception carry §10 and the lattice word] **A cold restore
/// continues the carry chain exactly where the kept charts have moved.** On the fold-free chain
/// under `Carry(Nothing)`, the resident's whole state (`Resident::continuing_state`: the
/// constitution's learned material, the carried end, and the passage with the kept charts) is saved
/// before every reception, read back from its text and mounted cold on a fresh founding
/// constitution (`Reference::mount_continued`). The restored resident's reception is the
/// uninterrupted one's at every window, faces, compare and deposit alike, and leaves the same
/// constitution, carry and charts:
/// `compare(refine(mount_continued(save(r)), m, φ), t) = compare(refine(r, m, φ), t)`. Deposits
/// move operators whose kept charts a cold start does not reproduce, and certified charts can split
/// one image differently (`chart::witness`), so the equality rests on the charts the passage
/// carries; whether this chain's reads straddle a tie is printed (none under the exact carry, v122).
#[test]
fn a_cold_restore_continues_the_carry_chain_where_the_kept_charts_have_moved() {
    use crate::hnn::constitution::{Constitution, ContinuingState};
    use crate::hnn::{Absorption, Charts, PendingRatio, WordOpening};
    let length = cut_length();
    let field = chain_of(length as u64);
    let cells = source(length, 81);
    let reference =
        Reference::new(64, OPEN_BUDGET).with_reception(Reception::Carry(Absorption::Nothing));
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let phases = resident.admitted()[0].clone();
    let ring = field.sources()[0];
    let (moment, _) = reference.ingest(&mut resident, None, &encoded(&field, &[])).unwrap();
    let (mut receptions, mut separated) = (0, 0);
    for span in phases.windows(cells.len()).unwrap().into_iter().take(24) {
        let window = &cells[span.clone()];
        if window.len() == phases.aperture() {
            let state = resident.continuing_state(ring).unwrap();
            let read = ContinuingState::from_text(&state.to_text()).unwrap();
            assert_eq!(read, state);
            let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
            let mut restored = reference
                .mount_continued(&field, &Current::at_rest(&field), opening, &read)
                .unwrap();
            assert_eq!(restored.charts(), resident.charts());
            assert_eq!(restored.carried(), resident.carried());
            // The witness that the kept charts carry the equality: the same word on fresh charts.
            let ratio = PendingRatio::produce(
                resident.current(),
                resident.moment(&moment).unwrap(),
                resident.address(),
                &phases,
                resident.constitution().commit(),
            )
            .unwrap();
            let word_opening = match resident.carried() {
                Some(carry) => WordOpening::Received {
                    carry: carry.clone(),
                    absorption: Absorption::Nothing,
                },
                None => WordOpening::Rest,
            };
            let mut fresh_charts = Charts::new();
            let (_, fresh) = ratio
                .read_on(&field, resident.constitution(), &mut fresh_charts, &word_opening)
                .unwrap();
            let (whole, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
            // Diagnosis only: whether the kept charts differ from cold ones at all.
            eprintln!("cold-restore charts window={receptions} kept_equals_fresh={}", resident.charts() == &fresh_charts);
            let (cold, restored_refined) =
                reference.refine(&mut restored, &moment, &phases).unwrap();
            assert_eq!(restored_refined.forward, refined.forward);
            separated += usize::from(refined.forward.present() != Some(&fresh));
            let target = encoded(&field, window);
            let (staged, compared) = reference.compare(&mut resident, whole, &target).unwrap();
            let (restored_staged, restored_compared) =
                reference.compare(&mut restored, cold, &target).unwrap();
            assert_eq!(restored_compared.forward, compared.forward);
            assert_eq!(restored_compared.deposit, compared.deposit);
            let deposited = reference.deposit(&mut resident, staged).unwrap();
            let reading = deposited.deposit.present().unwrap();
            // Progress and diagnosis only (no assertion): what each deposit moved, per window.
            eprintln!(
                "cold-restore window={receptions} separated={separated} stepped={} vanished={:?} unresolved={} loci={:?}",
                reading.stepped,
                reading.vanished,
                reading.unresolved_contact_material.len(),
                reading.steps.iter().map(|(locus, _)| *locus).collect::<Vec<_>>()
            );
            reference.deposit(&mut restored, restored_staged).unwrap();
            assert_eq!(restored.constitution(), resident.constitution());
            assert_eq!(restored.carried(), resident.carried());
            assert_eq!(restored.charts(), resident.charts());
            receptions += 1;
        }
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &encoded(&field, &window[fed..]))
                .unwrap();
            let ingested = ingested.forward.into_present().unwrap();
            fed += ingested.cells;
            if ingested.carry_out {
                let family = resident.admitted().to_vec();
                reference.close_aeon(&mut resident, &family).unwrap();
            }
        }
    }
    assert_eq!(receptions, 14);
    // The restore's exactness rests on the charts the passage carries (`chart::witness`: certified
    // charts can split one image differently). On this chain under the exact carry no window
    // straddles a tie, so the separation by fresh charts is a reading here (v122: 0 of 14), not an
    // assertion (October 8 trace; the former failure receipts are kept).
    eprintln!("cold-restore separations by fresh charts: {separated} of {receptions}");
}

/// The reception carry §8: several pending ratios are one chain in refine order. Each refine runs
/// its word on the end of the last word read, compared or not, and carries its own end; a compare
/// reads its word and leaves the carry. Three refines in a row run the same chain as three
/// refine-compare receptions with no deposit between. Their compares, taken in refine order with a
/// deposit after each (every later kept read stale, so its word is read again at the contemporary
/// constitution) or in reverse order, leave the carry at the third word's end. The chained balance
/// closes at every opening: between refines with no commit between them, and across the commits
/// published while the third word's end stood, read as one commit at held momentum.
#[test]
fn several_pending_ratios_are_one_chain_in_refine_order_and_the_chained_balance_closes() {
    use crate::hnn::word::{PowerForm, WordBalance};
    use crate::hnn::word::{ChainedBalance, EndChange, ReceptionCarry};
    let length = cut_length();
    let field = chain_of(length as u64);
    let cells = source(length, 81);
    let reference = Reference::new(64, OPEN_BUDGET);
    assert_eq!(reference.reception(), Reception::Carry(Absorption::Nothing));
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let phases = resident.admitted()[0].clone();
    let steps = phases.junction_steps();
    let (moment, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &cells[..phases.aperture()]))
        .unwrap();
    let serial = resident.clone();
    // The form at a word's cut and the opening change it reads, before its refine.
    let opening = |resident: &crate::hnn::reference::Resident,
                   carry: &ReceptionCarry|
     -> (PowerForm, EndChange) {
        let form =
            PowerForm::read(&field, resident.constitution(), resident.current()).unwrap();
        let source = resident
            .moment(&moment)
            .unwrap()
            .open_storage(&field, resident.constitution(), resident.current())
            .unwrap();
        let mut opened = form.opening(&field, carry).unwrap();
        for (wave, added) in opened.storage.iter_mut().zip(&source) {
            *wave = crate::ratio::linear::vector::add(wave, added);
        }
        (form, opened)
    };
    let balance = |receipt: &crate::hnn::port::PortReceipt| -> WordBalance {
        match &receipt.detail {
            ReceiptDetail::Refine { word, .. } => word.as_ref().clone(),
            _ => panic!("a refine's word balance"),
        }
    };
    let (mut pending, mut faces, mut balances, mut carries, mut forms) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for j in 0..3 {
        let opened = carries.last().map(|carry| opening(&resident, carry));
        let (id, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let carry = resident.carried().cloned().expect("the refine writes the carry");
        assert_eq!(carry.ticks, (j + 1) * (steps - 1));
        let word = balance(&refined.receipt);
        assert!(word.closes());
        if let (Some((form, opened)), Some(previous)) = (&opened, balances.last()) {
            let chained = ChainedBalance::read(
                &field,
                previous,
                form,
                carries.last().unwrap(),
                opened,
                &word,
            )
            .unwrap();
            assert!(chained.closes() && chained.dissipative());
            assert!(chained.deposition.is_zero(), "no commit between the refines");
        }
        forms.push(PowerForm::read(&field, resident.constitution(), resident.current()).unwrap());
        pending.push(id);
        faces.push(refined.forward.into_present().unwrap());
        balances.push(word);
        carries.push(carry);
    }
    assert_eq!(resident.carried(), carries.last());
    // The same chain, one reception at a time with no deposit between.
    let mut one = serial;
    for (j, read) in faces.iter().enumerate() {
        let (id, refined) = reference.refine(&mut one, &moment, &phases).unwrap();
        assert_eq!(refined.forward.into_present().as_ref(), Some(read));
        assert_eq!(one.carried(), Some(&carries[j]));
        reference
            .compare(&mut one, id, &encoded(&field, &cells[..phases.aperture()]))
            .unwrap();
    }
    // Compared in reverse order: every compare succeeds and the carry stands.
    let mut reversed = resident.clone();
    for &id in pending.iter().rev() {
        reference
            .compare(&mut reversed, id, &encoded(&field, &cells[..phases.aperture()]))
            .unwrap();
        assert_eq!(reversed.carried(), carries.last());
    }
    // Compared in refine order with a deposit after each: the commits act on the motion where it
    // stands, the third word's end.
    let mut moved = 0;
    for &id in &pending {
        let commit = resident.constitution().commit();
        let (staged, _) = reference
            .compare(&mut resident, id, &encoded(&field, &cells[..phases.aperture()]))
            .unwrap();
        reference.deposit(&mut resident, staged).unwrap();
        moved += usize::from(resident.constitution().commit() != commit);
        assert_eq!(resident.carried(), carries.last());
    }
    assert!(moved >= 2, "the later compares read their words again");
    let after = PowerForm::read(&field, resident.constitution(), resident.current()).unwrap();
    let mut previous = balances.last().unwrap().clone();
    previous.commit_held(forms.last().unwrap(), &after).unwrap();
    let (form, opened) = opening(&resident, carries.last().unwrap());
    let (_, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let next = balance(&refined.receipt);
    let chained = ChainedBalance::read(
        &field,
        &previous,
        &form,
        carries.last().unwrap(),
        &opened,
        &next,
    )
    .unwrap();
    assert!(chained.closes() && chained.dissipative());
}


/// The reception carry §10: a passage stopped at a window's opening is saved with the resident's
/// passage (its lift point, open moment, aeon in progress, first-law balance, charts, address
/// register and admitted ranks), read back from its text, mounted on the declared opening, and
/// continued at the epoch its moment's cells reach. The two runs together are the whole run: the
/// same retained constitution and carried end, the curve's points in order, the aeons with their
/// first laws, and the machine's code lengths summed exactly. The cut stops after four windows
/// (cell 8) and its one aeon closes at cell 11, inside the continued run.
#[test]
fn a_saved_passage_continues_at_its_epoch_as_the_whole_run() {
    use crate::hnn::constitution::{Constitution, ContinuingState};
    let length = cut_length();
    let field = chain_of(length as u64);
    let cut = Cut {
        cells: encoded(&field, &source(length, 81)),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET);
    let whole = reference.expose(&field, &cut).unwrap();
    assert!(whole.complete);
    assert_eq!(whole.aeons.len(), 1);
    let mounted = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let (prefix, resident) = reference
        .clone()
        .with_deadline(4)
        .expose_continuing(&field, &cut, mounted)
        .unwrap();
    assert_eq!(prefix.deadline, Some(8));
    assert!(prefix.aeons.is_empty());
    let ring = (0..field.rings().len()).find(|&g| field.is_source(g)).unwrap();
    let state = resident.continuing_state(ring).unwrap();
    assert!(state.passage().is_some());
    let read = ContinuingState::from_text(&state.to_text()).unwrap();
    assert_eq!(read, state);
    let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let restored = reference
        .mount_continued(&field, &Current::at_rest(&field), opening, &read)
        .unwrap();
    assert_eq!(restored.constitution(), resident.constitution());
    assert_eq!(restored.current(), resident.current());
    assert_eq!(restored.carried(), resident.carried());
    assert_eq!(restored.address(), resident.address());
    assert_eq!(restored.admitted(), resident.admitted());
    let (rest, _) = reference.expose_continuing(&field, &cut, restored).unwrap();
    assert!(rest.complete);
    assert_eq!(rest.retained, whole.retained);
    assert_eq!(rest.carried, whole.carried);
    let mut curve = prefix.constitution_curve.clone();
    curve.extend(rest.constitution_curve[1..].iter().cloned());
    assert_eq!(curve, whole.constitution_curve);
    assert_eq!(rest.aeons, whole.aeons);
    assert_eq!(rest.keys.len(), whole.keys.len());
    let sum = |a: &ExactInterval, b: &ExactInterval| ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    };
    for (p, r, w) in [
        (&prefix.training, &rest.training, &whole.training),
        (&prefix.held_out, &rest.held_out, &whole.held_out),
    ] {
        assert_eq!(p.cells + r.cells, w.cells);
        assert_eq!(sum(&p.model, &r.model), w.model);
        assert_eq!(sum(&p.tree, &r.tree), w.tree);
        assert_eq!(sum(&p.tree_grain, &r.tree_grain), w.tree_grain);
        assert_eq!(sum(&p.combined, &r.combined), w.combined);
    }
    // A damaged passage is refused by the state's check before any line is read.
    let mut damaged = state.to_text();
    damaged = damaged.replacen("\nmoment ", "\nmoment 1", 1);
    assert!(ContinuingState::from_text(&damaged).is_err());
}
