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
//! exposure's chain (no pair offset, so its capacity and cut are 17 and 18 cells: one aeon, nine
//! receiving windows), declare a budget two deposits pass (read off the unbudgeted run's curve at
//! its second commit, [`two_deposits`]), which is the stop rule's own case and keeps the exact
//! deposits few, and the rest of the cut runs on the last published constitution.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::{OPEN_BUDGET, chain, chain_of};
use super::support::Draw;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, LetterFamily, StopPrior, address, cell_letters,
    code_length,
};
use crate::hnn::HnnError;
use crate::hnn::field::Current;
use crate::hnn::port::{ExecutionPort, ReceiptDetail};
use crate::hnn::Absorption;
use crate::hnn::reference::{
    Cut, Exposure, ReadoutWall, Reception, Reference, WallTimes, one_hot, prequential,
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
        cells: source(length, 81),
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
        cells: source(length, 81),
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
    let reference = Reference::new(4, 1 << 40);
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
        cells: cells.clone(),
        held_out: vec![tail],
    };
    let declared = tree_declaration(4, 2);
    let run = prequential(&cut, &cell_letters(&cut.cells), &declared).unwrap();
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
    let (moment, _) = reference.ingest(&mut resident, None, &one_hot(&[1, 2, 0, 3, 1])).unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (staged, compared) = reference.compare(&mut resident, pending, &one_hot(&[1, 0])).unwrap();
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
    let field = chain();
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
        let (moment, _) = reference.ingest(resident, None, &one_hot(&[2, 3, 1, 0, 2])).unwrap();
        let phases = resident.admitted()[0].clone();
        let (pending, _) = reference.refine(resident, &moment, &phases).unwrap();
        let (_, compared) = reference.compare(resident, pending, &one_hot(&[2, 3])).unwrap();
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

/// A stored state that reads the receiving ring: the opening constitution after the deposits of the
/// first `windows` receiving windows of `cells`, at rest.
fn deposited(field: &crate::hnn::Field, cells: &[usize], windows: usize) -> crate::hnn::Constitution {
    let reference = Reference::new(64, OPEN_BUDGET);
    let mut resident = reference.mount(field, &Current::at_rest(field)).unwrap();
    let phases = resident.admitted()[0].clone();
    let (moment, _) = reference.ingest(&mut resident, None, &[]).unwrap();
    for span in phases.windows(cells.len()).unwrap().into_iter().take(windows) {
        let window = &cells[span];
        if window.len() == phases.aperture() {
            let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
            let (staged, _) = reference
                .compare(&mut resident, pending, &one_hot(window))
                .unwrap();
            reference.deposit(&mut resident, staged).unwrap();
        }
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &one_hot(&window[fed..]))
                .unwrap();
            let ingested = ingested.forward.into_present().unwrap();
            fed += ingested.cells;
            if ingested.carry_out {
                let family = resident.admitted().to_vec();
                reference.close_aeon(&mut resident, &family).unwrap();
            }
        }
    }
    resident.constitution().clone()
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
        cells: source(length, 81),
        held_out: vec![2..4, length - 4..length],
    };
    let reference = Reference::new(64, OPEN_BUDGET).with_deadline(6);
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
    for (a, b) in carried.aeons.iter_mut().zip(&rest.aeons) {
        a.state_bits = b.state_bits;
    }
    assert_eq!(carried, rest);
}

/// The reception carry §2.1 and §2.6: under `Carry(Nothing)` every compare writes its consumed
/// word's end as the resident's one carried change, at the field's elapsed ticks (the sum of the
/// junction steps of every earlier word), and the next reception's word opens on its interior with
/// the source rings imposed by the moment: the refine's faces are the read on that opening, and they
/// differ from the read at rest. A second refinement while one is pending is refused (one chain).
#[test]
fn the_carry_passes_each_receptions_end_to_the_next() {
    use crate::hnn::{Absorption, PendingRatio, WordOpening};
    let length = cut_length();
    let field = chain_of(length as u64);
    let cells = source(length, 81);
    let reference =
        Reference::new(64, OPEN_BUDGET).with_reception(Reception::Carry(Absorption::Nothing));
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let phases = resident.admitted()[0].clone();
    let steps = phases.junction_steps();
    let (moment, _) = reference.ingest(&mut resident, None, &[]).unwrap();
    assert!(resident.carried().is_none());
    let mut position = 0;
    let (mut receptions, mut moved) = (0, 0);
    for span in phases.windows(cells.len()).unwrap().into_iter().take(24) {
        let window = &cells[span.clone()];
        if window.len() == phases.aperture() {
            let before = resident.carried().cloned();
            let opening = match &before {
                Some(carry) => WordOpening::Received {
                    carry: carry.clone(),
                    absorption: Absorption::Nothing,
                },
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
            let (_, on) = ratio
                .read_on(&field, &theta, &mut crate::hnn::Charts::new(), &opening)
                .unwrap();
            assert_eq!(faces, on);
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
                let (_, at_rest) = ratio.read(&field, &theta).unwrap();
                moved += usize::from(faces != at_rest);
            }
            if before.is_some() {
                assert!(matches!(
                    reference.refine(&mut resident, &moment, &phases),
                    Err(HnnError::Shape { .. })
                ));
            }
            let (staged, _) = reference
                .compare(&mut resident, pending, &one_hot(window))
                .unwrap();
            receptions += 1;
            let carry = resident.carried().expect("the compare writes the carry");
            assert_eq!(carry.ticks, receptions * steps);
            reference.deposit(&mut resident, staged).unwrap();
        }
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &one_hot(&window[fed..]))
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
}

/// The reception carry §4: a held-out passage is read from the stored state with nothing
/// deposited, so the same passage reads the same whether or not others were read before it, and the
/// stored state is unchanged; under `Carry(Complete)` the read is the read at rest exactly, and under
/// `Carry(Nothing)` the motion carries across the passage's receptions and moves its stations'
/// code.
#[test]
fn each_held_out_passage_is_read_from_the_stored_state() {
    let length = cut_length();
    let field = chain_of(length as u64);
    let theta = deposited(&field, &source(length, 81), 24);
    // Inside one aeon of the chain's joint clock (it carries out at its eleventh cell from rest).
    let cells = source(10, 7);
    let stations = 6..10;
    let read = |reception: Reception, passage: &[usize]| {
        Reference::new(64, OPEN_BUDGET)
            .with_reception(reception)
            .read_passage(&field, &theta, passage, stations.clone())
            .unwrap()
    };
    let rest = read(Reception::Rest, &cells);
    assert_eq!(rest.stations, 4);
    assert!(rest.compares >= 2);
    assert_eq!(read(Reception::Carry(Absorption::Complete), &cells), rest);
    let carried = read(Reception::Carry(Absorption::Nothing), &cells);
    assert_eq!(carried.stations, rest.stations);
    assert_ne!(carried.code, rest.code, "the carry moves the stations' code");
    // Another passage read first changes nothing: every passage mounts the stored state.
    let other = source(10, 11);
    let reference =
        Reference::new(64, OPEN_BUDGET).with_reception(Reception::Carry(Absorption::Nothing));
    reference
        .read_passage(&field, &theta, &other, stations.clone())
        .unwrap();
    assert_eq!(
        reference
            .read_passage(&field, &theta, &cells, stations.clone())
            .unwrap(),
        carried
    );
    assert_eq!(theta, deposited(&field, &source(length, 81), 24));
}
