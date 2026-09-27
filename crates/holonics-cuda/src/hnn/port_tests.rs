//! **The device port against the host reference, return by return** (the parity law of rebuild
//! step 5: every `InteractionReturn` the card's port returns is the reference's, faces, receipts,
//! bits, code lengths, deposits and releases included).
//!
//! [definition] The harness ([`lockstep`]) runs campaign 1's exposure protocol
//! (`holonics::hnn::reference::expose`, design (d)) on the host [`Reference`] and on the card's
//! [`Resident`] side by side, on the same field, constitution and cut, and asserts after every method
//! (ingest, refine, release, compare, deposit or discard, close_aeon, locate_keys, read) that both
//! return the same value, a refusal included. The fast tests read the device port's host-side laws
//! without a card; the lockstep tests are `#[ignore]` and run alone on the card:
//!
//! ```text
//! flock .local/gpu.lock cargo test -p holonics-cuda -- --include-ignored --test-threads=1
//! ```
//!
//! The standing real cut (THE_REBUILD (f)) is private: its lockstep reads it from `HOLONICS_CUT` (the
//! cut file; its manifest beside it), and reports itself skipped when the file is absent.

use std::ops::Range;

use holonics::compression::landmark::context::Letter;
use holonics::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Steps};
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::port::{ExecutionPort, Handle, ReceiptDetail};
use holonics::hnn::reference::ExposedResident;
use holonics::hnn::reference::{Cut, Reference, one_hot};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::{
    Constitution, ConstitutionRead, Current, Field, FieldDeclaration, HnnError, PairPort,
    ReceivingPhases, RingDeclaration, SourceMoment, Word,
};
use holonics::holon::parametron::Carrier;
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{integer, rat};
use holonics::receiver::release::{BeyondTolerance, DecisionRule, WithinTolerance};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::dyadic::{exponent_of, integral, power_of_two};
use super::lattice::NormalMirror;
use super::tests::{Draw, card};
use super::{Resident, Traffic};

// -------------------------------------------------------------------------------------------
// fixtures

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: holonics::geometry::screw::ScrewGenerator::new(
            holonics::geometry::RatVec3::from_i64(0, 0, 1),
            holonics::geometry::RatVec3::zero(),
        ),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn contact(from: usize, to: usize, nodes: usize, exponent: i64) -> ContactDeclaration {
    ContactDeclaration {
        from,
        to,
        channel: (0..nodes).map(|node| (node, node)).collect(),
        admittance: integer(2),
        exponent: integer(exponent),
    }
}

/// The chain control on the quarter turns: rings of periods 2, 3, 2 (locks `{0}`, `{0}`, `∅`),
/// two contacts, source ring 0, `|A| = 4`, `Δ = {1}`, receiver ring 2 with aperture 2.
fn chain_declaration(population: u64) -> FieldDeclaration {
    FieldDeclaration {
        rings: vec![ring(2, vec![0]), ring(3, vec![0]), ring(2, vec![])],
        contacts: vec![contact(0, 1, 2, 2), contact(1, 2, 2, 0)],
        loops: Vec::new(),
        sources: vec![0],
        offsets: vec![1],
        alphabet: 4,
        step: integer(1),
        exponent_grain: 1,
        receivers: vec![ReceiverDeclaration {
            ring: 2,
            aperture: 2,
            tolerance: rat(1, 16),
            depth: 2,
            prior: holonics::compression::landmark::context::StopPrior::half(),
        }],
        crib: CribDeclaration {
            window: 16,
            offset: 1,
        },
        population,
        lattice: Default::default(),
    }
    .by_lattice_rule()
}

/// The chain at its capacity `n*` (the least population it admits).
fn chain() -> Field {
    let probe = Field::declare(chain_declaration(1 << 20)).unwrap();
    Field::declare(chain_declaration(probe.capacity().n_star())).unwrap()
}

/// The small chain control with a loaded source ring whose returned wave has a non-unit dyadic
/// coefficient, and a non-unit hop. It forces the integrated path to carry both splits.
fn loaded_y4_h2_field() -> Field {
    let mut declaration = chain_declaration(1 << 20);
    declaration.rings[0].admittance = integer(4);
    declaration.step = integer(2);
    declaration = declaration.by_lattice_rule();
    let probe = Field::declare(declaration.clone()).unwrap();
    declaration.population = probe.capacity().n_star() as u64;
    Field::declare(declaration.by_lattice_rule()).unwrap()
}

/// A half-integer (`½ℤ`, on every lattice `L ≥ 1`).
fn half(draw: &mut Draw) -> Rat {
    rat((draw.next() % 7) as i64 - 3, 2)
}

fn half_vector(draw: &mut Draw, width: usize) -> Vec<Rat> {
    (0..width).map(|_| half(draw)).collect()
}

fn half_matrix(draw: &mut Draw, rows: usize, columns: usize) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        rows,
        columns,
        (0..rows).map(|_| half_vector(draw, columns)).collect(),
    )
    .unwrap()
}

/// **A generic constitution on half-integers**: every locus drawn (the passive factor, the
/// contrast port, generic slices, a mixed standing, the ports, nonzero pair-port outputs, the
/// channels' factors, and the receiving parametron's landmark tree: a drawn passage
/// deposited at drawn addresses, so the tree's face differs from address to address and from
/// uniform), so every term of the word and its return is exercised from the first window.
fn generic(field: &Field, seed: u64) -> Constitution {
    let mut draw = Draw(seed);
    let a = field.alphabet();
    let mut theta =
        Constitution::initial(field, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET).unwrap();
    for g in 0..field.rings().len() {
        let n = field.ring(g).width();
        let passive = half_matrix(&mut draw, n, n);
        let contrast = half_matrix(&mut draw, n, n);
        let slices = (0..n)
            .map(|_| (half_vector(&mut draw, n), half_vector(&mut draw, n)))
            .collect();
        theta = theta.with_element(g, passive, contrast, slices).unwrap();
        let standing = Some(half_vector(&mut draw, n));
        let source = field.is_source(g).then(|| half_matrix(&mut draw, n, a));
        let receiving = field
            .receivers()
            .iter()
            .any(|r| r.ring == g)
            .then(|| half_matrix(&mut draw, 2 * a, n));
        theta = theta.with_ports(g, standing, source, receiving).unwrap();
        if let Some(empty) = theta.landmarks(g) {
            let mut tree = empty.clone();
            let depth = tree.declaration().depth;
            for _ in 0..24 {
                let address: Vec<Letter> = (0..depth)
                    .map(|_| match draw.below(a + 1) {
                        0 => Letter::Boundary,
                        cell => Letter::Cell(cell - 1),
                    })
                    .collect();
                tree.receive(&address, draw.below(a)).unwrap();
            }
            theta = theta.with_tree(g, tree).unwrap();
        }
        if field.is_source(g) {
            for &offset in field.offsets() {
                let pair = PairPort::new(
                    (0..n).map(|_| half_vector(&mut draw, n)).collect(),
                    (0..n).map(|_| half_vector(&mut draw, a)).collect(),
                    (0..n).map(|_| half_vector(&mut draw, a)).collect(),
                )
                .unwrap();
                theta = theta.with_pair(g, offset, pair).unwrap();
            }
        }
    }
    for c in 0..field.contacts().len() {
        let k = field.contact(c).width();
        theta = theta
            .with_channel(
                c,
                half_matrix(&mut draw, k, k),
                half_matrix(&mut draw, k, k),
                half_matrix(&mut draw, k, k),
            )
            .unwrap();
    }
    theta
}

/// A periodic source with a little noise over `alphabet` classes.
fn source(length: usize, alphabet: usize, seed: u64) -> Vec<usize> {
    let mut draw = Draw(seed);
    (0..length)
        .map(|k| {
            if draw.below(8) == 0 {
                draw.below(alphabet)
            } else {
                [0, 1, 2, 1][k % 4] % alphabet
            }
        })
        .collect()
}

fn releasing() -> DecisionRule {
    DecisionRule::new(
        "release at the grain",
        WithinTolerance::Release,
        BeyondTolerance::Hold,
    )
}

// -------------------------------------------------------------------------------------------
// the lockstep

/// Assert two results equal, a refusal included, and hand back the host's value.
fn same<T: PartialEq + std::fmt::Debug>(
    what: &str,
    host: Result<T, HnnError>,
    card: Result<T, HnnError>,
) -> Option<T> {
    match (host, card) {
        (Ok(host), Ok(card)) => {
            assert_eq!(
                host, card,
                "{what}: the card's return differs from the reference's"
            );
            Some(host)
        }
        (Err(host), Err(card)) => {
            assert_eq!(
                host, card,
                "{what}: the card refused otherwise than the reference"
            );
            None
        }
        (Ok(_), Err(card)) => {
            panic!("{what}: the card refused where the reference returned: {card}")
        }
        (Err(host), Ok(_)) => {
            panic!("{what}: the card returned where the reference refused: {host}")
        }
    }
}

/// [definition] **What a lockstep compared**: the returns asserted equal, by method, and the card
/// port's traffic.
#[derive(Debug, Default)]
struct Compared {
    ingests: u64,
    refines: u64,
    releases: u64,
    compares: u64,
    deposits: u64,
    discards: u64,
    boundaries: u64,
    keys: u64,
    reads: u64,
    /// The cells the deposits added to the receiving parametron's tree (the landmark tree).
    landmarks: u64,
    /// Declared resonator material families whose gains changed across a deposit.
    resonator_material_changes: u64,
    traffic: Traffic,
    /// The normal-law mirror's tally: every prox step carried, declined by reason or skipped.
    mirror: NormalMirror,
}

/// **Run the exposure protocol on both ports in lockstep** (module header) over at most `windows`
/// receiving windows of `cut`, from `constitution` (the declared initial one when `None`), with a
/// release at every `release_every`-th window. Every return is asserted equal.
fn lockstep(
    field: &Field,
    cut: &Cut,
    windows: u64,
    constitution: Option<Constitution>,
    release_every: u64,
) -> Compared {
    let card = card();
    let host = Reference::campaign_one();
    // The lockstep runs the normal-law mirror (the parity test it moved into, off the exposure's
    // path), and reports its tally.
    let device = Resident::campaign_one(&card).with_normal_mirror();
    let current = Current::at_rest(field);
    let (mut h, mut d) = match constitution {
        Some(theta) => (
            host.mount_with(field, &current, theta.clone()).unwrap(),
            device.mount_with(field, &current, theta).unwrap(),
        ),
        None => (
            host.mount(field, &current).unwrap(),
            device.mount(field, &current).unwrap(),
        ),
    };
    let mut compared = Compared::default();
    let phases = h.admitted()[0].clone();
    let family = h.admitted().to_vec();
    let aperture = phases.aperture();
    let crib = field.crib();
    let cells = &cut.cells;
    let (hm, _) = same(
        "the open",
        host.ingest(&mut h, None, &[]),
        device.ingest(&mut d, None, &[]),
    )
    .expect("the moment opens");
    let rule = releasing();
    let mut aeon_start = 0usize;
    let mut position = 0usize;
    let mut window = 0u64;
    while position < cells.len() && window < windows {
        let end = (position + aperture).min(cells.len());
        let span = &cells[position..end];
        if span.len() == aperture {
            window += 1;
            let refined = same(
                "refine",
                host.refine(&mut h, &hm, &phases),
                device.refine(&mut d, &hm, &phases),
            );
            compared.refines += 1;
            let Some((pending, _)) = refined else { break };
            if release_every > 0 && window.is_multiple_of(release_every) {
                same(
                    "release",
                    host.release(&mut h, &pending, &rule),
                    device.release(&mut d, &pending, &rule),
                );
                compared.releases += 1;
            }
            let compared_return = same(
                "compare",
                host.compare(&mut h, pending, &one_hot(span)),
                device.compare(&mut d, pending, &one_hot(span)),
            );
            compared.compares += 1;
            let Some((staged, _)) = compared_return else {
                break;
            };
            // Prequential scoring: every compared window is deposited, the held-out tail
            // included; only the budget stop discards.
            if h.stopped().is_some() {
                same(
                    "discard",
                    host.discard(&mut h, Handle::Staged(staged)),
                    device.discard(&mut d, Handle::Staged(staged)),
                );
                compared.discards += 1;
            } else {
                let resonators_before: Vec<_> = (0..field.rings().len())
                    .map(|ring| h.constitution().ring_resonator(ring).cloned())
                    .collect();
                let deposited = same(
                    "deposit",
                    host.deposit(&mut h, staged),
                    device.deposit(&mut d, staged),
                );
                compared.deposits += 1;
                // The cells a deposit added to the tree (the landmark tree), and the published
                // constitutions, the tree among them, equal on both ports.
                if let Some(reading) =
                    deposited.and_then(|returned| returned.deposit.into_present())
                {
                    compared.landmarks += reading.landmarks;
                }
                compared.resonator_material_changes += (0..field.rings().len())
                    .filter(|&ring| {
                        resonators_before[ring] != h.constitution().ring_resonator(ring).cloned()
                    })
                    .count() as u64;
                assert_eq!(
                    h.constitution(),
                    holonics::hnn::reference::ExposedResident::constitution(&d),
                    "the published constitutions"
                );
            }
        }
        let mut fed = 0;
        while fed < span.len() {
            let ingested = same(
                "ingest",
                host.ingest(&mut h, Some(&hm), &one_hot(&span[fed..])),
                device.ingest(&mut d, Some(&hm), &one_hot(&span[fed..])),
            )
            .expect("the ingest returns");
            compared.ingests += 1;
            assert_eq!(h.address(), d.address(), "the active suffix addresses");
            let ingested = ingested.1.forward.into_present().expect("ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                same(
                    "close_aeon",
                    host.close_aeon(&mut h, &family),
                    device.close_aeon(&mut d, &family),
                );
                compared.boundaries += 1;
                let at = position + fed;
                let span = cut.closing_crib(aeon_start, at, crib.window);
                if span.len() > crib.offset {
                    same(
                        "locate_keys",
                        host.locate_keys(&mut h, &one_hot(&cells[span.clone()]), crib.offset),
                        device.locate_keys(&mut d, &one_hot(&cells[span]), crib.offset),
                    );
                    compared.keys += 1;
                }
                aeon_start = at;
            }
        }
        position = end;
    }
    same("read", host.read(&h), device.read(&d));
    compared.reads += 1;
    // The state's bits, the tally and the ledger read the same.
    assert_eq!(
        holonics::hnn::reference::ExposedResident::state_bits(&h),
        holonics::hnn::reference::ExposedResident::state_bits(&d)
    );
    assert_eq!(
        h.tally(),
        holonics::hnn::reference::ExposedResident::tally(&d)
    );
    compared.traffic = d.traffic();
    compared.mirror = device
        .normal_mirror()
        .expect("the lockstep runs the mirror");
    println!(
        "the normal-law mirror: {} carried; {} declined (empty {}, off the dyadics {}, past a word {}, the kernel {}, the read {}); {} skipped (a locus stepped again {}, no normal law {})",
        compared.mirror.carried,
        compared.mirror.declined(),
        compared.mirror.empty,
        compared.mirror.off_dyadic,
        compared.mirror.past_word,
        compared.mirror.kernel,
        compared.mirror.read,
        compared.mirror.skipped(),
        compared.mirror.repeated,
        compared.mirror.lawless,
    );
    compared
}

fn cut_of(cells: Vec<usize>, held_out: Range<usize>) -> Cut {
    Cut {
        cells,
        held_out: vec![held_out],
    }
}

// -------------------------------------------------------------------------------------------
// fast tests: the port's host-side laws

/// The dyadic readings the port declares its scales with: a power of two's exponent, a dyadic
/// value's exponent, and the integral chart, each exact; anything else is refused by `None`.
#[test]
fn the_dyadic_readings_are_exact() {
    assert_eq!(power_of_two(&integer(1)), Some(0));
    assert_eq!(power_of_two(&integer(8)), Some(3));
    assert_eq!(power_of_two(&rat(1, 4)), Some(-2));
    assert_eq!(power_of_two(&rat(3, 4)), None);
    assert_eq!(power_of_two(&integer(0)), None);
    assert_eq!(exponent_of(&rat(3, 8)), Some(3));
    assert_eq!(exponent_of(&rat(-5, 1)), Some(0));
    assert_eq!(exponent_of(&rat(1, 6)), None);
    let (numerators, denominator) = integral(&[rat(1, 2), rat(-1, 3), integer(2)]);
    assert_eq!(denominator, BigInt::from(6));
    assert_eq!(
        numerators,
        vec![BigInt::from(3), BigInt::from(-2), BigInt::from(12)]
    );
}

/// The landmark tree on the card's publication (no card needed to form it): the receiving parametron's
/// tree is not a published locus of the word (its own mirror, `tree::CardTree`, carries it); the
/// reference reads it from the constitution at compare, at each phase's causal address and in cell
/// order (phase 1 after phase 0's target is deposited, on a working overlay), and the device's
/// formula is the reference's (`PendingRatio::against`): the wave's faces plus the tree's grain
/// logits, the tree's faces the class faces of the mirror's splits.
#[test]
fn the_tree_is_read_at_each_phases_address_in_cell_order() {
    let field = chain();
    let theta = generic(&field, 5);
    assert!(super::publication::Loci::of(&field, &theta).is_ok());
    let tree = theta.landmarks(2).unwrap();
    assert!(tree.passed() > 0);
    assert!(theta.landmarks(0).is_none() && theta.landmarks(1).is_none());
    let current = Current::at_rest(&field);
    let phases =
        holonics::hnn::ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0])
            .unwrap();
    let moment = holonics::hnn::SourceMoment::open(&field, &current);
    let mut address = holonics::hnn::ActiveAddress::boundary(phases.depth());
    address.receive(3).unwrap();
    let pending =
        holonics::hnn::PendingRatio::produce(&current, &moment, &address, &phases, 0).unwrap();
    let (_, wave) = pending.read(&field, &theta).unwrap();
    let against = pending.against(&theta, &wave, &[1, 2]).unwrap();
    let trees = phases.tree_faces(&theta, &address, &[1, 2]).unwrap();
    assert_eq!(against.trees, trees);
    assert_eq!(against.faces, phases.combine(&wave, &trees).unwrap());
    let addresses = pending.addresses(&[1, 2]).unwrap();
    assert_eq!(addresses[1], vec![Letter::Cell(1), Letter::Cell(3)]);
    let mut deposited = tree.clone();
    deposited.deposit(&addresses[0], 1).unwrap();
    assert_eq!(trees[1], deposited.face(&addresses[1], 16).unwrap());
    assert_eq!(
        theta.landmarks(2).unwrap(),
        tree,
        "the published tree is unchanged"
    );
}

// -------------------------------------------------------------------------------------------
// the lockstep on the card

/// The chain at its capacity from its declared initial constitution: every window refined,
/// released, compared and deposited, the held-out tail included (prequential scoring), the aeons closed and
/// keys located; every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_on_the_chain() {
    let field = chain();
    let population = field.population() as usize;
    let cells = source(population, field.alphabet(), 3);
    let held = population - 8;
    let compared = lockstep(&field, &cut_of(cells, held..population), u64::MAX, None, 3);
    println!("chain, declared constitution: {compared:?}");
    assert!(compared.boundaries > 0 && compared.keys > 0 && compared.deposits > 0);
    // Every deposited window added its two targets to the tree (the landmark tree).
    assert_eq!(compared.landmarks, 2 * compared.deposits);
}

/// The chain from a generic constitution on half-integers (every locus live: the contrast port,
/// the pair port's outputs, the channels' forms): every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_on_a_generic_constitution() {
    let field = chain();
    let population = field.population() as usize;
    for seed in [5u64, 11] {
        let cells = source(population, field.alphabet(), seed);
        let theta = generic(&field, seed);
        let compared = lockstep(
            &field,
            &cut_of(cells, population - 6..population),
            12,
            Some(theta),
            2,
        );
        println!("chain, generic constitution {seed}: {compared:?}");
        assert!(compared.deposits > 0);
        assert_eq!(compared.landmarks, 2 * compared.deposits);
    }
}

/// Campaign 1's declared field on a drawn byte cut of its capacity (`n* = 6,148` cells): the first
/// eight windows, every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_on_campaign_one() {
    let probe = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let n_star = probe.capacity().n_star() as usize;
    let field = Field::declare(FieldDeclaration::campaign_one(n_star as u64)).unwrap();
    let mut draw = Draw(7);
    let cells: Vec<usize> = (0..n_star).map(|_| draw.below(256)).collect();
    let compared = lockstep(&field, &cut_of(cells, n_star - 1_190..n_star), 8, None, 4);
    println!("campaign 1, drawn bytes: {compared:?}");
    assert_eq!(compared.compares, 8);
    assert_eq!(compared.landmarks, 16);
}

/// **Campaign 2's physics through the port** (the hardware-surfaces rule): campaign 1's field with a resonator on
/// every ring (`physics_tests::resonant`) and a certified boost on contact 0 (one negative
/// stiffness column), on a drawn byte cut: every return the reference's, the refine receipts'
/// resonator balances (the loaded word's ticks decoded by `crate::hnn::readout`)
/// and the published constitutions after every deposit included (the card's stiffness is the signed
/// one, `publication`), and the normal laws' prox steps the card carried in the deposits
/// (`crate::hnn::lattice::normal_deposit_on_card`, the mirror the GPU suite runs, its `X̂f` read
/// through the host's successor chart) read equal to the host's successor, with its declines and
/// skips counted and reported.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_with_resonators_and_a_boost() {
    let probe = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let n_star = probe.capacity().n_star() as usize;
    let field = Field::declare(FieldDeclaration::campaign_one(n_star as u64)).unwrap();
    let width = field.contact(0).width();
    let theta = super::physics_tests::resonant(&field)
        .with_contact_signature(&field, 0, (0..width).map(|j| j != 0).collect())
        .unwrap();
    let mut draw = Draw(13);
    let cells: Vec<usize> = (0..n_star).map(|_| draw.below(256)).collect();
    let compared = lockstep(
        &field,
        &cut_of(cells, n_star - 1_190..n_star),
        8,
        Some(theta),
        4,
    );
    println!("campaign 1 with resonators and a boost, drawn bytes: {compared:?}");
    assert_eq!(compared.compares, 8);
    assert!(compared.mirror.carried > 0);
    // Coarse gains may stay in their lattice cells on these first windows. The returned
    // covectors, carried statistics/remainders, and successor constitution are checked above;
    // the count of visible gain changes is reported rather than assumed positive.
}

/// A non-unit return and hop exercise the loaded wave's independent storage split and the
/// reverse solve/state recurrence through a pumped, non-diagonal parametron. The host fixture first
/// proves that the loaded source changes the receiving face and produces a nonzero split receipt;
/// then every card return, including a deferred compare/deposit, is checked against it.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_loaded_source_matches_with_y4_and_hop_two() {
    let field = loaded_y4_h2_field();
    let width = field.contact(0).width();
    let receiver = field.receivers()[0].ring;
    let receiver_width = field.ring(receiver).width();
    let receiving = ExactRatMatrix::shaped(
        2 * field.alphabet(),
        receiver_width,
        (0..2 * field.alphabet())
            .map(|row| {
                (0..receiver_width)
                    .map(|column| {
                        if row == column {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let baseline = Constitution::initial(&field, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ports(receiver, None, None, Some(receiving))
        .unwrap()
        .with_contact_signature(&field, 0, (0..width).map(|j| j != 0).collect())
        .unwrap();
    let pump = PumpDeclaration::new(
        rat(1, 8),
        Carrier::new(Rat::one(), Rat::zero()).unwrap(),
        PumpStep::Half,
    )
    .unwrap();
    let material =
        ResonatorMaterial::of_parametron(field.ring(0).parametron(), &rat(1, 4), Some(pump))
            .unwrap();
    let theta = baseline
        .clone()
        .with_ring_resonator(&field, 0, material)
        .unwrap();
    let mut draw = Draw(29);
    let cells: Vec<usize> = (0..field.capacity().n_star() as usize)
        .map(|_| draw.below(field.alphabet()))
        .collect();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    moment.ingest(&field, &mut current, &cells).unwrap();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let read = |constitution: &Constitution| {
        let mut word = Word::open(&field, constitution, &current, &moment).unwrap();
        let anchors = word.forward(&phases).unwrap();
        let faces = anchors
            .iter()
            .map(|anchor| phases.read(&field, constitution, &current, anchor).unwrap())
            .collect::<Vec<_>>();
        (faces, word.release().unwrap())
    };
    let (baseline_faces, _) = read(&baseline);
    let (loaded_faces, loaded) = read(&theta);
    assert_ne!(loaded_faces, baseline_faces);
    assert!(
        loaded
            .balances
            .iter()
            .any(|balance| !balance.loaded_split.is_zero())
    );

    let n_star = field.capacity().n_star() as usize;
    let compared = lockstep(
        &field,
        &cut_of(cells, n_star.saturating_sub(16)..n_star),
        8,
        Some(theta),
        2,
    );
    assert_eq!(compared.compares, 8);
    assert!(compared.mirror.carried > 0);
}

/// A finite, valid staged deposit may still fail when its successor is read. The host fails while
/// carrying the resulting exponent; the card may refuse earlier while forming its bounded
/// publication. In either case the old constitution, staged handle and every card mirror remain at
/// their predecessor, and a fresh read at the same moment/targets agrees with the old host tree.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn late_successor_read_refusal_restores_host_and_card_predecessors() {
    let field = chain();
    let steps = Steps {
        proxy: Rat::from_integer(BigInt::from(1u8) << 128usize),
        factor: Rat::zero(),
    };
    let theta = Constitution::initial(&field, steps.clone(), u64::MAX).unwrap();
    let host = Reference::new(64, steps.clone(), u64::MAX);
    let card = card();
    let device = Resident::new(&card, 64, steps, u64::MAX);
    let current = Current::at_rest(&field);
    let mut h = host.mount_with(&field, &current, theta.clone()).unwrap();
    let mut d = device.mount_with(&field, &current, theta).unwrap();

    let (moment, _) = same(
        "open and ingest a tiny source moment",
        host.ingest(&mut h, None, &one_hot(&[0])),
        device.ingest(&mut d, None, &one_hot(&[0])),
    )
    .unwrap();
    let phases = h.admitted()[0].clone();
    let (pending, _) = same(
        "refine before staging the large finite update",
        host.refine(&mut h, &moment, &phases),
        device.refine(&mut d, &moment, &phases),
    )
    .unwrap();
    let (staged, compared) = same(
        "stage a valid comparison",
        host.compare(&mut h, pending, &one_hot(&[0, 1])),
        device.compare(&mut d, pending, &one_hot(&[0, 1])),
    )
    .unwrap();
    let deposit = compared
        .deposit
        .into_present()
        .expect("compare staged a deposit");
    assert!(!deposit.linear().is_empty());
    assert!(!deposit.landmarks().is_empty());

    let host_theta = h.constitution().clone();
    let device_theta = d.constitution().clone();
    let host_current = h.current().clone();
    let device_current = d.current().clone();
    let host_charts = h.charts().clone();
    let host_ledger = h.ledger().clone();
    let host_bits = h.state_bits();
    let device_bits = d.state_bits();
    let host_handles = host.read(&h).unwrap().2;
    let device_handles = device.read(&d).unwrap().2;
    assert_eq!(host_handles, device_handles);
    assert!(
        host_handles
            .iter()
            .any(|(handle, _)| *handle == Handle::Staged(staged))
    );

    let host_refusal = host.deposit(&mut h, staged);
    let device_refusal = device.deposit(&mut d, staged);
    assert!(host_refusal.is_err() && device_refusal.is_err());
    assert!(!matches!(
        host_refusal,
        Err(HnnError::ConstitutionBudget { .. })
    ));
    assert!(!matches!(
        device_refusal,
        Err(HnnError::ConstitutionBudget { .. })
    ));
    assert!(h.stopped().is_none() && d.stopped().is_none());
    assert_eq!(h.constitution(), &host_theta);
    assert_eq!(d.constitution(), &device_theta);
    assert_eq!(h.current(), &host_current);
    assert_eq!(d.current(), &device_current);
    assert_eq!(h.charts(), &host_charts);
    assert_eq!(h.ledger(), &host_ledger);
    assert_eq!(h.state_bits(), host_bits);
    assert_eq!(d.state_bits(), device_bits);
    let host_handles_after = host.read(&h).unwrap().2;
    let device_handles_after = device.read(&d).unwrap().2;
    assert_eq!(host_handles_after, host_handles);
    assert_eq!(device_handles_after, device_handles);

    // The card's tree and chart mirrors must now answer the same fresh read as the unchanged host
    // constitution. This exercises the rollback, not just the public handles and state counts.
    let (host_pending, _) = host.refine(&mut h, &moment, &phases).unwrap();
    let (device_pending, _) = device.refine(&mut d, &moment, &phases).unwrap();
    assert_eq!(host_pending, device_pending);
    let retried = same(
        "compare again after the late refusal",
        host.compare(&mut h, host_pending, &one_hot(&[0, 1])),
        device.compare(&mut d, device_pending, &one_hot(&[0, 1])),
    );
    assert!(retried.is_some());
}

/// The standing real cut's manifest numbers (its population and held-out range).
fn manifest(path: &str) -> Option<(usize, Range<usize>)> {
    let manifest_path = path
        .strip_suffix(".bin")
        .map_or_else(|| format!("{path}.json"), |stem| format!("{stem}.json"));
    #[allow(clippy::disallowed_methods)]
    let manifest = std::fs::read_to_string(manifest_path).ok()?;
    let numbers_after = |key: &str| -> Vec<usize> {
        let start = manifest.find(key).expect("the manifest names the key") + key.len();
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
    Some((population, range[0]..range[1]))
}

/// **The standing real cut's first 24 windows** (THE_REBUILD (f); the cut file from `HOLONICS_CUT`):
/// every return the reference's.
#[test]
#[ignore = "needs the CUDA card and the private standing cut (HOLONICS_CUT); run alone"]
fn the_card_port_returns_the_reference_on_the_standing_cut() {
    let Ok(path) = std::env::var("HOLONICS_CUT") else {
        println!("skipped: HOLONICS_CUT names no standing cut file");
        return;
    };
    #[allow(clippy::disallowed_methods)]
    let Ok(bytes) = std::fs::read(&path) else {
        println!("skipped: the standing cut {path} is not readable");
        return;
    };
    let (population, held_out) = manifest(&path).expect("the cut's manifest");
    assert_eq!(bytes.len(), population);
    let field = Field::declare(FieldDeclaration::campaign_one(population as u64)).unwrap();
    let cells: Vec<usize> = bytes.iter().map(|b| usize::from(*b)).collect();
    let compared = lockstep(&field, &cut_of(cells, held_out), 24, None, 6);
    println!("standing real cut, 24 windows: {compared:?}");
    assert_eq!(compared.compares, 24);
}

/// A refusal is returned alike: a compare against a target of the wrong length, an unknown handle.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_refuses_as_the_reference() {
    let field = chain();
    let card = card();
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(&card);
    let current = Current::at_rest(&field);
    let mut h = host.mount(&field, &current).unwrap();
    let mut d = device.mount(&field, &current).unwrap();
    let (moment, _) = host.ingest(&mut h, None, &[]).unwrap();
    device.ingest(&mut d, None, &[]).unwrap();
    same(
        "ingest",
        host.ingest(&mut h, Some(&moment), &one_hot(&[0, 1, 2, 3])),
        device.ingest(&mut d, Some(&moment), &one_hot(&[0, 1, 2, 3])),
    );
    let phases = h.admitted()[0].clone();
    let (pending, _) = same(
        "refine",
        host.refine(&mut h, &moment, &phases),
        device.refine(&mut d, &moment, &phases),
    )
    .unwrap();
    same(
        "a short target",
        host.compare(&mut h, pending, &one_hot(&[1])),
        device.compare(&mut d, pending, &one_hot(&[1])),
    );
    same(
        "an unknown handle",
        host.discard(&mut h, Handle::Staged(holonics::hnn::port::StagedId(999))),
        device.discard(&mut d, Handle::Staged(holonics::hnn::port::StagedId(999))),
    );
    // The refused compare left the pending ratio open on both: it compares now.
    let compared = same(
        "compare",
        host.compare(&mut h, pending, &one_hot(&[1, 2])),
        device.compare(&mut d, pending, &one_hot(&[1, 2])),
    );
    assert!(compared.is_some());
    let _ = ReceiptDetail::Boundary;
}

/// Both ports mounted on one field and constitution, their moment open.
struct Pair<'c> {
    host: Reference,
    device: Resident<'c>,
    h: holonics::hnn::Resident,
    d: super::Mounted<'c>,
    moment: holonics::hnn::port::MomentId,
}

fn pair<'c>(card: &'c super::Card, field: &Field, theta: Option<Constitution>) -> Pair<'c> {
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(card);
    let current = Current::at_rest(field);
    let (mut h, mut d) = match theta {
        Some(theta) => (
            host.mount_with(field, &current, theta.clone()).unwrap(),
            device.mount_with(field, &current, theta).unwrap(),
        ),
        None => (
            host.mount(field, &current).unwrap(),
            device.mount(field, &current).unwrap(),
        ),
    };
    let (moment, _) = same(
        "the open",
        host.ingest(&mut h, None, &[]),
        device.ingest(&mut d, None, &[]),
    )
    .unwrap();
    Pair {
        host,
        device,
        h,
        d,
        moment,
    }
}

/// Ingest cells on both until they are all taken, closing each aeon at its carry-out on the
/// declared family (and locating no keys); the boundaries' returns asserted equal.
fn feed(pair: &mut Pair<'_>, cells: &[usize]) {
    let family = pair.h.admitted().to_vec();
    let mut fed = 0;
    while fed < cells.len() {
        let (_, ingested) = same(
            "ingest",
            pair.host
                .ingest(&mut pair.h, Some(&pair.moment), &one_hot(&cells[fed..])),
            pair.device
                .ingest(&mut pair.d, Some(&pair.moment), &one_hot(&cells[fed..])),
        )
        .unwrap();
        let ingested = ingested.forward.into_present().unwrap();
        fed += ingested.cells;
        if ingested.carry_out {
            same(
                "close_aeon",
                pair.host.close_aeon(&mut pair.h, &family),
                pair.device.close_aeon(&mut pair.d, &family),
            );
        }
    }
}

/// Several pending ratios alive across ingests (so their words open at different lifts, and the
/// contacts' charts at different carries), compared after deposits moved the constitution (so each
/// later compare's kept read is stale and the card reads its word again), a pending ratio and the
/// moment discarded: every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_on_deferred_compares() {
    let field = chain();
    let card = card();
    let mut both = pair(&card, &field, Some(generic(&field, 17)));
    let phases = both.h.admitted()[0].clone();
    let cells = source(40, field.alphabet(), 17);
    let mut pending = Vec::new();
    for chunk in cells.chunks(4).take(5) {
        let (id, _) = same(
            "refine",
            both.host.refine(&mut both.h, &both.moment, &phases),
            both.device.refine(&mut both.d, &both.moment, &phases),
        )
        .unwrap();
        pending.push((id, [chunk[0], chunk[1]]));
        feed(&mut both, chunk);
    }
    for (index, (id, targets)) in pending.iter().enumerate() {
        if index == 2 {
            same(
                "discard a pending ratio",
                both.host.discard(&mut both.h, Handle::Pending(*id)),
                both.device.discard(&mut both.d, Handle::Pending(*id)),
            );
            continue;
        }
        let (staged, _) = same(
            "compare",
            both.host.compare(&mut both.h, *id, &one_hot(targets)),
            both.device.compare(&mut both.d, *id, &one_hot(targets)),
        )
        .unwrap();
        same(
            "deposit",
            both.host.deposit(&mut both.h, staged),
            both.device.deposit(&mut both.d, staged),
        );
    }
    same("read", both.host.read(&both.h), both.device.read(&both.d));
    same(
        "discard the moment",
        both.host.discard(&mut both.h, Handle::Moment(both.moment)),
        both.device
            .discard(&mut both.d, Handle::Moment(both.moment)),
    );
    same("read", both.host.read(&both.h), both.device.read(&both.d));
}

/// A collapse onto an empty admitted family releases every locus the declared receivers'
/// diamonds retained: the descended constitution is published on the card at the same commit, the
/// arrived targets are read again on it (the first law's exchange step), a pending ratio is
/// refused with its separator and a staged deposit with the loci it would reach; then a word reads
/// the collapsed medium. Every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_through_a_releasing_collapse() {
    let field = chain();
    let card = card();
    let mut both = pair(&card, &field, Some(generic(&field, 23)));
    let phases = both.h.admitted()[0].clone();
    let cells = source(64, field.alphabet(), 23);
    let mut position = 0;
    // Refine, compare and deposit until the joint clock carries out.
    loop {
        let (id, _) = same(
            "refine",
            both.host.refine(&mut both.h, &both.moment, &phases),
            both.device.refine(&mut both.d, &both.moment, &phases),
        )
        .unwrap();
        let targets = one_hot(&cells[position..position + 2]);
        let (staged, _) = same(
            "compare",
            both.host.compare(&mut both.h, id, &targets),
            both.device.compare(&mut both.d, id, &targets),
        )
        .unwrap();
        same(
            "deposit",
            both.host.deposit(&mut both.h, staged),
            both.device.deposit(&mut both.d, staged),
        );
        let (_, ingested) = same(
            "ingest",
            both.host.ingest(&mut both.h, Some(&both.moment), &targets),
            both.device
                .ingest(&mut both.d, Some(&both.moment), &targets),
        )
        .unwrap();
        let ingested = ingested.forward.into_present().unwrap();
        position += ingested.cells;
        if ingested.carry_out {
            break;
        }
        assert!(
            position + 2 <= cells.len(),
            "the joint clock carries out within the cut"
        );
    }
    // A pending ratio and a staged deposit open across the boundary.
    let (id, _) = same(
        "refine",
        both.host.refine(&mut both.h, &both.moment, &phases),
        both.device.refine(&mut both.d, &both.moment, &phases),
    )
    .unwrap();
    let (other, _) = same(
        "refine",
        both.host.refine(&mut both.h, &both.moment, &phases),
        both.device.refine(&mut both.d, &both.moment, &phases),
    )
    .unwrap();
    same(
        "compare",
        both.host.compare(&mut both.h, other, &one_hot(&[1, 2])),
        both.device.compare(&mut both.d, other, &one_hot(&[1, 2])),
    );
    let boundary = same(
        "close_aeon onto no receiver",
        both.host.close_aeon(&mut both.h, &[]),
        both.device.close_aeon(&mut both.d, &[]),
    )
    .unwrap();
    let released = &boundary.forward.present().unwrap().collapse.released;
    assert!(!released.is_empty(), "the collapse releases loci");
    same(
        "compare a refused pending ratio",
        both.host.compare(&mut both.h, id, &one_hot(&[0, 1])),
        both.device.compare(&mut both.d, id, &one_hot(&[0, 1])),
    );
    let (fresh, _) = same(
        "refine on the collapsed medium",
        both.host.refine(&mut both.h, &both.moment, &phases),
        both.device.refine(&mut both.d, &both.moment, &phases),
    )
    .unwrap();
    same(
        "release on the collapsed medium",
        both.host.release(&mut both.h, &fresh, &releasing()),
        both.device.release(&mut both.d, &fresh, &releasing()),
    );
    same(
        "compare on the collapsed medium",
        both.host.compare(&mut both.h, fresh, &one_hot(&[2, 3])),
        both.device.compare(&mut both.d, fresh, &one_hot(&[2, 3])),
    );
    same("read", both.host.read(&both.h), both.device.read(&both.d));
}
