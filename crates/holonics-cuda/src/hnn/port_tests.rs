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
//! [historical; retired October 5 with THE_MACHINE guard 9 at the field's entries] The standing real
//! cut's lockstep read the private cut's bytes into campaign 1 through the residue chart; a byte
//! enters only through a founded encoding, so it has no route here (source at
//! [`f91666c0`](https://github.com/brandonrdug/holonics/blob/f91666c0/crates/holonics-cuda/src/hnn/port_tests.rs)).
//! Every lockstep reads a known truth's cells through its declared identity (`KnownTruth`,
//! `Encoded::identity`).

use std::ops::Range;

use holonics::compression::landmark::context::Letter;
use holonics::hnn::Encoded;
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::port::{ExecutionPort, Handle, ReceiptDetail};
use holonics::hnn::reference::ExposedResident;
use holonics::hnn::reference::{Cut, Reception, Reference};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::{
    Absorption, Constitution, ConstitutionRead, Current, Field, FieldDeclaration, HnnError,
    PairPort, ReceivingPhases, ReceptionCarry, RingDeclaration, SourceMoment, Word,
};
use holonics::holarchy::terrain::KnownTruth;
use holonics::holon::parametron::Carrier;
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{integer, rat};
use holonics::receiver::release::{BeyondTolerance, DecisionRule, WithinTolerance};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

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

/// The chain control on the quarter turns: rings of periods 4, 3, 2 (locks `{0, 2}`, `{0}`, `∅`; the
/// source ring's period 4 holds the four classes without a fold, THE_MACHINE guard 9),
/// two contacts, source ring 0, `|A| = 4`, `Δ = {1}`, receiver ring 2 with aperture 2.
fn chain_declaration(population: u64) -> FieldDeclaration {
    FieldDeclaration {
        founded: Vec::new(),
        founding: false,
        rings: vec![ring(4, vec![0, 2]), ring(3, vec![0]), ring(2, vec![])],
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
            mass: 1,
            base: holonics::compression::landmark::context::BaseMeasure::Even,
            receiving_prior: 0,
            ratio: holonics::compression::landmark::context::RatioLaw::Carried,
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

/// The tiny native finite-comparison fixture: two source/receiver stations and a one-class
/// aperture, with no pre-existing receiving material so the paired layout can be bound lawfully.
fn paired_candidate_field() -> Field {
    let mut declaration = FieldDeclaration::campaign_one(1024);
    declaration.rings.truncate(2);
    for (ring, period) in declaration.rings.iter_mut().zip([2u64, 3]) {
        ring.period = period;
        ring.placements = (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect();
        ring.reflector = (0..period)
            .map(|node| ((period - node) % period) as usize)
            .collect();
    }
    declaration.contacts.truncate(1);
    declaration.contacts[0].channel = vec![(0, 0), (1, 1)];
    declaration.loops.clear();
    declaration.alphabet = 2;
    declaration.receivers[0].ring = 1;
    declaration.receivers[0].depth = 2;
    declaration.receivers[0].aperture = 1;
    declaration.crib.window = 2;
    declaration.lattice.clear();
    Field::declare(declaration.by_lattice_rule()).unwrap()
}

/// Same field law and word precision as `chain`, with an explicitly finer declared receiving
/// material lattice so test maps containing tiny exact coefficients remain admissible.
fn return_precision_chain() -> Field {
    let mut probe_declaration = chain_declaration(1 << 20);
    probe_declaration
        .lattice
        .insert(holonics::hnn::Locus::ReceivingMap(2), 48);
    let probe = Field::declare(probe_declaration).unwrap();
    let mut declaration = chain_declaration(probe.capacity().n_star());
    declaration
        .lattice
        .insert(holonics::hnn::Locus::ReceivingMap(2), 48);
    Field::declare(declaration).unwrap()
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
    let mut theta = Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap();
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
                if let Some(partition) = field.receiving_context(g) {
                    use holonics::compression::landmark::context::{
                        ObservationPath, ObservedAddress,
                    };
                    use holonics::hnn::receiving::{
                        ObservationPartition, ReceivingRead, section_bits,
                    };
                    // This generic fixture draws a receiving carrier, then reads its declared
                    // partition before drawing the target. It is a tree preconditioning fixture,
                    // not a claim that these samples were produced by an executed source word.
                    let anchor = half_vector(&mut draw, n);
                    let observation = match partition {
                        ObservationPartition::SourceFramingRouteV1 => panic!("this wave-only fixture has no authentic SourceMoment framing producer"),
                        ObservationPartition::ReceivingSection => partition
                            .path(section_bits(field, g, &anchor).unwrap())
                            .unwrap(),
                        ObservationPartition::MaximumRealGrainSet => {
                            let grain = tree.declaration().grain;
                            let logits = theta.receiving_map(g).unwrap().apply(&anchor).unwrap();
                            let read = ReceivingRead::of_logits(logits, grain);
                            let face = holonics::hnn::ratio::Face::of_read(&read, grain).unwrap();
                            ObservationPath::from_maximum_mass_classes(
                                a,
                                &face.maximal_mass_classes(),
                            )
                            .unwrap()
                        }
                    };
                    tree.receive_observed(
                        &ObservedAddress::new(observation, address),
                        draw.below(a),
                    )
                    .unwrap();
                } else {
                    tree.receive(&address, draw.below(a)).unwrap();
                }
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
fn source(field: &Field, length: usize, seed: u64) -> Encoded {
    let truth = KnownTruth::interrupted(field.alphabet(), seed, 1, length).unwrap();
    Encoded::identity(&truth, field).unwrap().remove(0)
}

/// A drawn word of `length` cells on the field's classes (the uniform terrain), encoded for it
/// (THE_MACHINE guard 9: a test's word enters as every source does).
fn word(field: &Field, length: usize, seed: u64) -> Encoded {
    let truth = KnownTruth::uniform(field.alphabet(), seed, 1, length).unwrap();
    Encoded::identity(&truth, field).unwrap().remove(0)
}

/// Catch observed-fixture admission failures without requiring a CUDA device. The native
/// refine/compare below must still supply its own executed observation to the staged deposit.
#[test]
fn the_generic_fixture_preserves_each_declared_observation_partition() {
    use holonics::hnn::receiving::ObservationPartition;
    for partition in [
        ObservationPartition::MaximumRealGrainSet,
        ObservationPartition::ReceivingSection,
    ] {
        let field = chain().with_receiving_context(2, partition).unwrap();
        let initial = generic(&field, 0xC017_1);
        let tree = initial.landmarks(2).unwrap();
        assert_eq!(tree.observation_role(), partition.role());
        assert_eq!(tree.observation_width(), partition.outcome_bits(&field, 2));
        let host = Reference::campaign_one();
        let mut resident = host
            .mount_with(&field, &Current::at_rest(&field), initial)
            .unwrap();
        let (moment, _) = host
            .ingest(&mut resident, None, &word(&field, 3, 0xC017_2))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let (pending, _) = host.refine(&mut resident, &moment, &phases).unwrap();
        let (_, compared) = host
            .compare(
                &mut resident,
                pending,
                &word(&field, phases.aperture(), 0xC017_4),
            )
            .unwrap();
        let deposit = compared.deposit.present().unwrap();
        assert_eq!(deposit.landmark_partition(), Some(partition));
        assert!(
            deposit
                .observed_landmarks()
                .unwrap()
                .unwrap()
                .iter()
                .all(|address| address.observation().len() == partition.outcome_bits(&field, 2))
        );
    }
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
    /// Deposits both ports refused alike (a pumped resonator's growth is not certified, so the
    /// certified step refuses a linear step through it); their staged handles are discarded.
    refused: u64,
    /// The linear loci the published deposits stepped (their certified steps).
    stepped_loci: u64,
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
    /// The refines that opened on a received carry (the reception carry).
    received: u64,
    /// Received openings whose carried rate the deposit's storage moved off its momentum, so the
    /// open holds it at `w′ = w + δ`, `δ ≠ 0` (the deposit record §3).
    held: u64,
    /// Received openings whose carried wave crossed a moved conductance (record B §2.3a).
    crossed: u64,
    /// Received openings that carried a resonator state (record B §2.4).
    pumped: u64,
    /// Received openings whose carried resonator rate a deposit moved off its momentum.
    resonator_held: u64,
    /// The located receiving prior's reads at the stepped receiving maps, and the reads whose `k`
    /// moved (the receiving prior's carry; the published constitutions are compared after each).
    prior_reads: u64,
    prior_moves: u64,
}

/// A carry as its saved text (`ReceptionCarry::write`): the bytes a continuing state holds.
fn carry_text(carry: Option<&ReceptionCarry>) -> Option<String> {
    carry.map(|carry| {
        let mut text = String::new();
        carry.write(&mut text);
        text
    })
}

/// **Run the exposure protocol on both ports in lockstep** (module header) over at most `windows`
/// receiving epochs of `cut`, from `constitution` (the declared initial one when `None`), with a
/// release at every `release_every`-th epoch, at the production reception
/// (`Reference::campaign_one().reception()`, the carry). Every return is asserted equal. A test
/// about rest names `Reception::Rest` through [`lockstep_receiving`].
fn lockstep(
    field: &Field,
    cut: &Cut,
    windows: u64,
    constitution: Option<Constitution>,
    release_every: u64,
) -> Compared {
    lockstep_receiving(
        field,
        cut,
        windows,
        constitution,
        release_every,
        Reference::campaign_one().reception(),
    )
}

/// **The lockstep under a declared reception** ([`lockstep`]; the reception carry): every return
/// asserted equal, and after every method that writes the carry (compare, deposit, discard) the
/// carried end on both ports byte-identical as saved text.
fn lockstep_receiving(
    field: &Field,
    cut: &Cut,
    windows: u64,
    constitution: Option<Constitution>,
    release_every: u64,
    reception: Reception,
) -> Compared {
    let card = card();
    let host = Reference::campaign_one().with_reception(reception);
    // The lockstep runs the normal-law mirror (the parity test it moved into, off the exposure's
    // path), and reports its tally.
    let device = Resident::campaign_one(&card)
        .with_normal_mirror()
        .with_reception(reception);
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
        host.ingest(&mut h, None, &word(&field, 0, 0)),
        device.ingest(&mut d, None, &word(&field, 0, 0)),
    )
    .expect("the moment opens");
    let rule = releasing();
    let mut aeon_start = 0usize;
    let mut position = 0usize;
    let mut window = 0u64;
    while position < cells.len() && window < windows {
        let end = (position + aperture).min(cells.len());
        let span = &cells.part(position..end).unwrap();
        if span.len() == aperture {
            window += 1;
            if let Some(carry) = h.carried() {
                compared.received += 1;
                // What the opening does to the carry at this cut, read from the host owner.
                let form =
                    holonics::hnn::word::PowerForm::read(field, h.constitution(), h.current())
                        .unwrap();
                let opened = form.opening(field, carry).unwrap();
                compared.held += u64::from(
                    opened
                        .states
                        .iter()
                        .zip(&carry.change.states)
                        .any(|(after, before)| after[1] != before[1]),
                );
                compared.crossed += u64::from(
                    opened
                        .arrivals
                        .iter()
                        .zip(&carry.change.arrivals)
                        .any(|(after, before)| after != before),
                );
                compared.pumped += u64::from(carry.change.resonators.iter().any(Option::is_some));
                compared.resonator_held +=
                    u64::from(opened.resonators.iter().zip(&carry.change.resonators).any(
                        |(after, before)| match (after, before) {
                            (Some(after), Some(before)) => after[1] != before[1],
                            _ => false,
                        },
                    ));
            }
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
                host.compare(&mut h, pending, span),
                device.compare(&mut d, pending, span),
            );
            compared.compares += 1;
            let Some((staged, _)) = compared_return else {
                break;
            };
            assert_eq!(
                carry_text(h.carried()),
                carry_text(ExposedResident::carried(&d)),
                "the carried ends after the compare"
            );
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
                if deposited.is_none() {
                    compared.refused += 1;
                    same(
                        "discard a refused deposit",
                        host.discard(&mut h, Handle::Staged(staged)),
                        device.discard(&mut d, Handle::Staged(staged)),
                    );
                    compared.discards += 1;
                }
                // The cells a deposit added to the tree (the landmark tree), and the published
                // constitutions, the tree among them, equal on both ports.
                if let Some(reading) =
                    deposited.and_then(|returned| returned.deposit.into_present())
                {
                    compared.landmarks += reading.landmarks;
                    compared.stepped_loci += reading.steps.len() as u64;
                    for prior in reading
                        .charts
                        .iter()
                        .filter_map(|(_, chart)| chart.prior.as_ref())
                    {
                        compared.prior_reads += 1;
                        compared.prior_moves += u64::from(prior.to != prior.from);
                    }
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
                host.ingest(&mut h, Some(&hm), &span.part(fed..span.len()).unwrap()),
                device.ingest(&mut d, Some(&hm), &span.part(fed..span.len()).unwrap()),
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
                        host.locate_keys(&mut h, &cells.part(span.clone()).unwrap(), crib.offset),
                        device.locate_keys(&mut d, &cells.part(span).unwrap(), crib.offset),
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
    assert_eq!(
        carry_text(h.carried()),
        carry_text(ExposedResident::carried(&d)),
        "the carried ends at the run's end"
    );
    compared.traffic = d.traffic();
    compared.mirror = device
        .normal_mirror()
        .expect("the lockstep runs the mirror");
    println!(
        "the normal-law mirror: {} carried; {} declined (empty {}, off the dyadics {}, past a word {}, the kernel {}, the read {}); {} skipped (a locus stepped again {}, no normal law {}, a moved prior {})",
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
        compared.mirror.moved,
    );
    compared
}

fn cut_of(cells: Encoded, held_out: Range<usize>) -> Cut {
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
    let cells = source(&field, population, 3);
    let held = population - 8;
    let compared = lockstep(&field, &cut_of(cells, held..population), u64::MAX, None, 3);
    println!("chain, declared constitution: {compared:?}");
    assert!(compared.boundaries > 0 && compared.keys > 0 && compared.deposits > 0);
    // Every deposited window added its two targets to the tree (the landmark tree).
    assert_eq!(compared.landmarks, 2 * compared.deposits);
}

/// **The located receiving prior on the card** (the receiving prior's carry, record §7): the chain
/// with its receiver's prior located from `2^6`, in lockstep at the production reception (the
/// carry, `Reference::campaign_one().reception()`). The card deposits through the host
/// constitution, so the moved Gram, map, chart and pair are the reference's (the published
/// constitutions are compared after every deposit); the normal-law mirror skips a deposit whose
/// prior moved, since its kernel steps a fixed `2^k`, and counts it.
///
/// [historical; restated October 5 with THE_MACHINE guard 9] On the folded chain (four classes on a
/// period-2 source ring through `c mod 2`) this cut held the prior at rest and moved it only under
/// the carry (33 reads at rest, none moved; 33 under the carry, 22 moved). The chain is fold-free
/// now (its source ring of period 4), and the host's conditional law, a map that never leaves zero
/// holds its prior, is read on the two-class chain
/// (`holonics::hnn::tests::prior_carry::at_rest_a_map_that_never_leaves_zero_holds_its_prior`).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_across_a_moved_receiving_prior() {
    let declared = |population: u64| {
        let mut declaration = chain_declaration(population);
        declaration.receivers[0].receiving_prior = 6;
        Field::declare(declaration.by_lattice_rule()).unwrap()
    };
    let field = declared(declared(1 << 20).capacity().n_star() as u64);
    let population = field.population() as usize;
    let cells = source(&field, population, 3);
    let held = population - 8;
    let compared = lockstep_receiving(
        &field,
        &cut_of(cells, held..population),
        u64::MAX,
        None,
        3,
        Reference::campaign_one().reception(),
    );
    println!("chain, located prior, the production reception: {compared:?}");
    assert!(compared.prior_reads > 0 && compared.prior_moves > 0);
    // A moved locus stepped twice in one deposit is counted among the repeated steps instead.
    assert!(compared.mirror.moved > 0 && compared.mirror.moved <= compared.prior_moves);
}

/// **The reception carry's chain** (the host's fixture, `holonics::hnn::tests::learning::chain_of`):
/// the chain with no pair offset (`Δ = ∅`), at its capacity rounded up to a whole receiving window,
/// and its cut: the periodic source with its held-out windows at both ends.
fn carry_chain() -> (Field, Cut) {
    let declared = |population: u64| {
        let mut declaration = chain_declaration(population);
        declaration.offsets = Vec::new();
        Field::declare(declaration.by_lattice_rule()).unwrap()
    };
    let n_star = declared(1 << 20).capacity().n_star() as usize;
    let length = n_star + n_star % 2;
    let field = declared(length as u64);
    let cut = Cut {
        cells: source(&field, length, 81),
        held_out: vec![2..4, length - 4..length],
    };
    (field, cut)
}

/// An exposure with its wall times cleared: the one field two runs of one cut do not share.
fn without_wall(
    mut exposure: holonics::hnn::reference::Exposure,
) -> holonics::hnn::reference::Exposure {
    exposure.wall = Default::default();
    exposure.readout = Default::default();
    exposure
}

/// **The card carries each reception as the reference does** (record B §2.3, §2.3a; the deposit
/// record §3): under `Carry(Nothing)` on the chain every reception after the first opens on the
/// previous one's end change, kept on the card, its waves crossed at the lift's reference change
/// and its rates held at momentum in the card's open (both happen on this cut: a lift moves a
/// conductance and a deposit moves a contact's storage). Every return of the lockstep is the
/// reference's, and the carried end is byte-identical as saved text after every compare; the
/// card's exposure under the carry is the reference's exposure whole (wall times aside), its
/// chained balance closing at every reception with a nonzero opening split (a crossed wave off the
/// dyadics, carried over its denominator). A carry restored on both ports (`mount_carried`, from
/// its saved text) opens the next reception's word alike.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_carries_each_reception_as_the_reference() {
    let (field, cut) = carry_chain();
    let carry = Reception::Carry(Absorption::Nothing);
    let windows = (cut.cells.len() / 2) as u64;
    let compared = lockstep_receiving(&field, &cut, windows, None, 3, carry);
    println!("chain, Carry(Nothing): {compared:?}");
    assert_eq!(compared.compares, windows);
    assert_eq!(
        compared.received,
        windows - 1,
        "every reception after the first opens on a carry"
    );
    assert!(
        compared.crossed > 0,
        "a carried wave crosses a moved conductance"
    );
    assert!(
        compared.held > 0,
        "a deposit moves a carried rate off its momentum"
    );
    // The exposure on both ports.
    let card = card();
    let host = Reference::campaign_one().with_reception(carry);
    let device = Resident::campaign_one(&card).with_reception(carry);
    let reference = without_wall(host.expose(&field, &cut).unwrap());
    let carried = without_wall(device.expose(&field, &cut).unwrap());
    let chained = &reference.word.chained;
    assert_eq!(chained.read, reference.compares - 1);
    assert!(chained.closed && chained.dissipative == chained.read);
    assert!(
        !chained.split.is_zero(),
        "a crossed wave is split off the dyadics"
    );
    assert_eq!(carried, reference, "the card's exposure under the carry");
    // A saved carry restored on both ports opens the next word alike.
    let current = Current::at_rest(&field);
    let mut h = host.mount(&field, &current).unwrap();
    let mut d = device.mount(&field, &current).unwrap();
    let phases = h.admitted()[0].clone();
    let (hm, _) = same(
        "the open",
        host.ingest(&mut h, None, &word(&field, 0, 0)),
        device.ingest(&mut d, None, &word(&field, 0, 0)),
    )
    .unwrap();
    let (pending, _) = same(
        "refine",
        host.refine(&mut h, &hm, &phases),
        device.refine(&mut d, &hm, &phases),
    )
    .unwrap();
    same(
        "compare",
        host.compare(&mut h, pending, &cut.cells.part(0..2).unwrap()),
        device.compare(&mut d, pending, &cut.cells.part(0..2).unwrap()),
    );
    let saved = carry_text(h.carried()).expect("the refine writes the carry");
    assert_eq!(
        Some(&saved),
        carry_text(ExposedResident::carried(&d)).as_ref()
    );
    let mut lines = saved.lines();
    let head = lines.next().unwrap();
    let restored = ReceptionCarry::read(head, &mut |what| {
        lines.next().ok_or(HnnError::ContinuingState { what })
    })
    .unwrap();
    let theta = h.constitution().clone();
    let mut h = host
        .mount_carried(&field, &current, theta.clone(), restored.clone())
        .unwrap();
    let mut d = device
        .mount_carried(&field, &current, theta, restored)
        .unwrap();
    let (hm, _) = same(
        "the open",
        host.ingest(&mut h, None, &word(&field, 0, 0)),
        device.ingest(&mut d, None, &word(&field, 0, 0)),
    )
    .unwrap();
    same(
        "refine on the restored carry",
        host.refine(&mut h, &hm, &phases),
        device.refine(&mut d, &hm, &phases),
    );
}

/// The carry from a generic constitution on half-integers (every locus live: the contrast port,
/// the pair port's outputs, the channels' forms) under `Carry(Nothing)`: every return the
/// reference's and the carried end byte-identical after every compare.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_carries_the_reference_on_a_generic_constitution() {
    let field = chain();
    let population = field.population() as usize;
    for seed in [5u64, 11] {
        let cells = source(&field, population, seed);
        let compared = lockstep_receiving(
            &field,
            &cut_of(cells, population - 6..population),
            12,
            Some(generic(&field, seed)),
            2,
            Reception::Carry(Absorption::Nothing),
        );
        println!("chain, generic constitution {seed}, Carry(Nothing): {compared:?}");
        assert_eq!(compared.received, compared.compares - 1);
        assert!(
            compared.crossed > 0,
            "a carried wave crosses a moved conductance"
        );
    }
}

/// **The carry chain with a pumped resonator on every ring** (the host's
/// `the_chained_balance_closes_on_a_pumped_field`, at the dyadic carrier the card's words carry):
/// the declared initial constitution with a parametron resonator pumped at a half step on each
/// ring.
fn pumped(field: &Field) -> Constitution {
    let mut theta = Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap();
    for ring in 0..field.rings().len() {
        let pump = PumpDeclaration::new(
            rat(1, 16),
            // The card's words carry dyadic material only: the carrier at phase zero, `(1, 0)`.
            Carrier::new(Rat::one(), Rat::zero()).unwrap(),
            PumpStep::Half,
        )
        .unwrap();
        let material =
            ResonatorMaterial::of_parametron(field.ring(ring).parametron(), &rat(1, 8), Some(pump))
                .unwrap();
        theta = theta.with_ring_resonator(field, ring, material).unwrap();
    }
    theta
}

/// **The card carries the pump across receptions as the reference does** (record B §2.4): under
/// `Carry(Nothing)` on the chain with a pumped resonator on every ring, each reception opens on the
/// previous one's last crossing with the resonator states as its last hop left them, the next word's
/// pump phases read the field's elapsed ticks, and each carried resonator rate is held at its
/// momentum across the deposit. Every return of the lockstep is the reference's and the carried end
/// byte-identical after every compare; the card's exposure from the pumped constitution is the
/// reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_carries_the_pump_as_the_reference() {
    let (field, cut) = carry_chain();
    let carry = Reception::Carry(Absorption::Nothing);
    let windows = (cut.cells.len() / 2) as u64;
    let theta = pumped(&field);
    let compared = lockstep_receiving(&field, &cut, windows, Some(theta.clone()), 3, carry);
    println!("pumped chain, Carry(Nothing): {compared:?}");
    assert_eq!(compared.compares, windows);
    assert_eq!(compared.received, windows - 1);
    assert_eq!(
        compared.pumped,
        windows - 1,
        "every carry holds the resonators' states"
    );
    let card = card();
    let host = Reference::campaign_one().with_reception(carry);
    let device = Resident::campaign_one(&card).with_reception(carry);
    let reference = without_wall(host.expose_with(&field, &cut, theta.clone()).unwrap());
    let carried = without_wall(device.expose_with(&field, &cut, theta).unwrap());
    let chained = &reference.word.chained;
    assert_eq!(chained.read, reference.compares - 1);
    assert!(chained.closed && chained.dissipative == chained.read);
    assert_eq!(
        carried, reference,
        "the card's exposure under the pumped carry"
    );
}

/// The same per-node quartic kick/drift and its producing-state Hessian return on both ports.
/// Three receptions retain the real carry, then a changed capacity holds the carried rate off
/// the dyadics and a changed fifth gain publishes beta'=beta*(3/2)^2. Two more receptions compare
/// every return, balance and saved carry exactly. The integration defect must be nonzero.
/// This is transition/publication parity, not a nonlinear stability or pump-lock certificate.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_saturating_ring_matches_the_reference_with_carry() {
    fn reception(both: &mut Pair<'_>, span: &Encoded) -> bool {
        let phases = both.h.admitted()[0].clone();
        same(
            "ingest the source",
            both.host.ingest(&mut both.h, Some(&both.moment), span),
            both.device.ingest(&mut both.d, Some(&both.moment), span),
        )
        .unwrap();
        let (pending, refined) = same(
            "the quartic refine",
            both.host.refine(&mut both.h, &both.moment, &phases),
            both.device.refine(&mut both.d, &both.moment, &phases),
        )
        .unwrap();
        let ReceiptDetail::Refine {
            resonators, word, ..
        } = &refined.receipt.detail
        else {
            panic!("refine returns its balance receipt");
        };
        assert!(resonators.iter().all(|balance| balance.closes()));
        assert!(word.closes());
        let integration_seen = resonators
            .iter()
            .any(|balance| !balance.integration.is_zero());
        let (staged, _) = same(
            "the quartic Hessian return",
            both.host.compare(&mut both.h, pending, span),
            both.device.compare(&mut both.d, pending, span),
        )
        .unwrap();
        let host_carry = carry_text(both.h.carried()).expect("comparison retains the carry");
        assert_eq!(
            Some(host_carry),
            carry_text(ExposedResident::carried(&both.d))
        );
        same(
            "discard the staged variation",
            both.host.discard(&mut both.h, Handle::Staged(staged)),
            both.device.discard(&mut both.d, Handle::Staged(staged)),
        )
        .unwrap();
        integration_seen
    }

    let (field, cut) = carry_chain();
    let mut theta = pumped(&field);
    for ring in 0..field.rings().len() {
        let material = theta
            .ring_resonator(ring)
            .unwrap()
            .clone()
            .with_symmetric_saturation(rat(1, 16))
            .unwrap();
        assert_eq!(material.gain_count(), 5);
        theta = theta.with_ring_resonator(&field, ring, material).unwrap();
    }
    let card = card();
    let mut both = pair(&card, &field, Some(theta));
    assert!(both.h.admitted().iter().all(|phases| {
        phases.rank_scope() == holonics::hnn::receiving::RankScope::TangentAtRest
    }));
    let mut integration_seen = false;
    for window in 0..3 {
        integration_seen |= reception(
            &mut both,
            &cut.cells.part(2 * window..2 * window + 2).unwrap(),
        );
    }

    let saved = carry_text(both.h.carried()).expect("the comparison writes the carry");
    let mut lines = saved.lines();
    let restored = ReceptionCarry::read(lines.next().unwrap(), &mut |what| {
        lines.next().ok_or(HnnError::ContinuingState { what })
    })
    .unwrap();
    let current = both.h.current().clone();
    let mut moved = both.h.constitution().clone();
    for ring in 0..field.rings().len() {
        let material = moved.ring_resonator(ring).unwrap().clone();
        let mut gains = material.gains().clone();
        gains[0] = rat(3, 4);
        gains[4] = rat(3, 2);
        let material = material.with_gains(gains).unwrap();
        assert_eq!(material.saturation().unwrap().coefficient(), &rat(9, 64));
        moved = moved.with_ring_resonator(&field, ring, material).unwrap();
    }
    let form = holonics::hnn::word::PowerForm::read(&field, &moved, &current).unwrap();
    let opened = form.opening(&field, &restored).unwrap();
    let off_dyadic = opened
        .resonators
        .iter()
        .zip(&restored.change.resonators)
        .filter_map(|(after, before)| Some((after.as_ref()?, before.as_ref()?)))
        .flat_map(|(after, before)| after[1].iter().zip(&before[1]))
        .filter(|(after, before)| after != before)
        .filter(|(after, _)| exponent_of(after).is_none())
        .count();
    assert!(
        off_dyadic > 0,
        "the quartic carry is held off the dyadics after C'=9C/16"
    );
    let mut h = both
        .host
        .mount_carried(&field, &current, moved.clone(), restored.clone())
        .unwrap();
    let mut d = both
        .device
        .mount_carried(&field, &current, moved.clone(), restored)
        .unwrap();
    assert_eq!(h.constitution(), &moved);
    assert_eq!(d.constitution(), &moved);
    let (moment, _) = same(
        "the moved publication opens",
        both.host.ingest(&mut h, None, &word(&field, 0, 0)),
        both.device.ingest(&mut d, None, &word(&field, 0, 0)),
    )
    .unwrap();
    let mut both = Pair {
        host: both.host,
        device: both.device,
        h,
        d,
        moment,
    };
    for window in 3..5 {
        integration_seen |= reception(
            &mut both,
            &cut.cells.part(2 * window..2 * window + 2).unwrap(),
        );
    }
    assert!(
        integration_seen,
        "the quartic transition exposes its signed integration defect"
    );
}

/// **The card holds a carried resonator's momentum across a moved capacity as the reference does**
/// (record B §2.4; `ReceptionCarry::crossed`, `held_resonator_rate`): on the pumped chain under
/// `Carry(Nothing)`, three receptions run in lockstep and their carry is saved as text; the
/// constitution is then moved on every ring's capacity gain, `1 → 3/4`, so `C′_r = (9/16) C_r` and
/// the held rate `w′_r = (16/9) w_r` leaves the dyadics, and both ports mount the saved carry beside
/// it (`mount_carried`) and receive three more windows. Every return is the reference's, the
/// carried end byte-identical after every compare, and the first opening's held resonator rate
/// moves off the dyadics (its jump's denominator is odd), so the card's open splits it over that
/// denominator and its velocity carries the remainder. [agent-inferred] The capacity move is
/// declared, not deposited: on these cuts no deposit moves a capacity gain (only the dissipation's
/// moves), and the hold reads only `C_r` and `C′_r`.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_holds_a_resonators_momentum_as_the_reference() {
    let (field, cut) = carry_chain();
    let carry = Reception::Carry(Absorption::Nothing);
    let card = card();
    let host = Reference::campaign_one().with_reception(carry);
    let device = Resident::campaign_one(&card).with_reception(carry);
    let current = Current::at_rest(&field);
    let theta = pumped(&field);
    let mut h = host.mount_with(&field, &current, theta.clone()).unwrap();
    let mut d = device.mount_with(&field, &current, theta).unwrap();
    receive(&host, &device, &mut h, &mut d, &cut.cells, 0, 3);
    let saved = carry_text(h.carried()).expect("the refine writes the carry");
    let mut lines = saved.lines();
    let head = lines.next().unwrap();
    let restored = ReceptionCarry::read(head, &mut |what| {
        lines.next().ok_or(HnnError::ContinuingState { what })
    })
    .unwrap();
    // The capacity gain moved on every ring: `C′_r = (3/4)² C_r`.
    let mut moved = h.constitution().clone();
    for ring in 0..field.rings().len() {
        let material = moved.ring_resonator(ring).unwrap().clone();
        let mut gains = material.gains().clone();
        gains[0] = rat(3, 4);
        moved = moved
            .with_ring_resonator(&field, ring, material.with_gains(gains).unwrap())
            .unwrap();
    }
    // The first opening's held resonator rate leaves the dyadics.
    let form = holonics::hnn::word::PowerForm::read(&field, &moved, &current).unwrap();
    let opened = form.opening(&field, &restored).unwrap();
    let off_dyadic = opened
        .resonators
        .iter()
        .zip(&restored.change.resonators)
        .filter_map(|(after, before)| Some((after.as_ref()?, before.as_ref()?)))
        .flat_map(|(after, before)| after[1].iter().zip(&before[1]))
        .filter(|(after, before)| after != before)
        .filter(|(after, _)| power_of_two(&Rat::from_integer(after.denom().clone())).is_none())
        .count();
    assert!(off_dyadic > 0, "a held resonator rate leaves the dyadics");
    let mut h = host
        .mount_carried(&field, &current, moved.clone(), restored.clone())
        .unwrap();
    let mut d = device
        .mount_carried(&field, &current, moved, restored)
        .unwrap();
    receive(&host, &device, &mut h, &mut d, &cut.cells, 6, 3);
}

/// `windows` receptions on both ports from `from`, every return asserted equal and the carried end
/// byte-identical after every compare.
fn receive<'c>(
    host: &Reference,
    device: &Resident<'c>,
    h: &mut holonics::hnn::reference::Resident,
    d: &mut super::Mounted<'c>,
    cells: &Encoded,
    from: usize,
    windows: usize,
) {
    let phases = h.admitted()[0].clone();
    let (moment, _) = same(
        "the open",
        host.ingest(h, None, &cells.part(0..0).unwrap()),
        device.ingest(d, None, &cells.part(0..0).unwrap()),
    )
    .unwrap();
    for window in 0..windows {
        let span = &cells
            .part(from + 2 * window..from + 2 * window + 2)
            .unwrap();
        let (pending, _) = same(
            "refine",
            host.refine(h, &moment, &phases),
            device.refine(d, &moment, &phases),
        )
        .unwrap();
        let (staged, _) = same(
            "compare",
            host.compare(h, pending, span),
            device.compare(d, pending, span),
        )
        .unwrap();
        assert_eq!(
            carry_text(h.carried()),
            carry_text(ExposedResident::carried(d)),
            "the carried ends after the compare"
        );
        same(
            "deposit",
            host.deposit(h, staged),
            device.deposit(d, staged),
        );
        same(
            "ingest",
            host.ingest(h, Some(&moment), span),
            device.ingest(d, Some(&moment), span),
        );
    }
}

/// **The card holds a contact's rate past a word's width as the reference does** (the deposit
/// record §3; `ReceptionCarry::crossed`, `held_rate`, the card's `HeldRow`): on the carry chain
/// under `Carry(Nothing)`, three receptions run in lockstep and their carry is saved as text; every
/// contact's storage factor is then moved to the banded `c′ = (255 I + B)/128` (`B` the unit band
/// beside the diagonal, on the channel's lattice), so the held rate `C′⁻¹ C w` carries
/// denominators from `det(C′)` and its jump `δ·2^(L_w) = n/d` passes a signed 64-bit word; both
/// ports mount the saved carry beside it (`mount_carried`) and receive three more windows. Every
/// return is the reference's and the carried end byte-identical: the card carries the host's split
/// of the held rate (the coordinate's jump and the remainder's integer part, the fraction read back
/// by the host), so no width of `n` or `d` enters.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_holds_a_rate_past_a_words_width_as_the_reference() {
    let (field, cut) = carry_chain();
    let carry = Reception::Carry(Absorption::Nothing);
    let card = card();
    let host = Reference::campaign_one().with_reception(carry);
    let device = Resident::campaign_one(&card).with_reception(carry);
    let current = Current::at_rest(&field);
    let mut h = host.mount(&field, &current).unwrap();
    let mut d = device.mount(&field, &current).unwrap();
    receive(&host, &device, &mut h, &mut d, &cut.cells, 0, 3);
    let saved = carry_text(h.carried()).expect("the compare writes the carry");
    let mut lines = saved.lines();
    let head = lines.next().unwrap();
    let restored = ReceptionCarry::read(head, &mut |what| {
        lines.next().ok_or(HnnError::ContinuingState { what })
    })
    .unwrap();
    let mut moved = h.constitution().clone();
    for contact in 0..field.contacts().len() {
        let n = field.contact(contact).width();
        let factor = ExactRatMatrix::shaped(
            n,
            n,
            (0..n)
                .map(|i| {
                    (0..n)
                        .map(|j| match i.abs_diff(j) {
                            0 => rat(255, 128),
                            1 => rat(1, 128),
                            _ => Rat::zero(),
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let theta = moved.clone();
        moved = moved
            .with_channel(
                contact,
                factor,
                theta.contact_stiffness(contact).clone(),
                theta.contact_dissipation(contact).clone(),
            )
            .unwrap();
    }
    // The first opening's held rate: its jump at `L_w` passes a signed 64-bit word.
    let lw = field.word_lattice().unwrap().transient_exponent();
    let form = holonics::hnn::word::PowerForm::read(&field, &moved, &current).unwrap();
    let opened = form.opening(&field, &restored).unwrap();
    let widest = opened
        .states
        .iter()
        .zip(&restored.change.states)
        .flat_map(|(after, before)| after[1].iter().zip(&before[1]))
        .map(|(after, before)| (after - before) * Rat::from_integer(BigInt::one() << lw as usize))
        .map(|jump| jump.numer().bits().max(jump.denom().bits()))
        .max()
        .unwrap();
    assert!(widest > 63, "a held rate's jump past a word: {widest} bits");
    let mut h = host
        .mount_carried(&field, &current, moved.clone(), restored.clone())
        .unwrap();
    let mut d = device
        .mount_carried(&field, &current, moved, restored)
        .unwrap();
    receive(&host, &device, &mut h, &mut d, &cut.cells, 6, 3);
}

/// At complete absorption (`Carry(Complete)`) the carry is the rest change at the field's elapsed
/// ticks: on the chain every return is the reference's, the carried end byte-identical after
/// every compare.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_absorbs_each_reception_as_the_reference() {
    let (field, cut) = carry_chain();
    let windows = (cut.cells.len() / 2) as u64;
    let compared = lockstep_receiving(
        &field,
        &cut,
        windows,
        None,
        3,
        Reception::Carry(Absorption::Complete),
    );
    println!("chain, Carry(Complete): {compared:?}");
    assert_eq!(compared.compares, windows);
    assert_eq!(compared.received, windows - 1);
    // With a pumped resonator on every ring the word opens at rest at the carried tick, its pump
    // phases reading the field's elapsed ticks.
    let compared = lockstep_receiving(
        &field,
        &cut,
        windows,
        Some(pumped(&field)),
        3,
        Reception::Carry(Absorption::Complete),
    );
    println!("pumped chain, Carry(Complete): {compared:?}");
    assert_eq!(compared.compares, windows);
    assert_eq!(compared.received, windows - 1);
}

/// The chain from a generic constitution on half-integers (every locus live: the contrast port,
/// the pair port's outputs, the channels' forms): every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_on_a_generic_constitution() {
    let field = chain();
    let population = field.population() as usize;
    for seed in [5u64, 11] {
        let cells = source(&field, population, seed);
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

/// Campaign 1's declared field on a drawn cut of its capacity on its five classes (the uniform
/// terrain; THE_MACHINE guard 9 refuses the byte cut it read through the residue chart): the first
/// eight windows, every return the reference's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_on_campaign_one() {
    let probe = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let n_star = probe.capacity().n_star() as usize;
    let field = Field::declare(FieldDeclaration::campaign_one(n_star as u64)).unwrap();
    let cells = word(&field, n_star, 7);
    let compared = lockstep(
        &field,
        &cut_of(cells, n_star - n_star / 5..n_star),
        8,
        None,
        4,
    );
    println!("campaign 1, drawn classes: {compared:?}");
    assert_eq!(compared.compares, 8);
    assert_eq!(compared.landmarks, 16);
}

/// The reverse chart is chosen from the actual `R^T g` seed but does not change the already-run
/// word. Compare the complete host and card returns on deliberately tiny and mixed row scales;
/// this exercises the fixed-Lw card kernel with a reverse-only normalized source.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_reverse_seed_rechart_matches_host_for_tiny_and_mixed_scales() {
    let field = return_precision_chain();
    let card = card();
    let original = generic(&field, 0x51a7);
    let receiving_rows = original.receiving_map(2).unwrap().to_rows();
    for (scenario, row_exponents) in [
        ("tiny", vec![42; receiving_rows.len()]),
        (
            "mixed",
            (0..receiving_rows.len())
                .map(|row| [18, 27, 35, 43][row % 4])
                .collect(),
        ),
    ] {
        let scaled = receiving_rows
            .iter()
            .zip(row_exponents)
            .map(|(row, exponent)| {
                let factor = rat(1, 1i64 << exponent);
                row.iter().map(|value| value * &factor).collect()
            })
            .collect();
        let receiving =
            ExactRatMatrix::shaped(2 * field.alphabet(), field.ring(2).width(), scaled).unwrap();
        let theta = original
            .clone()
            .with_ports(2, None, None, Some(receiving))
            .unwrap();
        let target = word(&field, 2, if scenario == "tiny" { 37 } else { 41 });
        let mut pair = pair(&card, &field, Some(theta));
        feed(&mut pair, &target);
        let phases = pair.h.admitted()[0].clone();
        let (pending, _) = same(
            "refine before return rechart",
            pair.host.refine(&mut pair.h, &pair.moment, &phases),
            pair.device.refine(&mut pair.d, &pair.moment, &phases),
        )
        .unwrap();
        let (staged, compared) = same(
            "tiny/mixed reverse return",
            pair.host.compare(&mut pair.h, pending, &target),
            pair.device.compare(&mut pair.d, pending, &target),
        )
        .unwrap();
        let ReceiptDetail::Compare {
            return_precision, ..
        } = &compared.receipt.detail
        else {
            panic!("compare receipt has return precision")
        };
        assert!(
            return_precision.levels() > 0,
            "{scenario} R^Tg must select a finer reverse chart: {return_precision:?}"
        );
        assert!(return_precision.seed_groups() > 0);
        println!(
            "reverse parity scenario={scenario} levels={} groups={} smallest_peak={}",
            return_precision.levels(),
            return_precision.seed_groups(),
            return_precision.smallest_nonzero_group_peak()
        );
        same(
            "discard the parity probe's staged deposit",
            pair.host.discard(&mut pair.h, Handle::Staged(staged)),
            pair.device.discard(&mut pair.d, Handle::Staged(staged)),
        );
    }
}

/// The actual card path executes the selected source E/pair-output view, while the shared return
/// applies its exact transpose once. This locks the projected forward publication and back-return
/// to the same host realization on a nontrivial dyadic primitive component.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_mode_view_forward_and_transpose_match_host() {
    use holonics::hnn::ring::modes::ModeView;
    let field = chain();
    let theta = generic(&field, 0x28_041);
    let card = card();
    let mut both = pair(&card, &field, Some(theta));
    let cells = source(&field, 8, 0x28_042);
    feed(&mut both, &cells);
    let phases = both.h.admitted()[0].clone();
    let view = ModeView::from_periods(&field, &[(0, 2)]).unwrap();
    assert!(!view.is_whole());
    let mut impulse = vec![integer(0); field.ring(0).width()];
    impulse[0] = integer(1);
    assert_ne!(view.apply_ring(&field, 0, &impulse).unwrap(), impulse);
    let (pending, refined) = same(
        "view-qualified source opening",
        both.host
            .refine_view(&mut both.h, &both.moment, &phases, &view),
        both.device
            .refine_view(&mut both.d, &both.moment, &phases, &view),
    )
    .expect("host/card projected face and receipt parity");
    match refined.receipt.detail {
        ReceiptDetail::Refine { view: observed, .. } => assert_eq!(observed, view),
        other => panic!("unexpected view receipt: {other:?}"),
    }
    let target = word(&field, 2, 0x28_043);
    let (staged, returned) = same(
        "view-qualified transpose return",
        both.host.compare(&mut both.h, pending, &target),
        both.device.compare(&mut both.d, pending, &target),
    )
    .expect("host/card projected return parity");
    assert!(matches!(
        returned.receipt.detail,
        ReceiptDetail::Compare { .. }
    ));
    same(
        "discard the view probe's staged deposit",
        both.host.discard(&mut both.h, Handle::Staged(staged)),
        both.device.discard(&mut both.d, Handle::Staged(staged)),
    );
}

/// **Campaign 2's physics through the port** (the hardware-surfaces rule): campaign 1's field with a resonator on
/// every ring (`physics_tests::resonant`), on a drawn byte cut: every return the reference's, the
/// refine receipts' resonator balances (the loaded word's ticks decoded by `crate::hnn::readout`)
/// and the published constitutions after every deposit included, and the normal laws' prox steps the
/// card carried in the deposits (`crate::hnn::lattice::normal_deposit_on_card`, the mirror the GPU
/// suite runs, its `X̂f` read through the host's successor chart) read equal to the host's
/// successor, with its declines and skips counted and reported. A declared boost refuses every
/// deposit that moves a family (its signed stiffness stores indefinite energy, `ActiveContact`), so
/// its port path is read by `a_refused_deposit_restores_host_and_card_predecessors` and its word by
/// the loaded source's test; [historical] this test carried a boost until the gains' certificate
/// refused it (September 29).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_port_returns_the_reference_with_resonators() {
    let probe = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let n_star = probe.capacity().n_star() as usize;
    let field = Field::declare(FieldDeclaration::campaign_one(n_star as u64)).unwrap();
    // Unpumped loaded resonators (passive), so the certified step certifies the deposits and the
    // normal-law mirror carries them; the pumped resonators' word is checked by the physics tests,
    // and their deposit's refusal by `the_loaded_source_matches_with_y4_and_hop_two`.
    let theta = super::physics_tests::loaded(&field);

    let cells = word(&field, n_star, 13);
    let compared = lockstep(
        &field,
        &cut_of(cells, n_star - n_star / 5..n_star),
        8,
        Some(theta),
        4,
    );
    println!("campaign 1 with resonators, drawn classes: {compared:?}");
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
    let baseline = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
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
    let cells = word(&field, field.capacity().n_star() as usize, 29);
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    moment.ingest(&field, &mut current, &cells).unwrap();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let read = |constitution: &Constitution| {
        let mut word = Word::open(&field, constitution, &current, &moment).unwrap();
        let anchors = word.forward(&phases).unwrap();
        let faces = anchors
            .iter()
            .map(|anchor| phases.read(&field, constitution, anchor).unwrap())
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
    // Contact 0's declared boost stores indefinite energy in its signed stiffness, so the certified
    // step refuses every deposit whose families move (`ActiveContact`), alike on both ports, before
    // the pumped ring's Floquet reach is read (`hnn::constitution`, "The pumped medium's reach");
    // a deposit whose families move nothing is published and steps no family.
    assert!(compared.refused > 0);
    assert_eq!(compared.stepped_loci, 0);
}

/// A finite, valid staged deposit the constitution refuses leaves the old constitution, staged
/// handle and every card mirror at their predecessor on both ports, and a fresh read at the same
/// moment/targets agrees with the old host tree. Contact 0 declares a certified boost, whose signed
/// stiffness stores indefinite energy, so no step's gain is certified through it and every deposit
/// that moves a family is refused on both ports alike (`ActiveContact`). [historical] The refusal was
/// the committed energy bound's, forced by a 129-bit declared factor step, until the factor
/// families' step was certified (September 29).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_refused_deposit_restores_host_and_card_predecessors() {
    let field = chain();
    let k = field.contact(0).width();
    let theta = Constitution::initial(&field, u64::MAX)
        .unwrap()
        .with_contact_signature(&field, 0, (0..k).map(|j| j != 0).collect())
        .unwrap();
    let host = Reference::new(64, u64::MAX);
    let card = card();
    let device = Resident::new(&card, 64, u64::MAX);
    let current = Current::at_rest(&field);
    let mut h = host.mount_with(&field, &current, theta.clone()).unwrap();
    let mut d = device.mount_with(&field, &current, theta).unwrap();

    let (moment, _) = same(
        "open and ingest a tiny source moment",
        host.ingest(&mut h, None, &word(&field, 1, 101)),
        device.ingest(&mut d, None, &word(&field, 1, 101)),
    )
    .unwrap();
    let phases = h.admitted()[0].clone();
    let (pending, _) = same(
        "refine the first window",
        host.refine(&mut h, &moment, &phases),
        device.refine(&mut d, &moment, &phases),
    )
    .unwrap();
    let (staged, compared) = same(
        "stage a valid comparison",
        host.compare(&mut h, pending, &word(&field, 2, 103)),
        device.compare(&mut d, pending, &word(&field, 2, 103)),
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
    assert!(matches!(
        host_refusal,
        Err(HnnError::ActiveContact { contact: 0 })
    ));
    assert!(matches!(
        device_refusal,
        Err(HnnError::ActiveContact { contact: 0 })
    ));
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
        "compare again after the refusal",
        host.compare(&mut h, host_pending, &word(&field, 2, 105)),
        device.compare(&mut d, device_pending, &word(&field, 2, 105)),
    );
    assert!(retried.is_some());
}

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
    let (moment, _) = host.ingest(&mut h, None, &word(&field, 0, 0)).unwrap();
    device.ingest(&mut d, None, &word(&field, 0, 0)).unwrap();
    same(
        "ingest",
        host.ingest(&mut h, Some(&moment), &word(&field, 4, 107)),
        device.ingest(&mut d, Some(&moment), &word(&field, 4, 107)),
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
        host.compare(&mut h, pending, &word(&field, 1, 109)),
        device.compare(&mut d, pending, &word(&field, 1, 109)),
    );
    same(
        "an unknown handle",
        host.discard(&mut h, Handle::Staged(holonics::hnn::port::StagedId(999))),
        device.discard(&mut d, Handle::Staged(holonics::hnn::port::StagedId(999))),
    );
    // The refused compare left the pending ratio open on both: it compares now.
    let compared = same(
        "compare",
        host.compare(&mut h, pending, &word(&field, 2, 111)),
        device.compare(&mut d, pending, &word(&field, 2, 111)),
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
        host.ingest(&mut h, None, &word(&field, 0, 0)),
        device.ingest(&mut d, None, &word(&field, 0, 0)),
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
fn feed(pair: &mut Pair<'_>, cells: &Encoded) {
    let family = pair.h.admitted().to_vec();
    let mut fed = 0;
    while fed < cells.len() {
        let (_, ingested) = same(
            "ingest",
            pair.host.ingest(
                &mut pair.h,
                Some(&pair.moment),
                &cells.part(fed..cells.len()).unwrap(),
            ),
            pair.device.ingest(
                &mut pair.d,
                Some(&pair.moment),
                &cells.part(fed..cells.len()).unwrap(),
            ),
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
    let cells = source(&field, 40, 17);
    let mut pending = Vec::new();
    for k in 0..5 {
        let chunk = cells.part(4 * k..4 * k + 4).unwrap();
        let (id, _) = same(
            "refine",
            both.host.refine(&mut both.h, &both.moment, &phases),
            both.device.refine(&mut both.d, &both.moment, &phases),
        )
        .unwrap();
        pending.push((id, chunk.part(0..2).unwrap()));
        feed(&mut both, &chunk);
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
            both.host.compare(&mut both.h, *id, targets),
            both.device.compare(&mut both.d, *id, targets),
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
    let cells = source(&field, 64, 23);
    let mut position = 0;
    // Refine, compare and deposit until the joint clock carries out.
    loop {
        let (id, _) = same(
            "refine",
            both.host.refine(&mut both.h, &both.moment, &phases),
            both.device.refine(&mut both.d, &both.moment, &phases),
        )
        .unwrap();
        let targets = cells.part(position..position + 2).unwrap();
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
        both.host.compare(&mut both.h, other, &word(&field, 2, 113)),
        both.device
            .compare(&mut both.d, other, &word(&field, 2, 113)),
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
        both.host.compare(&mut both.h, id, &word(&field, 2, 115)),
        both.device.compare(&mut both.d, id, &word(&field, 2, 115)),
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
        both.host.compare(&mut both.h, fresh, &word(&field, 2, 117)),
        both.device
            .compare(&mut both.d, fresh, &word(&field, 2, 117)),
    );
    same("read", both.host.read(&both.h), both.device.read(&both.d));
}

// -------------------------------------------------------------------------------------------
// a failed ingest

/// The helix `(2, 3, 5)` as a field (the host's `hnn::tests::moment` fixture): the rings in carry
/// order on the quarter turns, chained on their common nodes, source ring 2 holding the five
/// classes, `Δ = {1, 3}`, receiver ring 2 with aperture 5.
fn helix_field() -> Field {
    helix_field_at(1 << 16)
}

fn helix_field_at(population: u64) -> Field {
    let mut declaration = chain_declaration(population);
    declaration.rings = [2u64, 3, 5].into_iter().map(|d| ring(d, vec![0])).collect();
    declaration.contacts = vec![contact(0, 1, 2, 0), contact(1, 2, 3, 0)];
    declaration.sources = vec![2];
    declaration.offsets = vec![1, 3];
    declaration.alphabet = 5;
    declaration.receivers[0].aperture = 5;
    Field::declare(declaration.by_lattice_rule()).unwrap()
}

/// The population 436 admits the identity carrier, but lies below the located carrier's 438.
/// Both ports refuse before opening a handle or touching an existing moment; the card's traffic
/// remains unchanged, and the same existing handle still accepts an identity passage.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_located_capacity_refusal_leaves_both_ports_unchanged() {
    let field = helix_field_at(436);
    assert_eq!(field.capacity().n_star(), 436);
    let (located, _) = partial_span(&field);
    let card = card();
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(&card);
    let opening = Current::at_rest(&field);
    let mut h = host.mount(&field, &opening).unwrap();
    let mut d = device.mount(&field, &opening).unwrap();
    let before = same("read before refusal", host.read(&h), device.read(&d)).unwrap();
    let address = h.address().clone();
    let traffic = d.traffic();
    let below = HnnError::BelowCapacity {
        population: 436,
        n_star: 438,
    };
    assert_eq!(
        host.ingest(&mut h, None, &located).err().as_ref(),
        Some(&below)
    );
    assert_eq!(
        device.ingest(&mut d, None, &located).err().as_ref(),
        Some(&below)
    );
    assert_eq!(
        same("read after refusal", host.read(&h), device.read(&d)).unwrap(),
        before
    );
    assert_eq!(h.address(), &address);
    assert_eq!(d.address(), &address);
    assert_eq!(d.traffic(), traffic);

    let empty = located.part(0..0).unwrap();
    let (moment, _) = same(
        "the existing open",
        host.ingest(&mut h, None, &empty),
        device.ingest(&mut d, None, &empty),
    )
    .unwrap();
    let before = same("read the existing open", host.read(&h), device.read(&d)).unwrap();
    assert_eq!(
        host.ingest(&mut h, Some(&moment), &located).err().as_ref(),
        Some(&below)
    );
    assert_eq!(
        device
            .ingest(&mut d, Some(&moment), &located)
            .err()
            .as_ref(),
        Some(&below)
    );
    assert_eq!(
        same("read the refused open", host.read(&h), device.read(&d)).unwrap(),
        before
    );
    assert_eq!(ExposedResident::moment(&h, &moment).unwrap().cells(), 0);
    assert_eq!(ExposedResident::moment(&d, &moment).unwrap().cells(), 0);
    assert_eq!(h.address(), &address);
    assert_eq!(d.address(), &address);
    assert_eq!(d.traffic(), traffic);
    let identity = word(&field, 1, 2);
    let (_, entered) = same(
        "identity after the capacity refusal",
        host.ingest(&mut h, Some(&moment), &identity),
        device.ingest(&mut d, Some(&moment), &identity),
    )
    .unwrap();
    assert_eq!(entered.forward.present().unwrap().cells, 1);
    assert_eq!(ExposedResident::moment(&h, &moment).unwrap().cells(), 1);
    assert_eq!(ExposedResident::moment(&d, &moment).unwrap().cells(), 1);
}

/// Two source moments share the current's clock while retaining their own injected cells. A
/// sibling's advance must leave the other moment's capacity readable and its counts untouched;
/// alternating the producing moment then exercises the card's next ingest at that joined clock.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn sibling_moments_keep_their_counts_and_capacity_on_the_shared_clock() {
    use holonics::hnn::moment::SourceCapacity;
    let field = chain();
    let turn = BigInt::one() << 80usize;
    let opening = Current::at(
        &field,
        field
            .rings()
            .iter()
            .map(|ring| &turn * ring.period())
            .collect(),
    )
    .unwrap();
    let card = card();
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(&card);
    let mut h = host.mount(&field, &opening).unwrap();
    let mut d = device.mount(&field, &opening).unwrap();
    let passage = word(&field, 32, 21);
    let empty = passage.part(0..0).unwrap();
    let first = same(
        "the first open",
        host.ingest(&mut h, None, &empty),
        device.ingest(&mut d, None, &empty),
    )
    .unwrap()
    .0;
    let second = same(
        "the sibling open",
        host.ingest(&mut h, None, &empty),
        device.ingest(&mut d, None, &empty),
    )
    .unwrap()
    .0;
    let at = passage.classes_read().position(|class| class == 0).unwrap();
    let ticking = passage.part(at..at + 1).unwrap();
    let counts = |moment: &SourceMoment| {
        field
            .sources()
            .iter()
            .map(|&ring| {
                (0..field.ring(ring).period() as usize)
                    .map(|phase| {
                        (
                            moment.phase_counts(ring, phase).unwrap().to_vec(),
                            field
                                .offsets()
                                .iter()
                                .map(|&offset| {
                                    moment.offset_counts(ring, offset, phase).unwrap().to_vec()
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };
    for (active, sibling) in [
        (first, second),
        (second, first),
        (first, second),
        (second, first),
    ] {
        let before = ExposedResident::moment(&h, &sibling).unwrap();
        let kept = (before.cells(), before.window(), counts(before));
        let (_, ingested) = same(
            "ingest beside an open sibling",
            host.ingest(&mut h, Some(&active), &ticking),
            device.ingest(&mut d, Some(&active), &ticking),
        )
        .unwrap();
        assert_eq!(ingested.forward.present().unwrap().cells, 1);
        let after = ExposedResident::moment(&h, &sibling).unwrap();
        assert_eq!((after.cells(), after.window(), counts(after)), kept);
        for id in [first, second] {
            let hm = ExposedResident::moment(&h, &id).unwrap();
            let dm = ExposedResident::moment(&d, &id).unwrap();
            assert_eq!(
                SourceCapacity::checked_of(hm, &field, ExposedResident::current(&h)).unwrap(),
                SourceCapacity::checked_of(dm, &field, ExposedResident::current(&d)).unwrap(),
            );
            let (mut hs, mut ds) = (String::new(), String::new());
            hm.write(&mut hs);
            dm.write(&mut ds);
            assert_eq!(hs, ds, "the host and card source-clock bindings must agree");
        }
        same("read the sibling clocks", host.read(&h), device.read(&d)).unwrap();
        if ingested.forward.present().unwrap().carry_out {
            let family = h.admitted().to_vec();
            same(
                "close the shared aeon",
                host.close_aeon(&mut h, &family),
                device.close_aeon(&mut d, &family),
            )
            .unwrap();
        }
    }
    assert_ne!(
        ExposedResident::current(&h),
        &opening,
        "the fixture must advance the clock"
    );
    assert_eq!(ExposedResident::moment(&h, &first).unwrap().cells(), 2);
    assert_eq!(ExposedResident::moment(&h, &second).unwrap().cells(), 2);
}

/// Closing and locating keys reframes the open source without adding cells. Its shared-clock
/// capacity stays readable, the injection counts stay fixed, and the next ingest uses that frame.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn key_relocation_keeps_the_open_capacity_readable() {
    use holonics::hnn::moment::SourceCapacity;
    let field = chain();
    let card = card();
    let mut both = pair(&card, &field, None);
    let cells = source(&field, field.population() as usize, 3);
    let (_, entered) = same(
        "ingest to the boundary",
        both.host.ingest(&mut both.h, Some(&both.moment), &cells),
        both.device.ingest(&mut both.d, Some(&both.moment), &cells),
    )
    .unwrap();
    let entered = entered.forward.present().unwrap();
    assert!(entered.carry_out);
    let count = ExposedResident::moment(&both.h, &both.moment)
        .unwrap()
        .cells();
    let family = both.h.admitted().to_vec();
    same(
        "close before location",
        both.host.close_aeon(&mut both.h, &family),
        both.device.close_aeon(&mut both.d, &family),
    )
    .unwrap();
    let crib = cells
        .part(entered.cells.saturating_sub(8)..entered.cells)
        .unwrap();
    same(
        "locate the closing keys",
        both.host.locate_keys(&mut both.h, &crib, 1),
        both.device.locate_keys(&mut both.d, &crib, 1),
    )
    .unwrap();
    let hm = ExposedResident::moment(&both.h, &both.moment).unwrap();
    let dm = ExposedResident::moment(&both.d, &both.moment).unwrap();
    assert_eq!(hm.cells(), count);
    assert_eq!(dm.cells(), count);
    let capacity =
        SourceCapacity::checked_of(hm, &field, ExposedResident::current(&both.h)).unwrap();
    assert!(matches!(capacity, SourceCapacity::Reframed { .. }));
    assert_eq!(
        SourceCapacity::checked_of(dm, &field, ExposedResident::current(&both.d)).unwrap(),
        capacity,
    );
    let (mut hs, mut ds) = (String::new(), String::new());
    hm.write(&mut hs);
    dm.write(&mut ds);
    assert_eq!(hs, ds);
    let tail = cells.part(entered.cells..entered.cells + 1).unwrap();
    let (_, continued) = same(
        "ingest after location",
        both.host.ingest(&mut both.h, Some(&both.moment), &tail),
        both.device.ingest(&mut both.d, Some(&both.moment), &tail),
    )
    .unwrap();
    assert_eq!(continued.forward.present().unwrap().cells, 1);
    assert_eq!(
        ExposedResident::moment(&both.h, &both.moment)
            .unwrap()
            .cells(),
        count + 1
    );
    assert_eq!(
        ExposedResident::moment(&both.d, &both.moment)
            .unwrap()
            .cells(),
        count + 1
    );
}

/// [agent-inferred, October 5] **A founded partial-span passage** (the host's
/// `hnn::tests::moment::partial_span`, the same draw `2_026_100_995`): advances that are nonzero
/// multiples of 5 on the helix `(2, 3, 5)`, located from a passage at every key to one gauge class;
/// the chart founded on the first passage's key reaches that key's coset only. Returns the encoded
/// passage and its opening key.
fn partial_span(field: &Field) -> (Encoded, u64) {
    use holonics::compression::keys::transport::{CarryHelix, SteppedTerrain, TransportLocation};
    use holonics::hnn::encoding::{Encoding, PassageChart};
    let helix = CarryHelix::new(vec![2, 3, 5]).unwrap();
    let mut draw = holonics::holarchy::terrain::Draw::new(2_026_100_995);
    let advances: Vec<u64> = (0..5).map(|_| 5 * (1 + draw.below(5)) as u64).collect();
    let mut left: Vec<usize> = (0..5).collect();
    let labels: Vec<usize> = (0..5)
        .map(|_| left.remove(draw.below(left.len())))
        .collect();
    let terrain = SteppedTerrain::new(helix.clone(), advances, labels).unwrap();
    let passages: Vec<Vec<usize>> = (0..helix.period())
        .map(|key| terrain.passage(key, 60))
        .collect();
    let location = TransportLocation::locate(helix, 5, &passages).unwrap();
    let chart = PassageChart::located(&location, &passages[..1]).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    assert_eq!(
        encoding.reached(),
        6,
        "the chart reaches one coset of 5ℤ/30"
    );
    let key = chart.openings()[0]
        .iter()
        .position(|entry| !entry.is_zero())
        .expect("an opening is a lift") as u64;
    let encoded = Encoded::through(&encoding, &chart, field, &passages[..1])
        .unwrap()
        .remove(0);
    (encoded, key)
}

/// [implemented-exact] **A failed ingest leaves no further reads** (`port::ingest_open`, Codex's
/// invalidation law `ResidentMoment::is_valid`): on both ports, a moment opened off the passage's
/// reached coset refuses the passage's first located step alike (`EncodingError::Unreached`), and
/// the failed open is discarded, never consumed: the read lists no moment, and a later ingest or
/// refine of its handle is refused (`HnnError::UnknownHandle`). The lift point is the mount's, and a
/// fresh open on the reached coset ingests the passage on both ports alike.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_failed_ingest_leaves_no_further_reads() {
    let field = helix_field();
    let (encoded, key) = partial_span(&field);
    let card = card();
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(&card);
    let lift = |ell: u64| {
        let ell = ell % 30;
        Current::at(
            &field,
            vec![
                BigInt::from(ell % 2),
                BigInt::from(ell / 2 % 3),
                BigInt::from(ell / 6),
            ],
        )
        .unwrap()
    };
    let off = lift(key + 1);
    let mut h = host.mount(&field, &off).unwrap();
    let mut d = device.mount(&field, &off).unwrap();
    let phases = h.admitted()[0].clone();
    let empty = encoded.part(0..0).unwrap();
    let (moment, _) = same(
        "the open",
        host.ingest(&mut h, None, &empty),
        device.ingest(&mut d, None, &empty),
    )
    .unwrap();
    let refused = (
        host.ingest(&mut h, Some(&moment), &encoded),
        device.ingest(&mut d, Some(&moment), &encoded),
    );
    let unreached = HnnError::from(holonics::hnn::encoding::EncodingError::Unreached);
    assert_eq!(refused.0.as_ref().err(), Some(&unreached));
    assert_eq!(refused.1.as_ref().err(), Some(&unreached));
    assert!(ExposedResident::moment(&h, &moment).is_none());
    assert!(ExposedResident::moment(&d, &moment).is_none());
    assert_eq!(ExposedResident::current(&h), &off);
    assert_eq!(ExposedResident::current(&d), &off);
    let (_, _, handles) = same("read", host.read(&h), device.read(&d)).unwrap();
    assert!(
        handles
            .iter()
            .all(|(handle, _)| !matches!(handle, Handle::Moment(_)))
    );
    let unknown = || HnnError::UnknownHandle {
        handle: Handle::Moment(moment),
    };
    assert_eq!(
        host.ingest(&mut h, Some(&moment), &empty).err(),
        Some(unknown())
    );
    assert_eq!(
        device.ingest(&mut d, Some(&moment), &empty).err(),
        Some(unknown())
    );
    assert_eq!(host.refine(&mut h, &moment, &phases).err(), Some(unknown()));
    assert_eq!(
        device.refine(&mut d, &moment, &phases).err(),
        Some(unknown())
    );
    // On the reached coset a fresh open ingests the passage through the card's located route alike.
    let on = lift(key);
    let mut h = host.mount(&field, &on).unwrap();
    let mut d = device.mount(&field, &on).unwrap();
    let (_, ingested) = same(
        "the located ingest",
        host.ingest(&mut h, None, &encoded),
        device.ingest(&mut d, None, &encoded),
    )
    .unwrap();
    assert!(ingested.forward.present().unwrap().cells > 0);
    assert_eq!(ExposedResident::current(&h), ExposedResident::current(&d));
}

/// Full native passage restoration keeps the actual one-open moment, its window and counts,
/// saved declaring reader, address, warm charts, carry and arrived selected-view operands.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_full_resident_continuation_preserves_next_native_operations() {
    full_resident_continuation_case(chain());
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_observation_context_preserves_compare_deposit_and_continuation() {
    use holonics::hnn::receiving::ObservationPartition;
    full_resident_continuation_case(
        chain()
            .with_receiving_context(2, ObservationPartition::MaximumRealGrainSet)
            .unwrap(),
    );
}

/// The refining section uses the executed receiving anchors and typed Section letters all the
/// way through the card tree's deposit, then keeps that law across cold continuation.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_receiving_section_preserves_compare_deposit_and_continuation() {
    use holonics::hnn::receiving::ObservationPartition;
    full_resident_continuation_case(
        chain()
            .with_receiving_context(2, ObservationPartition::ReceivingSection)
            .unwrap(),
    );
}

/// The paired receiving operator is physically 2A×2w. Its candidate is replayed on the same
/// CUDA word and must receive the same strict same-window acceptance decision as the host.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_paired_finite_candidate_replay_matches_reference() {
    let field = paired_candidate_field();
    let mut initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    initial
        .bind_arrival_context_receiving(field.receivers()[0].ring)
        .unwrap();
    let current = Current::at_rest(&field);
    let card = card();
    let reception = Reception::Carry(Absorption::Nothing);
    let host = Reference::campaign_one().with_reception(reception);
    let device = Resident::campaign_one(&card).with_reception(reception);
    let mut h = host.mount_with(&field, &current, initial.clone()).unwrap();
    let mut d = device.mount_with(&field, &current, initial).unwrap();

    let source_truth = KnownTruth::uniform(field.alphabet(), 71, 1, 2).unwrap();
    let source = Encoded::identity(&source_truth, &field).unwrap().remove(0);
    let (moment, _) = same(
        "paired comparison source",
        host.ingest(&mut h, None, &source),
        device.ingest(&mut d, None, &source),
    )
    .unwrap();
    let phases = h.admitted()[0].clone();
    let target_truth = (0..128)
        .find_map(|seed| {
            let truth = KnownTruth::uniform(field.alphabet(), seed, 1, 1).ok()?;
            (truth.passages()[0] == [0]).then_some(truth)
        })
        .expect("a deterministic one-cell uniform truth with class zero");
    let target = Encoded::identity(&target_truth, &field).unwrap().remove(0);
    let (pending, _) = same(
        "paired finite-candidate refine",
        host.refine(&mut h, &moment, &phases),
        device.refine(&mut d, &moment, &phases),
    )
    .unwrap();
    let (staged, compared) = same(
        "paired finite-candidate compare",
        host.compare(&mut h, pending, &target),
        device.compare(&mut d, pending, &target),
    )
    .unwrap();
    let ReceiptDetail::Compare {
        response_defect: Some(defect),
        ..
    } = &compared.receipt.detail
    else {
        panic!("paired return reports the executed actual and fresh response defects");
    };
    assert_eq!(defect.context_bounds().unwrap().len(), phases.aperture());
    let predecessor = ExposedResident::constitution(&d).clone();
    let carry = ExposedResident::carried(&d).cloned();
    let deposited = same(
        "paired finite-candidate deposit",
        host.deposit(&mut h, staged),
        device.deposit(&mut d, staged),
    )
    .unwrap();
    let ReceiptDetail::Deposit {
        finite_comparison: Some(finite),
        ..
    } = deposited.receipt.detail
    else {
        panic!("the accepted paired candidate reports its finite comparison");
    };
    assert!(
        finite.comparison.strictly_improved
            || finite.comparison.unchanged
            || finite.comparison.objective_equal()
    );
    if finite.comparison.strictly_improved {
        assert!(finite.comparison.objective_change.upper < integer(0));
    }
    if finite.comparison.objective_equal() {
        assert_eq!(finite.comparison.objective_change.lower, integer(0));
        assert_eq!(finite.comparison.objective_change.upper, integer(0));
    }
    if finite.comparison.unchanged {
        assert!(finite.comparison.objective_equal());
    }
    assert!(finite.attempts > 0);
    assert_eq!(finite.trials.len(), finite.attempts as usize);
    assert!(finite.trials.iter().all(|trial| {
        (trial.comparison.strictly_improved && trial.comparison.objective_change.upper < integer(0))
            || trial.comparison.unchanged
            || trial.comparison.objective_equal()
            || trial.comparison.needs_precision()
            || trial.comparison.objective_change.lower > integer(0)
    }));
    assert!(ExposedResident::constitution(&d).commit() > predecessor.commit());
    assert_eq!(ExposedResident::carried(&d), carry.as_ref());
    assert_eq!(
        h.continuing_state(0).unwrap().to_text(),
        d.continuing_state(0).unwrap().to_text()
    );
}

fn full_resident_continuation_case(field: Field) {
    use holonics::hnn::constitution::ContinuingState;
    use holonics::hnn::reference::passage::ResidentPassage;
    use holonics::hnn::ring::modes::ModeView;
    let initial = generic(&field, 0xC017_1);
    let current = Current::at_rest(&field);
    let card = card();
    let reception = Reception::Carry(Absorption::Nothing);
    let host = Reference::campaign_one().with_reception(reception);
    let device = Resident::campaign_one(&card).with_reception(reception);
    let mut h = host.mount_with(&field, &current, initial.clone()).unwrap();
    let mut d = device
        .mount_with(&field, &current, initial.clone())
        .unwrap();
    assert_eq!(
        h.continuing_state(0).unwrap().to_text(),
        d.continuing_state(0).unwrap().to_text()
    );
    let (moment, _) = same(
        "full continuation partial source",
        host.ingest(&mut h, None, &word(&field, 3, 0xC017_2)),
        device.ingest(&mut d, None, &word(&field, 3, 0xC017_2)),
    )
    .unwrap();
    let (extra, _) = same(
        "second open before continuation refusal",
        host.ingest(&mut h, None, &word(&field, 0, 0)),
        device.ingest(&mut d, None, &word(&field, 0, 0)),
    )
    .unwrap();
    assert!(h.continuing_state(0).is_err());
    assert!(d.continuing_state(0).is_err());
    same(
        "discard second open",
        host.discard(&mut h, Handle::Moment(extra)),
        device.discard(&mut d, Handle::Moment(extra)),
    )
    .unwrap();
    let saved = d.continuing_state(0).unwrap();
    let text = saved.to_text();
    assert_eq!(text, h.continuing_state(0).unwrap().to_text());
    let saved = ContinuingState::from_text(&text, initial.budget()).unwrap();
    let mut restored = device
        .mount_continued(&field, &current, initial.clone(), &saved)
        .unwrap();
    assert_eq!(restored.continuing_state(0).unwrap().to_text(), text);
    let next = word(&field, 2, 0xC017_3);
    let expected = same(
        "continued source ingest",
        host.ingest(&mut h, Some(&moment), &next),
        device.ingest(&mut d, Some(&moment), &next),
    )
    .unwrap();
    assert_eq!(
        device.ingest(&mut restored, Some(&moment), &next).unwrap(),
        expected
    );
    assert_eq!(
        d.continuing_state(0).unwrap().to_text(),
        restored.continuing_state(0).unwrap().to_text()
    );
    let phases = h.admitted()[0].clone();
    let view = ModeView::primitive(&field, 0, 2).unwrap();
    let (pending, _) = same(
        "continued selected view",
        host.refine_view(&mut h, &moment, &phases, &view),
        device.refine_view(&mut d, &moment, &phases, &view),
    )
    .unwrap();
    assert!(h.continuing_state(0).is_err());
    assert!(d.continuing_state(0).is_err());
    let targets = word(&field, phases.aperture(), 0xC017_4);
    let (staged, compared) = same(
        "continued selected return",
        host.compare(&mut h, pending, &targets),
        device.compare(&mut d, pending, &targets),
    )
    .unwrap();
    if matches!(
        ExposedResident::constitution(&d).receiving_layout(phases.ring()),
        Some(holonics::hnn::constitution::ReceivingLayout::ArrivalContext { .. })
    ) {
        let ReceiptDetail::Compare {
            response_defect: Some(defect),
            ..
        } = &compared.receipt.detail
        else {
            panic!("paired comparison receipt includes both executed response defects");
        };
        assert_eq!(defect.fresh.len(), phases.aperture());
        assert_eq!(
            defect.actual.as_ref().map(Vec::len),
            Some(phases.aperture())
        );
        // A paired receipt must expose certified context bounds, never silently omit the
        // actual lane or treat a missing lane as a zero error.
        assert_eq!(defect.context_bounds().unwrap().len(), phases.aperture());
    }
    assert!(h.continuing_state(0).is_err());
    assert!(d.continuing_state(0).is_err());
    let deposited = same(
        "continued selected deposit",
        host.deposit(&mut h, staged),
        device.deposit(&mut d, staged),
    )
    .unwrap();
    if matches!(
        ExposedResident::constitution(&d).receiving_layout(phases.ring()),
        Some(holonics::hnn::constitution::ReceivingLayout::ArrivalContext { .. })
    ) {
        let ReceiptDetail::Deposit {
            finite_comparison: Some(finite),
            ..
        } = &deposited.receipt.detail
        else {
            panic!("an accepted paired update reports its finite same-window comparison");
        };
        assert!(finite.comparison.strictly_improved || finite.comparison.objective_equal());
        if finite.comparison.strictly_improved {
            assert!(finite.comparison.objective_change.upper < integer(0));
        } else {
            assert_eq!(finite.comparison.objective_change.lower, integer(0));
            assert_eq!(finite.comparison.objective_change.upper, integer(0));
        }
        assert!(finite.attempts > 0);
    }
    let saved = d.continuing_state(0).unwrap();
    assert_eq!(saved.to_text(), h.continuing_state(0).unwrap().to_text());
    let passage =
        ResidentPassage::from_text(&field, d.constitution(), saved.passage().unwrap()).unwrap();
    assert!(!passage.parts().charts.is_empty());
    assert_eq!(
        passage.parts().arrived.as_ref().unwrap().ratio.view(),
        &view
    );
    assert!(saved.carry().is_some());
    assert!(
        Resident::campaign_one(&card)
            .with_reception(Reception::Rest)
            .mount_continued(&field, &current, initial.clone(), &saved)
            .is_err()
    );
    let mut restored = device
        .mount_continued(&field, &current, initial.clone(), &saved)
        .unwrap();
    let mut restored_host = host
        .mount_continued(&field, &current, initial, &saved)
        .unwrap();
    assert_eq!(
        restored.continuing_state(0).unwrap().to_text(),
        saved.to_text()
    );
    assert_eq!(
        restored_host.continuing_state(0).unwrap().to_text(),
        saved.to_text()
    );
    assert_eq!(restored.address(), d.address());
    assert_eq!(restored.current(), d.current());
    let next = word(&field, 2, 0xC017_5);
    let expected = same(
        "warm continued ingest",
        host.ingest(&mut h, Some(&moment), &next),
        device.ingest(&mut d, Some(&moment), &next),
    )
    .unwrap();
    assert_eq!(
        device.ingest(&mut restored, Some(&moment), &next).unwrap(),
        expected
    );
    assert_eq!(
        host.ingest(&mut restored_host, Some(&moment), &next)
            .unwrap(),
        expected
    );
    let expected = same(
        "warm continued read",
        host.refine(&mut h, &moment, &phases),
        device.refine(&mut d, &moment, &phases),
    )
    .unwrap();
    assert_eq!(
        device.refine(&mut restored, &moment, &phases).unwrap(),
        expected
    );
    assert_eq!(
        host.refine(&mut restored_host, &moment, &phases).unwrap(),
        expected
    );
    let pending = expected.0;
    let expected = same(
        "warm continued return",
        host.compare(&mut h, pending, &targets),
        device.compare(&mut d, pending, &targets),
    )
    .unwrap();
    assert_eq!(
        device.compare(&mut restored, pending, &targets).unwrap(),
        expected
    );
    assert_eq!(
        host.compare(&mut restored_host, pending, &targets).unwrap(),
        expected
    );
    let staged = expected.0;
    let expected = same(
        "warm continued publication",
        host.deposit(&mut h, staged),
        device.deposit(&mut d, staged),
    )
    .unwrap();
    assert_eq!(device.deposit(&mut restored, staged).unwrap(), expected);
    assert_eq!(host.deposit(&mut restored_host, staged).unwrap(), expected);
    assert_eq!(
        d.continuing_state(0).unwrap().to_text(),
        restored.continuing_state(0).unwrap().to_text()
    );
}

/// Every erased receiver component survives the same admitted precision publication, including
/// turns, while a previously published component cannot discharge another row's demand.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_receiving_component_precision_preserves_outputs_and_cold_continuation() {
    use holonics::hnn::Locus;
    use holonics::hnn::constitution::{ContinuingState, Lattice};
    let field = chain();
    let ring = field.receivers()[0].ring;
    let width = field.ring(ring).width();
    let mut rows = vec![vec![Rat::zero(); width]; 2 * field.alphabet()];
    rows[0][0] = Rat::one();
    let opening = generic(&field, 0xC0_18)
        .with_ports(
            ring,
            None,
            None,
            Some(ExactRatMatrix::shaped(rows.len(), width, rows).unwrap()),
        )
        .unwrap();
    let exponent = opening
        .lattice(Locus::ReceivingMap(ring))
        .unwrap()
        .exponent();
    let unit = Lattice::new(exponent).unit();
    // Exact persisted-state control fixture: valid sub-lattice remainders, no fabricated
    // target/gradient or direct device-buffer mutation. The native restore validates it.
    let text = opening
        .continuing_state(field.sources()[0])
        .unwrap()
        .to_text();
    let header = format!("receiving {} {}\n", 2 * field.alphabet(), width);
    let start = text.find(&header).unwrap();
    let carry = start + text[start..].find("map-carry 0\n").unwrap();
    let mut seeded = text.clone();
    seeded.replace_range(
        carry..carry + "map-carry 0\n".len(),
        &format!(
            "map-carry 2\n{} {}\n{} {}\n",
            2 * width,
            &unit / integer(8),
            3 * width,
            -&unit / integer(32)
        ),
    );
    assert!(
        ContinuingState::from_text(&seeded, opening.budget()).is_err(),
        "editing a checksummed state must be refused"
    );
    // These same remainders are refused at clock zero by the native fine-lattice law.
    let clock_zero = ContinuingState::stamped(&seeded, &opening).unwrap();
    let clock_zero = ContinuingState::from_text(&clock_zero, opening.budget()).unwrap();
    assert!(matches!(
        opening.clone().continued(&clock_zero),
        Err(HnnError::ContinuingState {
            what: "a remainder off its locus's fine lattice or outside its half cell"
        })
    ));
    // The deeper remainder is unit/32, depth d = 5. Its smallest carrying clock is
    // 1 << ((d - 1) / 2): gamma_length(4) = 5. Four sub-lattice deposits can advance
    // that clock while leaving the map equal to the opening's, as asserted below.
    let deeper_remainder_depth = 5u32;
    let receiving_clock = 1u64 << ((deeper_remainder_depth - 1) / 2);
    let clocks_start = seeded.find("\nclocks ").unwrap() + 1;
    let clocks_head_end = clocks_start + seeded[clocks_start..].find('\n').unwrap();
    let clock_count: usize = seeded[clocks_start..clocks_head_end]
        .strip_prefix("clocks ")
        .unwrap()
        .parse()
        .unwrap();
    let entries_start = clocks_head_end + 1;
    let mut clocks: Vec<String> = seeded[entries_start..]
        .lines()
        .take(clock_count)
        .map(str::to_owned)
        .collect();
    let clocks_end = entries_start + clocks.iter().map(|line| line.len() + 1).sum::<usize>();
    let receiving_locus = format!("receiving {ring} ");
    let receiving_entry = format!("{receiving_locus}{receiving_clock}");
    if let Some(entry) = clocks
        .iter_mut()
        .find(|line| line.starts_with(&receiving_locus))
    {
        *entry = receiving_entry;
    } else {
        clocks.push(receiving_entry);
    }
    let clock_block = format!("clocks {}\n{}\n", clocks.len(), clocks.join("\n"));
    seeded.replace_range(clocks_start..clocks_end, &clock_block);
    // Recompute the text integrity check after constructing this explicit carried-state fixture.
    let seeded = ContinuingState::stamped(&seeded, &opening).unwrap();
    let state = ContinuingState::from_text(&seeded, opening.budget()).unwrap();
    assert_eq!(
        ContinuingState::from_text(&state.to_text(), opening.budget()).unwrap(),
        state
    );
    let theta = opening.clone().continued(&state).unwrap();
    let restored_carry = theta.receiving_law(ring).unwrap().map_remainder();
    assert_eq!(restored_carry.get(2, 0).unwrap(), &(&unit / integer(8)));
    assert_eq!(restored_carry.get(3, 0).unwrap(), &(-&unit / integer(32)));
    assert_eq!(theta.receiving_map(ring), opening.receiving_map(ring));
    let mut feature = vec![Rat::zero(); width];
    let feature_scale = Rat::from_integer(BigInt::one() << (exponent + 1) as usize);
    feature[0] = feature_scale.clone();
    let tolerance = &field.receivers()[0].tolerance;
    let grain = Rat::new(
        BigInt::one(),
        BigInt::from(holonics::hnn::field::receiver_grain(tolerance).unwrap()) << 1usize,
    );
    assert!(feature_scale > Rat::one() / &unit);
    let retained_reads = restored_carry.apply(&feature).unwrap();
    assert!(retained_reads[2].abs() > grain && retained_reads[3].abs() > grain);
    let event = theta
        .receiving_precision_event(ring, &[feature.clone()], tolerance)
        .unwrap()
        .unwrap();
    assert_eq!(event.erased_components(), &[(0, 2), (0, 3)]);
    assert_eq!(event.levels(), 5);
    let current = Current::at_rest(&field);
    let card = card();
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(&card);
    {
        let mut h = host.mount_with(&field, &current, theta.clone()).unwrap();
        let mut d = device.mount_with(&field, &current, theta.clone()).unwrap();
        let input = word(&field, 8, 0xC0_21);
        let (moment, _) = same(
            "publication open moment",
            host.ingest(&mut h, None, &input),
            device.ingest(&mut d, None, &input),
        )
        .unwrap();
        let phases = h.admitted()[0].clone();
        let (pending, _) = same(
            "publication producing receiver",
            host.refine(&mut h, &moment, &phases),
            device.refine(&mut d, &moment, &phases),
        )
        .unwrap();
        let targets = word(&field, phases.aperture(), 0xC0_22);
        let (staged, _) = same(
            "publication arrived operand",
            host.compare(&mut h, pending, &targets),
            device.compare(&mut d, pending, &targets),
        )
        .unwrap();
        same(
            "publication consumes staged",
            host.discard(&mut h, Handle::Staged(staged)),
            device.discard(&mut d, Handle::Staged(staged)),
        )
        .unwrap();
        let before = h.ledger().balance().clone();
        same(
            "open-moment precision publication",
            h.publish_receiving_precision(&event),
            d.publish_receiving_precision(&event),
        )
        .unwrap();
        let saved = d.continuing_state(field.sources()[0]).unwrap();
        assert_eq!(saved, h.continuing_state(field.sources()[0]).unwrap());
        assert_eq!(h.ledger().balance().publications, before.publications + 1);
        assert_eq!(h.ledger().balance().arrived, before.arrived);
        assert_eq!(h.ledger().balance().cells, before.cells);
        assert_eq!(
            h.ledger().balance(),
            d.ledger().balance(),
            "publication keeps the whole enclosed balance, including the published subtotal"
        );
        let mut cold = device
            .mount_continued(&field, &current, opening.clone(), &saved)
            .unwrap();
        let input = word(&field, 1, 0xC0_23);
        let read = same(
            "publication warm continuation",
            host.ingest(&mut h, Some(&moment), &input),
            device.ingest(&mut d, Some(&moment), &input),
        )
        .unwrap();
        assert_eq!(
            device.ingest(&mut cold, Some(&moment), &input).unwrap(),
            read
        );
        assert_eq!(
            cold.continuing_state(field.sources()[0]).unwrap(),
            d.continuing_state(field.sources()[0]).unwrap()
        );
        assert_eq!(
            h.ledger().balance(),
            d.ledger().balance(),
            "warm continuation preserves publication balance parity"
        );
    }
    let mut h = host.mount_with(&field, &current, theta.clone()).unwrap();
    let mut d = device.mount_with(&field, &current, theta).unwrap();
    same(
        "component precision publication",
        h.publish_receiving_precision(&event),
        d.publish_receiving_precision(&event),
    )
    .unwrap();
    assert_eq!(h.constitution(), d.constitution());
    assert_eq!(h.current(), &current);
    assert_eq!(d.current(), &current);
    let actual = d
        .constitution()
        .receiving_map(ring)
        .unwrap()
        .apply(&feature)
        .unwrap();
    assert_eq!(actual[0], feature_scale);
    assert!(!actual[2].is_zero());
    assert!(!actual[3].is_zero());
    assert!(
        d.publish_receiving_precision(&event).is_err(),
        "stale event must refuse"
    );
    let saved = d.continuing_state(field.sources()[0]).unwrap();
    assert_eq!(
        saved.to_text(),
        h.continuing_state(field.sources()[0]).unwrap().to_text()
    );
    let mut cold = device
        .mount_continued(&field, &current, opening, &saved)
        .unwrap();
    assert_eq!(cold.constitution(), d.constitution());
    let input = word(&field, 8, 0xC0_19);
    let ingested = same(
        "component publication input",
        host.ingest(&mut h, None, &input),
        device.ingest(&mut d, None, &input),
    )
    .unwrap();
    assert_eq!(device.ingest(&mut cold, None, &input).unwrap(), ingested);
    let phases = h.admitted()[0].clone();
    let refined = same(
        "component publication actual word",
        host.refine(&mut h, &ingested.0, &phases),
        device.refine(&mut d, &ingested.0, &phases),
    )
    .unwrap();
    assert_eq!(
        device.refine(&mut cold, &ingested.0, &phases).unwrap(),
        refined
    );
    let released = same(
        "component publication actual release",
        host.release(&mut h, &refined.0, &releasing()),
        device.release(&mut d, &refined.0, &releasing()),
    )
    .unwrap();
    assert_eq!(
        device.release(&mut cold, &refined.0, &releasing()).unwrap(),
        released
    );
}

/// The card reads one fixed producing window per call, and receives its own released prefix
/// through the same tree/population sequence as comparison without changing live carry.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_class_grain_release_matches_scored_prefix_and_preserves_opening() {
    use holonics::hnn::receiving::cells::CellLaw;
    use holonics::receiver::release::KeyStream;
    let field = chain();
    let card = card();
    let host = Reference::campaign_one();
    let device = Resident::campaign_one(&card);
    let current = Current::at_rest(&field);
    let mut h = host.mount(&field, &current).unwrap();
    let mut d = device.mount(&field, &current).unwrap();
    let input = word(&field, 4, 0x12);
    let (moment, _) = same(
        "class release ingest",
        host.ingest(&mut h, None, &input),
        device.ingest(&mut d, None, &input),
    )
    .unwrap();
    let phases = h.admitted()[0].clone();
    let (pending, _) = same(
        "class release refine",
        host.refine(&mut h, &moment, &phases),
        device.refine(&mut d, &moment, &phases),
    )
    .unwrap();
    let saved_current = d.current().clone();
    let saved_carry = d.carried().cloned();
    let committed = same(
        "class commit",
        host.release_cells(&mut h, &pending, CellLaw::Commit),
        device.release_cells(&mut d, &pending, CellLaw::Commit),
    )
    .unwrap();
    let bytes = vec![0x5a, 0x01, 0xc3, 0x7e, 0x0f, 0xe0, 0x21, 0x99];
    let mut hk = KeyStream::new(bytes.clone(), 4).unwrap();
    let mut dk = hk.clone();
    let drawn = same(
        "class draw",
        host.release_cells(&mut h, &pending, CellLaw::Draw(&mut hk)),
        device.release_cells(&mut d, &pending, CellLaw::Draw(&mut dk)),
    )
    .unwrap();
    assert_eq!(hk, dk);
    assert_eq!(d.current(), &saved_current);
    assert_eq!(d.carried(), saved_carry.as_ref());
    let release = drawn.forward.present().unwrap();
    assert_eq!(
        committed.forward.present().unwrap().cells[0].face,
        release.cells[0].face
    );
    let placement = release.classes().expect("fixture draws every phase");
    let mut again = KeyStream::new(bytes, 4).unwrap();
    assert_eq!(
        device
            .release_cells(&mut d, &pending, CellLaw::Draw(&mut again))
            .unwrap()
            .forward
            .present(),
        Some(release)
    );
    // Select the drawn target from an already admitted identity passage; no unchecked encoding.
    let targets = word(&field, 4096, 0x1234);
    let classes: Vec<_> = targets.classes_read().collect();
    let start = classes
        .windows(placement.len())
        .position(|part| part == placement)
        .expect("finite fixture contains drawn pair");
    let input = targets.part(start..start + placement.len()).unwrap();
    let (_, compared) = same(
        "class draw compare",
        host.compare(&mut h, pending, &input),
        device.compare(&mut d, pending, &input),
    )
    .unwrap();
    let ReceiptDetail::Compare { model, .. } = compared.receipt.detail else {
        panic!("comparison receipt");
    };
    for ((code, cell), class) in model.iter().zip(&release.cells).zip(placement) {
        let upper = holonics::ratio::algebraic::log2_enclosure(&cell.face[class].upper).unwrap();
        let lower = holonics::ratio::algebraic::log2_enclosure(&cell.face[class].lower).unwrap();
        assert!(code.lower <= -upper.lower);
        assert!(-lower.upper <= code.upper);
    }
}

#[test]
#[ignore = "R4b test 18: GPU suite only"]
fn r4b_18_founded_mount_refuses_before_upload() {
    let card = card();
    let base = Field::declare(chain_declaration(1 << 16)).unwrap();
    let field = base
        .found(holonics::hnn::FoundedRing { period: 2, key: 1 })
        .unwrap();
    let port = Resident::new(&card, 4, 1 << 40);
    let before = port.traffic();
    assert!(matches!(
        port.mount(&field, &Current::at_rest(&field)),
        Err(HnnError::Founding {
            what: "the card's founded ring is owed (#76)"
        })
    ));
    assert_eq!(port.traffic(), before);
    assert!(matches!(
        super::ResidentMoment::open(&card, &field, &Current::at_rest(&field)),
        Err(super::DeviceError::Hnn(HnnError::Founding {
            what: "the card's founded ring is owed (#76)"
        }))
    ));

    // A host state saved with its founding law open: the card carries no founding law, so the
    // resume refuses before anything crosses the bus rather than dropping the law.
    let mut declaration = chain_declaration(1 << 16);
    declaration.founding = true;
    let field = Field::declare(declaration).unwrap();
    let host = Reference::new(4, 1 << 40);
    let mut saved = host.mount(&field, &Current::at_rest(&field)).unwrap();
    saved.open_founding().unwrap();
    let state = saved.continuing_state(0).unwrap();
    assert!(state.founding_open());
    let opening = Constitution::initial(&field, 1 << 40).unwrap();
    assert!(matches!(
        port.mount_continued(&field, &Current::at_rest(&field), opening, &state),
        Err(HnnError::Founding {
            what: "the card's founding law is owed (#76)"
        })
    ));
    assert_eq!(port.traffic(), before);
}
