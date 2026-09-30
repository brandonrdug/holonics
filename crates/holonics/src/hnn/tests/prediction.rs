//! Native generation (`hnn::prediction`): the continuing word, the refinement's balance, the
//! section return's exact pairing, the release at width zero, the loci a deposit does not reach,
//! and the path's reading of no landmark tree.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{OPEN_BUDGET, chain, generic, moment, six_path};
use super::support::Draw;
use crate::compression::landmark::context::Landmarks;
use crate::hnn::chart::Charts;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::{PairPort, SourceMoment};
use crate::hnn::prediction::{
    BankImages, BankPlacement, Refinement, Section, bank_reach, deposit_of, generate_by_bank,
    stage, stage_bank,
    unreached_unchanged,
};
use crate::hnn::propagation::Operands;
use crate::hnn::ring::{PumpDeclaration, PumpStep, ReceivingBank, ResonatorMaterial};
use crate::hnn::word::{EndChange, Word};
use crate::holon::parametron::{Carrier, Parametron};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};
use crate::receiver::population::PortPopulation;
use crate::receiver::release::ReleaseReturn;

/// A cycle parametron of `d` nodes (unit branches), the ring's resonator base.
fn cycle(d: usize) -> Parametron {
    let incidence = crate::ratio::linear::vector::matrix(d, d, |branch, node| {
        if node == branch {
            -Rat::one()
        } else if node == (branch + 1) % d {
            Rat::one()
        } else {
            Rat::zero()
        }
    })
    .unwrap();
    Parametron::new(incidence, vec![Rat::one(); d], vec![integer(2); d]).unwrap()
}

/// The constitution with a pumped resonator declared on every ring.
fn resonant(field: &Field, theta: Constitution) -> Constitution {
    let mut resonant = theta;
    for ring in 0..field.rings().len() {
        let period = field.ring(ring).period() as usize;
        let pump =
            PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
        resonant = resonant
            .with_ring_resonator(
                field,
                ring,
                ResonatorMaterial::of_parametron(&cycle(period), &rat(1, 8), Some(pump)).unwrap(),
            )
            .unwrap();
    }
    resonant
}

/// The same resonators unpumped: the loaded resonators passive (`C, K, D ⪰ 0`), whose growth the
/// certified step reads as one.
fn loaded(field: &Field, theta: Constitution) -> Constitution {
    let mut loaded = theta;
    for ring in 0..field.rings().len() {
        let period = field.ring(ring).period() as usize;
        loaded = loaded
            .with_ring_resonator(
                field,
                ring,
                ResonatorMaterial::of_parametron(&cycle(period), &rat(1, 8), None).unwrap(),
            )
            .unwrap();
    }
    loaded
}

fn storage(field: &Field, seed: u64) -> Vec<Vec<Rat>> {
    let mut draw = Draw::new(seed);
    field
        .rings()
        .iter()
        .map(|ring| draw.half_vector(ring.width()))
        .collect()
}

/// A word opened at rest is the continuing word opened on the rest change at tick zero.
#[test]
fn a_word_at_rest_is_the_continuing_word_on_the_rest_change() {
    let field = chain();
    let theta = resonant(&field, generic(&field, 71));
    let current = Current::at_rest(&field);
    let operands = Operands::at_cut(&field, &theta, &current).unwrap();
    let injected = storage(&field, 72);
    let mut rest = Word::on_operands(&field, operands.clone(), injected.clone()).unwrap();
    rest.run(3).unwrap();
    let mut continuing = Word::continuing(
        &field,
        operands.clone(),
        &EndChange::rest(&field, &operands),
        &injected,
        0,
    )
    .unwrap();
    continuing.run(3).unwrap();
    assert_eq!(rest.change().unwrap(), continuing.change().unwrap());
    assert_eq!(rest.field_balances(), continuing.field_balances());
}

/// **Continuing motion carries the whole change** (`hnn::word`, "Continuing motion within a
/// refinement"): under the exact law, two words of two ticks, the second opened on the first's
/// change with nothing injected, end on the change one word of four ticks ends on, the pumped
/// resonators' states and phases included; each word's ticks close and the second's first tick
/// opens at the first's last energy.
#[test]
fn continuing_words_carry_waves_contact_and_resonator_states() {
    let field = chain().with_exact_word();
    let theta = resonant(&field, generic(&field, 73));
    let current = Current::at_rest(&field);
    let operands = Operands::exact_at_cut(&field, &theta, &current).unwrap();
    let injected = storage(&field, 74);
    let mut whole = Word::on_operands(&field, operands.clone(), injected.clone()).unwrap();
    whole.run(4).unwrap();
    let mut first = Word::on_operands(&field, operands.clone(), injected).unwrap();
    first.run(2).unwrap();
    let carried = first.change().unwrap();
    let nothing: Vec<Vec<Rat>> = carried
        .storage
        .iter()
        .map(|wave| vec![Rat::zero(); wave.len()])
        .collect();
    let mut second = Word::continuing(&field, operands, &carried, &nothing, 2).unwrap();
    second.run(2).unwrap();
    assert_eq!(second.change().unwrap(), whole.change().unwrap());
    assert!(
        carried
            .resonators
            .iter()
            .flatten()
            .flatten()
            .flatten()
            .any(|x| !x.is_zero()),
        "the resonator states carried are not at rest"
    );
    let (last, next) = (
        first.field_balances().last().unwrap(),
        &second.field_balances()[0],
    );
    assert_eq!(last.after, next.before);
    assert_eq!(last.resonator_after, next.resonator_before);
    for tick in first.field_balances().iter().chain(second.field_balances()) {
        assert!(tick.closes(), "{tick:?}");
    }
    assert_eq!(second.field_balances(), &whole.field_balances()[2..]);
}

fn declared(field: &Field, words: usize, span: usize) -> Refinement {
    let receiver = field.receivers()[0].ring;
    let stations = field.ring(receiver).period() as usize;
    Refinement::declare(field, receiver, words, span, stations, field.alphabet() - 1).unwrap()
}

/// **The refinement's balance closes** on the words' lattice with resonators pumped: every tick
/// closes, the ticks chain within and across the words, the request's moment is the only jump at a
/// word's open, the identity telescopes within its certified bound, and across the commit the
/// deposition work closes it.
#[test]
fn the_refinement_balance_closes_with_the_injection_the_pump_and_the_commit() {
    let field = chain();
    let theta = resonant(&field, generic(&field, 75));
    // A moment whose phases leave the path from the source to the receiver open, so the section
    // reads a nonzero anchor and the deposit moves its linear loci.
    let (current, moment) = moment(&field, 177, 11);
    let refinement = declared(&field, 3, 2);
    let section = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    let balance = section.balance().clone();
    assert_eq!(balance.words, 3);
    assert_eq!(balance.ticks, 6);
    assert!(balance.every_tick_closes && balance.chained, "{balance:?}");
    assert!(!balance.injected.is_zero(), "the moment re-enters");
    assert!(!balance.pump.is_zero(), "the pump works across the words");
    assert!(balance.closes(), "{balance:?}");
    let targets: Vec<usize> = (0..refinement.stations()).map(|j| j % 4).collect();
    let staged = stage(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &targets,
        &vec![false; refinement.stations()],
        &mut Charts::new(),
        false,
    )
    .unwrap();
    // Pumped, every ring's growth is read by its Floquet reach (`hnn::constitution`, "The pumped
    // medium's reach"): the step through the pumped rings is certified and taken, the rings' own
    // gain families held, and the balance closes across the commit within the committed energy
    // bound read with the span factor at the refinement's span.
    let deposit = deposit_of(&theta, &refinement, std::slice::from_ref(&staged.composed)).unwrap();
    let medium = theta.medium_reach(refinement.last_epoch() as u64).unwrap();
    assert_eq!(medium.rings.len(), field.rings().len());
    assert!(theta.amplitude().unwrap().is_none());
    let (next, reading) = theta.deposited(&deposit).unwrap();
    assert!(!reading.steps.is_empty());
    assert!(reading.steps.iter().all(|(_, step)| step.step.holds()));
    let pumped = reading
        .pumped
        .clone()
        .expect("the pumped rings' reach is read");
    assert!(
        pumped
            .held
            .iter()
            .all(|(locus, _)| matches!(locus, crate::hnn::constitution::Locus::Resonator(_)))
    );
    assert!(
        reading
            .steps
            .iter()
            .all(|(locus, _)| !matches!(locus, crate::hnn::constitution::Locus::Resonator(_)))
    );
    let mut pumped_balance = balance.clone();
    let before = crate::hnn::word::PowerForm::read(&field, &theta, &current).unwrap();
    let after = crate::hnn::word::PowerForm::read(&field, &next, &current).unwrap();
    pumped_balance
        .commit(&before, &after, section.end())
        .unwrap();
    assert!(pumped_balance.closes(), "{pumped_balance:?}");
    let passive = pumped_balance
        .energy_bound(
            &refinement,
            &medium.amplitude,
            &reading.storage_growth,
            field.word_lattice(),
        )
        .unwrap();
    let factor = medium.factor(refinement.last_epoch() as u64).unwrap();
    assert!(passive.committed <= &passive.bound * factor, "{passive:?}");
    // Unpumped, the loaded resonators are passive: the step is certified and the balance closes
    // across its commit, within the committed energy bound.
    let theta = loaded(&field, generic(&field, 75));
    let section = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    let mut balance = section.balance().clone();
    assert!(balance.closes(), "{balance:?}");
    let staged = stage(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &targets,
        &vec![false; refinement.stations()],
        &mut Charts::new(),
        false,
    )
    .unwrap();
    let deposit = deposit_of(&theta, &refinement, std::slice::from_ref(&staged.composed)).unwrap();
    let amplitude = theta.amplitude().unwrap().unwrap();
    let (next, reading) = theta.deposited(&deposit).unwrap();
    assert!(!reading.steps.is_empty());
    assert!(reading.steps.iter().all(|(_, step)| step.step.holds()));
    let before = crate::hnn::word::PowerForm::read(&field, &theta, &current).unwrap();
    let after = crate::hnn::word::PowerForm::read(&field, &next, &current).unwrap();
    balance.commit(&before, &after, section.end()).unwrap();
    assert!(balance.commit.is_some());
    assert!(balance.closes(), "{balance:?}");
    let bound = balance
        .energy_bound(
            &refinement,
            &amplitude,
            &reading.storage_growth,
            field.word_lattice(),
        )
        .unwrap();
    assert!(bound.holds, "{bound:?}");
}

/// **The section's return is the exact adjoint of its refinement** on the executed charts with no
/// transient split: the stations' covectors paired with their logits equal the words' opening
/// covectors paired with the injections, and the pairing is not zero.
#[test]
fn the_section_return_pairs_exactly_on_the_executed_charts() {
    let field = chain();
    for (seed, theta) in [
        (77u64, generic(&field, 77)),
        (78, resonant(&field, generic(&field, 78))),
    ] {
        let (current, moment) = moment(&field, seed + 100, 11);
        let refinement = declared(&field, 3, 2);
        let targets: Vec<usize> = (0..refinement.stations()).map(|j| (j + 1) % 4).collect();
        let staged = stage(
            &field,
            &theta,
            &current,
            &moment,
            &refinement,
            &targets,
            &vec![false; refinement.stations()],
            &mut Charts::new(),
            true,
        )
        .unwrap();
        let pairing = staged.pairing.unwrap();
        assert!(pairing.holds(), "{pairing:?}");
        assert!(!pairing.produced.is_zero());
    }
}

/// **The release commits a determined section at width zero and holds a plural one**: at the
/// initial constitution `R = 0` reads every class at one cell, so every station is plural and the
/// section is held; at a generic `R` every station's top cell is unique and it is released.
#[test]
fn the_release_holds_a_plural_section_and_releases_a_determined_one() {
    let field = chain();
    let (current, moment) = moment(&field, 79, 7);
    let refinement = declared(&field, 2, 2);
    let initial = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let plural = Section::refine(
        &field,
        &initial,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap()
    .release()
    .unwrap();
    assert_eq!(plural.decision, ReleaseReturn::Hold);
    assert_eq!(plural.width, Rat::one());
    assert_eq!(plural.plural.len(), refinement.stations());
    // The chain's anchor at ring 2 is small (the moment's population chart and two contacts): a
    // receiving map at the scale 2^12 reads its classes on separate grain cells.
    let mut draw = Draw::new(80);
    let receiving = field.receivers()[0].ring;
    let scaled = draw
        .half_matrix(2 * field.alphabet(), field.ring(receiving).width())
        .scaled(&integer(1 << 12));
    let theta = generic(&field, 80)
        .with_ports(receiving, None, None, Some(scaled))
        .unwrap();
    let determined = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap()
    .release()
    .unwrap();
    assert!(determined.released(), "{determined:?}");
    assert!(determined.width.is_zero());
    assert!(determined.plural.is_empty());
    assert_eq!(determined.classes.len(), refinement.stations());
    let end = determined.terminated.unwrap_or(refinement.stations());
    assert_eq!(determined.emitted, determined.classes[..end].to_vec());
}

/// **A deposit reaches only the refinement's diamond** (Lean `HNN/Retention.deposit_descends`): on
/// the six-ring path read at ring 2 after two words of two ticks, rings 3–5's elements, standings
/// and the far channels lie outside the diamond and are unchanged, material and clock, while the
/// receiving map moves.
#[test]
fn a_deposit_leaves_every_unreached_locus_unchanged() {
    let field = six_path(1);
    let theta = generic(&field, 81);
    let (current, moment) = moment(&field, 82, 5);
    let refinement = declared(&field, 2, 2);
    let diamond = refinement.diamond(&field);
    let targets: Vec<usize> = (0..refinement.stations()).map(|j| j % 2).collect();
    let staged = stage(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &targets,
        &vec![false; refinement.stations()],
        &mut Charts::new(),
        false,
    )
    .unwrap();
    let deposit = deposit_of(&theta, &refinement, std::slice::from_ref(&staged.composed)).unwrap();
    assert!(deposit.landmarks().is_empty() && deposit.receiving().is_empty());
    let (next, _) = theta.deposited(&deposit).unwrap();
    let (count, unchanged) = unreached_unchanged(&field, &theta, &next, &diamond);
    assert!(count > 0, "the path's far rings lie outside the diamond");
    assert!(unchanged);
    assert_ne!(theta.receiving_map(2), next.receiving_map(2));
}

/// A constitution read that refuses the receiving tree and population: the section's forward reads
/// neither (no window anywhere).
struct NoTree<'a>(&'a Constitution);

impl ConstitutionRead for NoTree<'_> {
    fn standing(&self, ring: usize) -> &[Rat] {
        self.0.standing(ring)
    }
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix {
        self.0.passive_factor(ring)
    }
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix {
        self.0.contrast_port(ring)
    }
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        self.0.slices(ring)
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.0.source_port(ring)
    }
    fn pair_port(&self, ring: usize, offset: usize) -> Option<&PairPort> {
        self.0.pair_port(ring, offset)
    }
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix {
        self.0.contact_storage(contact)
    }
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix {
        self.0.contact_stiffness(contact)
    }
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix {
        self.0.contact_dissipation(contact)
    }
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.0.receiving_map(ring)
    }
    fn landmarks(&self, _ring: usize) -> Option<&Landmarks> {
        panic!("the native section reads no landmark tree")
    }
    fn population(&self, _ring: usize) -> Option<&PortPopulation> {
        panic!("the native section reads no receiving population")
    }
    fn ring_resonator(&self, ring: usize) -> Option<&ResonatorMaterial> {
        self.0.ring_resonator(ring)
    }
}

/// The section's forward reads the request only through its moment: never the landmark tree, its
/// suffix address or the receiving population.
#[test]
fn the_section_reads_no_landmark_tree() {
    let field = chain();
    let theta = generic(&field, 83);
    let (current, moment): (Current, SourceMoment) = moment(&field, 84, 6);
    let refinement = declared(&field, 2, 1);
    let plain = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap()
    .faces()
    .clone();
    let guarded = Section::refine(
        &field,
        &NoTree(&theta),
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap()
    .faces()
    .clone();
    assert_eq!(plain, guarded);
}

/// Every station of a section is read from its one anchor: station `j` reads the receiving ring's
/// anchor through the port map to the power `1 + j`, so the section is one joint reading, never a
/// product of station marginals.
#[test]
fn every_station_is_read_from_the_one_anchor() {
    let field = chain();
    let theta = generic(&field, 85);
    let (current, moment) = moment(&field, 86, 6);
    let refinement = declared(&field, 2, 1);
    let section = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    assert!(section.anchor().iter().any(|x| !x.is_zero()));
    let ring = field.ring(refinement.ring());
    for (j, read) in section.reads().iter().enumerate() {
        assert_eq!(
            read,
            &ring.rotate(section.anchor(), &BigInt::from(j as u64 + 1))
        );
    }
}

// -------------------------------------------------------------------------------------------
// the order repair: the joint residue class, the section's placement and the lock

/// **A joint-residue field**: three rings of period `6 = 2·3` in a chain `0 — 1 — 2`, joined node to
/// node on every node at exponent 0; ring 0 the source and receiving ring, stepping every cell (its
/// lock every port), rings 1 and 2 stepping by carries; no pair offset; `|A| = 3`, the last class
/// the termination.
fn joint() -> Field {
    Field::declare(
        crate::hnn::field::FieldDeclaration {
            rings: vec![
                super::support::ring(6, (0..6).collect()),
                super::support::ring(6, Vec::new()),
                super::support::ring(6, Vec::new()),
            ],
            contacts: vec![
                super::support::contact(0, 1, 6, 0),
                super::support::contact(1, 2, 6, 0),
            ],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 3,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![crate::hnn::field::ReceiverDeclaration {
                ring: 0,
                aperture: 3,
                tolerance: rat(1, 16),
                depth: 1,
                prior: crate::compression::landmark::context::StopPrior::half(),
            }],
            crib: crate::hnn::field::CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// **A placed datum is read at its station's residue, in the passage's one population**
/// (`SourceMoment::continued`; Lean `HNN/IndexedOpen.{passage_population, passage_read}`): the
/// datum locked at station `j` is counted into the request's phase counts at the receiving ring's
/// residue `τ + 1 + j`, the passage's population is the request's `n` plus the placed data, and the
/// open storage is the request's counts and the datum's column of `E`, rotated to station `j`'s
/// frame by `P^(1+j)`, together over `ν̂(n + 1)`.
#[test]
fn a_placed_datum_is_read_at_its_station_residue() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, request) = moment(&field, 92, 7);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let phase = current.phase(&field, 0).unwrap() as usize;
    let n = request.population(0).unwrap();
    let nu = crate::hnn::moment::PopulationChart::of(&field).value(n + 1);
    let port = theta.source_port(0).unwrap();
    let ring = field.ring(0);
    let (reads, pairs) = request.open_parts(&field, &theta, &current, 0).unwrap();
    assert!(pairs.iter().all(Rat::is_zero));
    let mut marginal = vec![Rat::zero(); ring.width()];
    for (_, read) in &reads {
        for (value, add) in marginal.iter_mut().zip(read) {
            *value += add;
        }
    }
    for station in 0..4 {
        for code in 0..field.alphabet() {
            let mut cells = vec![None; 4];
            cells[station] = Some(code);
            let passage = refinement.passage(&field, &current, &request, &cells).unwrap();
            assert_eq!(passage.cells(), request.cells() + 1);
            assert_eq!(passage.population(0).unwrap(), n + 1);
            let residue = (phase + 1 + station) % 6;
            assert_eq!(
                passage.phase_counts(0, residue).unwrap()[code],
                request.phase_counts(0, residue).unwrap()[code] + 1
            );
            let open = passage.open_storage(&field, &theta, &current).unwrap();
            let read = ring.rotate(&open[0], &BigInt::from(station as u64 + 1));
            let column: Vec<Rat> = (0..ring.width())
                .map(|row| port.get(row, code).unwrap().clone())
                .collect();
            let request_read = ring.rotate(&marginal, &BigInt::from(station as u64 + 1));
            let expected: Vec<Rat> = request_read
                .iter()
                .zip(&column)
                .map(|(r, c)| (r + c) * &nu)
                .collect();
            assert_eq!(read, expected);
        }
    }
}

/// **One passage weighs every datum alike** (the September 30 located cause, repaired; Lean
/// `HNN/IndexedOpen.{passage_weight_one_population, separate_populations_ratio}`): in the passage's
/// open, a request cell and a section datum at the same class and residue class enter with the
/// same weight `ν̂(n + v)`, so moving a crossing from the request to the section moves nothing but
/// its tick; read over separate populations, the section's datum weighed `n/v` times the request's.
#[test]
fn one_passage_weighs_every_datum_alike() {
    let field = joint();
    let theta = generic(&field, 91);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    // Seven cells ingested and their continuation by one placed datum, against eight cells
    // ingested: the same passage, split at a different tick.
    let cells = [2usize, 0, 1, 1, 0, 2, 1, 0];
    let (whole_current, whole) = {
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        moment.ingest(&field, &mut current, &cells).unwrap();
        (current, moment)
    };
    let (current, request) = {
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        moment.ingest(&field, &mut current, &cells[..7]).unwrap();
        (current, moment)
    };
    // The joint field's receiving ring steps every cell, so the continuation's station 0 is the
    // eighth cell's tick.
    let passage = refinement
        .passage(&field, &current, &request, &[Some(cells[7]), None, None, None])
        .unwrap();
    assert_eq!(passage.population(0).unwrap(), whole.population(0).unwrap());
    for c in 0..6 {
        assert_eq!(passage.phase_counts(0, c).unwrap(), whole.phase_counts(0, c).unwrap());
    }
    // The same counts and population: the same open, read at the request's frame (the whole
    // passage's frame is one tick on, the rotation between them).
    let open = passage.open_storage(&field, &theta, &current).unwrap();
    let whole_open = whole.open_storage(&field, &theta, &whole_current).unwrap();
    assert_eq!(field.ring(0).rotate(&open[0], &BigInt::one()), whole_open[0]);
}

/// **A compared station never reads its own target**, and the partition's ratio is the whole
/// ratio at its stations: two target sections that differ only at the compared stations give the
/// same faces; the partition's covector is zero at the locked stations and equals the whole
/// comparison's at the compared ones; the staged return with the section placed pairs exactly.
#[test]
fn a_compared_station_never_reads_its_own_target() {
    let field = joint();
    let theta = generic(&field, 93);
    let (current, moment) = moment(&field, 94, 9);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let locked = [true, false, true, false];
    let compared: Vec<bool> = locked.iter().map(|lock| !lock).collect();
    let first = [0usize, 1, 2, 0];
    let second = [0usize, 2, 2, 1];
    let faces = |targets: &[usize]| {
        let cells: Vec<Option<usize>> = targets
            .iter()
            .zip(&locked)
            .map(|(&t, &lock)| lock.then_some(t))
            .collect();
        let passage = refinement.passage(&field, &current, &moment, &cells).unwrap();
        Section::refine(
            &field,
            &theta,
            &current,
            &passage,
            &refinement,
            &mut Charts::new(),
        )
        .unwrap()
    };
    let section = faces(&first);
    assert_eq!(section.faces(), faces(&second).faces());
    let whole = section.compare(&first).unwrap().covector().unwrap();
    let part = section
        .compare_partition(&first, &compared)
        .unwrap()
        .covector()
        .unwrap();
    for (j, lock) in locked.iter().enumerate() {
        if *lock {
            assert!(part.logits()[j].iter().all(Rat::is_zero));
        } else {
            assert_eq!(part.logits()[j], whole.logits()[j]);
        }
    }
    let staged = stage(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &first,
        &locked,
        &mut Charts::new(),
        true,
    )
    .unwrap();
    assert_eq!(staged.ratio.stations(), &[1, 3]);
    let pairing = staged.pairing.unwrap();
    assert!(pairing.holds() && !pairing.produced.is_zero(), "{pairing:?}");
    assert!(staged.balance.closes());
}

/// **The partition law** (`prediction::mask`): at least one station is always compared, and every
/// number of locked stations `0 … m − 1` is drawn.
#[test]
fn the_mask_compares_a_station_and_reaches_every_level() {
    let mut draw = crate::holarchy::terrain::Draw::new(95);
    let mut levels = [0usize; 8];
    for _ in 0..512 {
        let locked = crate::hnn::prediction::mask(&mut draw, 8);
        let count = locked.iter().filter(|&&lock| lock).count();
        assert!(count < 8);
        levels[count] += 1;
    }
    assert!(levels.iter().all(|&count| count > 0), "{levels:?}");
}

/// **Generation locks by the largest gap and releases at width zero** (`prediction::generate`): at
/// the initial constitution (`R = 0`) every station is plural, so the first refinement holds the
/// whole section; at a generic constitution with a receiving map at scale `2^12` every lock reads a
/// unique top cell, the locks partition the stations, one refinement a lock, every balance closes,
/// and the section is released at width zero with each locked class.
#[test]
fn generation_locks_by_the_largest_gap_and_releases_at_width_zero() {
    let field = joint();
    let (current, moment) = moment(&field, 96, 9);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let initial = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let held = crate::hnn::prediction::generate(
        &field,
        &initial,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    assert_eq!(held.release.decision, ReleaseReturn::Hold);
    assert_eq!(held.refinements, 1);
    assert_eq!(held.release.plural, vec![0, 1, 2, 3]);
    let mut draw = Draw::new(97);
    let scaled = draw
        .half_matrix(2 * field.alphabet(), field.ring(0).width())
        .scaled(&integer(1 << 12));
    let theta = generic(&field, 97)
        .with_ports(0, None, None, Some(scaled))
        .unwrap();
    let generated = crate::hnn::prediction::generate(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    assert!(generated.release.released(), "{generated:?}");
    assert!(generated.release.width.is_zero());
    assert_eq!(generated.refinements, generated.locks.len());
    assert_eq!(generated.balances_closed, generated.refinements);
    let mut stations: Vec<usize> = generated.locks.iter().flatten().copied().collect();
    stations.sort_unstable();
    assert_eq!(stations, vec![0, 1, 2, 3]);
    // The first lock is the unplaced section's leader: its release reads the same top classes there.
    let first = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap()
    .release()
    .unwrap();
    for &station in &generated.locks[0] {
        assert_eq!(generated.release.classes[station], first.classes[station]);
    }
}

/// **The bank's placement is the section's injection** (`prediction::BankPlacement`): at a
/// transport of modulus one the receiving ring's storage with any set of stations placed, read from
/// any station, equals the open storage of the passage (the request's moment continued by the
/// section, `SourceMoment::continued`), exactly, every datum at `ν̂(n + v)` in every frame; with
/// nothing placed it is the request's own.
#[test]
fn the_bank_placement_is_the_sections_injection() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, request) = moment(&field, 92, 7);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let placement =
        BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
    let patterns: [[Option<usize>; 4]; 5] = [
        [None; 4],
        [Some(1), None, None, None],
        [None, Some(2), None, Some(0)],
        [Some(0), Some(0), Some(1), None],
        [Some(2), Some(1), Some(0), Some(1)],
    ];
    for cells in &patterns {
        let passage = refinement.passage(&field, &current, &request, cells).unwrap();
        let injected = passage.open_storage(&field, &theta, &current).unwrap();
        let placed = cells.iter().filter(|cell| cell.is_some()).count() as u64;
        let nu = crate::hnn::moment::PopulationChart::of(&field)
            .value(request.population(0).unwrap() + placed);
        for station in 0..4 {
            assert_eq!(placement.storage(station, cells), injected[0]);
            let (request_weights, station_weights) = placement.weights(station, cells);
            assert!(request_weights.iter().all(|w| *w == nu));
            for (cell, weight) in cells.iter().zip(&station_weights) {
                assert_eq!(weight.as_ref(), cell.map(|_| &nu));
            }
        }
    }
    let open = request.open_storage(&field, &theta, &current).unwrap();
    assert_eq!(placement.storage(0, &[None; 4]), open[0]);
}

/// **Under a dissipative transport a candidate reads the span from its own station**
/// (`prediction::BankPlacement`, the station-framed law; Lean
/// `HNN/IndexedOpen.{framed_weight_mass, framed_weight_one_sided, framed_weight_ratio,
/// framed_weight_symmetric}`): at a transport modulus `ρ = 3/4`, read from station `j`,
/// - every datum weighs `ρ^|τ_j − τ_k|` over the span's transported mass read from `j`, on the
///   population chart: the weights carry unit mass within the chart's residual;
/// - when no placed datum lies after `j`, the storage equals the continued passage's open (read
///   at the span's last datum) exactly: the one-way law on past data;
/// - a placed datum `r` ticks from `j`, on either side, weighs `ρ^r` times `j`'s own candidate
///   (within the chart's residual), so two data at equal distance on either side weigh alike, and a
///   lock after `j` weighs less than the candidate, where the one-way law read at the span's end
///   weighs it `ρ^(−r)` times the candidate;
/// - the modulus's derivative matches the exact weights' central difference to the second order;
/// - a request whose span with the stations exceeds one turn is refused, as is a modulus outside
///   `(0, 1]`; and the readout's one anchor refuses a lock after an open station below modulus one
///   (`Refinement::anchor_frames`), `stage` with it.
#[test]
fn the_bank_placement_under_a_dissipative_transport() {
    use crate::hnn::HnnError;
    use crate::hnn::moment::{PopulationChart, modulus_power};
    let field = joint();
    let theta = generic(&field, 91);
    assert_eq!(theta.transport(0), Rat::one());
    assert!(matches!(
        theta.clone().with_transport(0, Rat::zero()),
        Err(HnnError::Transport { .. })
    ));
    assert!(matches!(
        theta.clone().with_transport(0, rat(5, 4)),
        Err(HnnError::Transport { .. })
    ));
    let modulus = rat(3, 4);
    let theta = theta.with_transport(0, modulus.clone()).unwrap();
    assert_eq!(theta.transport(0), modulus);
    // Two cells and four stations fill the ring's turn of six ticks.
    let (current, request) = moment(&field, 92, 2);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let placement = BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
    let chart = PopulationChart::of(&field);
    let near = |a: &Rat, b: &Rat, slack: &Rat| (a - b).abs() <= *slack;
    let patterns: [[Option<usize>; 4]; 6] = [
        [None; 4],
        [Some(1), None, None, None],
        [None, Some(2), None, Some(0)],
        [Some(0), Some(0), Some(1), None],
        [Some(2), Some(1), Some(0), Some(1)],
        [Some(0), Some(1), Some(2), Some(0)],
    ];
    let mut two_sided = 0usize;
    for cells in &patterns {
        let passage = refinement.passage(&field, &current, &request, cells).unwrap();
        let injected = passage.open_storage(&field, &theta, &current).unwrap();
        let last = cells.iter().rposition(Option::is_some);
        for station in 0..4 {
            let (request_weights, station_weights) = placement.weights(station, cells);
            // Every datum's weight within the chart's residual of its exact transported weight, the
            // exact weights summing to one: so the charted mass lies within one residual a datum.
            let data: Vec<Rat> = request_weights
                .iter()
                .cloned()
                .chain(station_weights.iter().flatten().cloned())
                .collect();
            let counted: Rat = data.iter().sum();
            let slack = chart.residual() * Rat::from_integer(BigInt::from(data.len() as u64 + 2));
            assert!((&counted - Rat::one()).abs() <= slack, "{counted}");
            // On past data the one-way law, read at the span's last datum, exactly.
            if last.is_none_or(|last| last <= station) {
                assert_eq!(placement.storage(station, cells), injected[0]);
            } else {
                two_sided += 1;
            }
            // A placed datum r ticks away, on either side, weighs ρ^r times the station's own
            // candidate (every weight within the chart's residual of its exact value).
            if let Some(own) = &station_weights[station] {
                let residual = chart.residual() * integer(2);
                for (placed, weight) in station_weights.iter().enumerate() {
                    let Some(weight) = weight else { continue };
                    let r = placed.abs_diff(station) as u64;
                    let power = modulus_power(&modulus, r);
                    assert!(near(weight, &(own * &power), &residual), "ρ^{r} of the candidate");
                    if placed > station {
                        assert!(weight < own, "a later lock weighs less than the candidate");
                    }
                }
                // Two data at equal distance on either side weigh alike.
                if station >= 1 && station + 1 < 4 {
                    if let (Some(before), Some(after)) =
                        (&station_weights[station - 1], &station_weights[station + 1])
                    {
                        assert_eq!(before, after);
                    }
                }
            }
            // The modulus's derivative against the exact weights' central difference: second order.
            if cells.iter().any(Option::is_some) {
                let derivative = placement.modulus_derivative(station, cells);
                let residual = |h: &Rat| -> Rat {
                    let up = placement.exact_storage(station, cells, &(&modulus + h));
                    let down = placement.exact_storage(station, cells, &(&modulus - h));
                    up.iter()
                        .zip(&down)
                        .zip(&derivative)
                        .map(|((u, d), g)| ((u - d) / (integer(2) * h) - g).abs())
                        .max()
                        .unwrap()
                };
                let (wide, narrow) = (residual(&rat(1, 64)), residual(&rat(1, 128)));
                assert!(narrow * integer(3) <= wide, "the central difference is second order");
            }
        }
    }
    assert!(two_sided > 0, "some reading holds a lock after its station");
    // The one-way law read at the span's end against the framed law, from station 0 with a lock at
    // station 3: the end frame weighs the lock ρ^(−3) times station 0's candidate, the framed law
    // ρ^3 times.
    let cells = [Some(1), None, None, Some(0)];
    let passage = refinement.passage(&field, &current, &request, &cells).unwrap();
    let oneway = passage.phase_weights(&field, 0, &modulus).unwrap();
    let phase = current.phase(&field, 0).unwrap() as usize;
    let (at0, at3) = (&oneway[(phase + 1) % 6], &oneway[(phase + 4) % 6]);
    let power = modulus_power(&modulus, 3);
    let residual = chart.residual() * integer(2);
    assert!(near(at0, &(at3 * &power), &residual));
    let (_, framed) = placement.weights(0, &cells);
    let (own, lock) = (framed[0].clone().unwrap(), framed[3].clone().unwrap());
    assert!(near(&lock, &(&own * &power), &residual));
    assert!(lock < own && at3 > at0);
    // Seven cells and four stations span more than the turn of six: refused below modulus one.
    let (long_current, long_request) = moment(&field, 92, 7);
    assert!(matches!(
        BankPlacement::of(&field, &theta, &long_current, &long_request, &refinement),
        Err(HnnError::AliasedAges { .. })
    ));
    // The readout's one anchor: a lock after an open station is refused below modulus one, and
    // `stage` refuses it; a lock before every open station, or any lock at modulus one, is read.
    assert!(refinement.anchor_frames(&theta, &[Some(0), None, None, None]).is_ok());
    assert!(refinement.anchor_frames(&theta, &[Some(0), Some(1), None, None]).is_ok());
    assert!(matches!(
        refinement.anchor_frames(&theta, &[None, Some(1), None, None]),
        Err(HnnError::UnframedAnchor { station: 0, placed: 1, .. })
    ));
    let unit = generic(&field, 91);
    assert!(refinement.anchor_frames(&unit, &[None, Some(1), None, None]).is_ok());
    let mut charts = Charts::new();
    assert!(matches!(
        stage(
            &field,
            &theta,
            &current,
            &request,
            &refinement,
            &[1, 2, 0, 1],
            &[false, true, false, false],
            &mut charts,
            false,
        ),
        Err(HnnError::UnframedAnchor { station: 0, placed: 1, .. })
    ));
}

/// **The transport is founded off the lossless boundary** (`Constitution::founding_transport`;
/// Lean `HNN/IndexedOpen.{IsFounding, founded_modulus_pow_le, founded_modulus_greatest,
/// founded_modulus_lt_one, order_founding}`): the founding modulus is the greatest on the source
/// port's lattice whose one-turn transport is at most one unit of the weights' chart,
/// `ρ₀^d ≤ 2^(−L_ν) < (ρ₀ + 2^(−L_s))^d`, strictly between zero and one; the order-2 declaration
/// (`d = 60`, `L_ν = L_s = 21`) founds at `102837/131072`; on the joint field's ring of period 6 the
/// founded constitution carries it, and a ring with no source port refuses it.
#[test]
fn the_transport_is_founded_off_the_lossless_boundary() {
    use crate::hnn::HnnError;
    use crate::hnn::constitution::{Locus, founding_modulus};
    use crate::hnn::moment::PopulationChart;
    let check = |lattice: u32, period: u64, chart: u32| -> Rat {
        let modulus = founding_modulus(lattice, period, chart).unwrap();
        let unit = Rat::new(BigInt::one(), BigInt::one() << lattice as usize);
        let grain = Rat::new(BigInt::one(), BigInt::one() << chart as usize);
        let power = |x: &Rat| (0..period).fold(Rat::one(), |p, _| p * x);
        assert!(modulus.is_positive() && modulus < Rat::one());
        assert!((&modulus / &unit).is_integer());
        assert!(power(&modulus) <= grain);
        assert!(power(&(&modulus + &unit)) > grain);
        modulus
    };
    assert_eq!(check(21, 60, 21), rat(102837, 131072));
    assert_eq!(check(21, 35, 21), rat(345901, 524288));
    assert_eq!(founding_modulus(2, 3, 7), None);
    let field = joint();
    let theta = generic(&field, 91);
    let lattice = theta.lattice(Locus::SourcePort(0)).unwrap().exponent();
    let chart = PopulationChart::of(&field).exponent();
    let founded = theta.clone().founded_transport(&field, 0).unwrap();
    assert_eq!(
        founded.transport(0),
        check(lattice, field.ring(0).period(), chart)
    );
    assert_eq!(founded.transport(0), theta.founding_transport(&field, 0).unwrap());
    assert!(matches!(
        theta.founding_transport(&field, 1),
        Err(HnnError::MissingSourcePort { ring: 1 })
    ));
}

/// **The bank generates by its locks** (`prediction::generate_by_bank`): on the joint field's ring of
/// period 6, a bank of the members whose period divides the turn (standing and half-turn) reads
/// every unlocked station's candidates, locks the stations of the largest gap, each lock certified
/// on both members with every executed tick closed and its growth above the runner-up's; a
/// released section is released at width zero with every station locked once.
#[test]
fn the_bank_generates_by_its_certified_locks() {
    let field = joint();
    let theta = generic(&field, 94);
    let (current, request) = moment(&field, 95, 9);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let identity = ExactRatMatrix::identity(2).unwrap();
    let axis = Carrier::new(Rat::one(), Rat::zero()).unwrap();
    let bank = ReceivingBank::new(
        ResonatorMaterial::new(
            identity.clone(),
            identity,
            ExactRatMatrix::zero(2, 2).unwrap(),
            None,
        )
        .unwrap(),
        [PumpStep::Stand, PumpStep::Half]
            .into_iter()
            .map(|step| PumpDeclaration::new(rat(5, 8), axis.clone(), step).unwrap())
            .collect(),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    let generated =
        generate_by_bank(&field, &theta, &current, &request, &refinement, &bank, 12).unwrap();
    let locked: usize = generated.locks.iter().map(Vec::len).sum();
    assert_eq!(generated.decisions.len(), locked);
    assert_eq!(generated.members, 2 * locked);
    assert_eq!(generated.certified, generated.members);
    assert_eq!(generated.ticks_closed, generated.ticks);
    for (_, _, growth, runner) in &generated.decisions {
        assert!(growth.exceeds(runner) && growth.is_locked());
    }
    if generated.release.released() {
        assert!(generated.release.width.is_zero());
        let mut stations: Vec<usize> = generated.locks.iter().flatten().copied().collect();
        stations.sort_unstable();
        assert_eq!(stations, vec![0, 1, 2, 3]);
        assert_eq!(generated.refinements, generated.locks.len());
    } else {
        assert_eq!(generated.refinements, generated.locks.len() + 1);
        assert!(!generated.release.plural.is_empty());
    }
}

// -------------------------------------------------------------------------------------------
// the bank's learning path

/// The bank of the joint field's tests: one node `C = I`, `K = I`, `Y = 16`, `h = 1`, the members
/// whose period divides the ring's 6 (standing and half-turn), at `p = 5/8`.
fn joint_bank() -> ReceivingBank {
    let identity = ExactRatMatrix::identity(2).unwrap();
    let axis = Carrier::new(Rat::one(), Rat::zero()).unwrap();
    ReceivingBank::new(
        ResonatorMaterial::new(
            identity.clone(),
            identity,
            ExactRatMatrix::zero(2, 2).unwrap(),
            None,
        )
        .unwrap(),
        [PumpStep::Stand, PumpStep::Half]
            .into_iter()
            .map(|step| PumpDeclaration::new(rat(5, 8), axis.clone(), step).unwrap())
            .collect(),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap()
}

/// **The bank's images are its placements' readings** (`prediction::{BankImages, stage_bank}`): at
/// every compared station, the face's normalizer `Σ_x A(x)` and the target's reading `A(t)` read
/// from the images equal the bank chart's reading of `BankPlacement::storage` with that candidate
/// placed and the locked targets beside it, exactly.
#[test]
fn the_banks_images_are_its_placements_readings() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, request) = moment(&field, 92, 7);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let images = BankImages::of(&field, &theta, &refinement, &bank).unwrap();
    let placement = BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
    let chart = bank.chart(6).unwrap();
    let targets = [1usize, 0, 2, 1];
    for locked in [
        [false; 4],
        [true, false, false, false],
        [false, true, false, true],
        [true, true, true, false],
    ] {
        let staged =
            stage_bank(&field, &current, &request, &refinement, &images, &targets, &locked)
                .unwrap();
        assert_eq!(staged.skipped + staged.stations.len(), locked.iter().filter(|l| !**l).count());
        for reading in &staged.stations {
            let read = |class: usize| -> Rat {
                let mut cells: Vec<Option<usize>> = targets
                    .iter()
                    .zip(&locked)
                    .map(|(&t, &l)| l.then_some(t))
                    .collect();
                cells[reading.station] = Some(class);
                chart.of_storage(&placement.storage(reading.station, &cells)).unwrap().reading(&chart)
            };
            let total: Rat = (0..field.alphabet()).map(read).sum();
            assert_eq!(reading.total, total);
            assert_eq!(reading.reading, read(reading.target));
            assert_eq!(reading.mass, &reading.reading / &reading.total);
        }
    }
}

/// **The bank's returns are its score's differential in `E`, within their charged rounding** (module
/// header, "The bank's learning path"): the samples `bank_reach` carries give `G = Σ w g fᵀ` with
/// each reading's covector at its dyadic face `ĉ_x`; for a drawn move `δE` of the source port,
/// `−⟨G, δE⟩` differs from the derivative of the stations' scores
/// `Σ_j (log Σ_x A_j(x) − log A_j(t_j))` along `E + η δE` at `η = 0` by at most
/// `Σ_j e_j Σ_x |A′_j(x)|`, each station's rounding bound times its readings' derivatives, all read
/// exactly (each reading is quadratic in `η`, so its derivative is `(A(1) − A(−1))/2`).
#[test]
fn the_banks_returns_are_its_scores_differential_in_e() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, request) = moment(&field, 93, 9);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let chart = bank.chart(6).unwrap();
    let targets = [2usize, 1, 0, 1];
    let locked = [false, true, false, false];
    let port = theta.source_port(0).unwrap().clone();
    let mut draw = Draw::new(97);
    let direction = draw.matrix(port.rows(), port.columns());
    let moved = |eta: Rat| {
        let moved = port.add(&direction.scaled(&eta)).unwrap();
        theta.clone().with_ports(0, None, Some(moved), None).unwrap()
    };
    let at = |theta: &Constitution| {
        let images = BankImages::of(&field, theta, &refinement, &bank).unwrap();
        stage_bank(&field, &current, &request, &refinement, &images, &targets, &locked).unwrap()
    };
    let (ahead_theta, behind_theta) = (moved(Rat::one()), moved(-Rat::one()));
    let (here, ahead, behind) = (at(&theta), at(&ahead_theta), at(&behind_theta));
    let reading = |theta: &Constitution, station: usize, class: usize| -> Rat {
        let placement =
            BankPlacement::of(&field, theta, &current, &request, &refinement).unwrap();
        let mut cells: Vec<Option<usize>> = targets
            .iter()
            .zip(&locked)
            .map(|(&t, &l)| l.then_some(t))
            .collect();
        cells[station] = Some(class);
        chart.of_storage(&placement.storage(station, &cells)).unwrap().reading(&chart)
    };
    let (mut expected, mut charge) = (Rat::zero(), Rat::zero());
    for ((now, up), down) in here.stations.iter().zip(&ahead.stations).zip(&behind.stations) {
        expected += (&up.total - &down.total) / (integer(2) * &now.total)
            - (&up.reading - &down.reading) / (integer(2) * &now.reading);
        let derivatives: Rat = (0..field.alphabet())
            .map(|class| {
                ((reading(&ahead_theta, now.station, class)
                    - reading(&behind_theta, now.station, class))
                    / integer(2))
                .abs()
            })
            .sum();
        charge += &now.rounding * derivatives;
    }
    let images = BankImages::of(&field, &theta, &refinement, &bank).unwrap();
    let reach = bank_reach(&images, std::slice::from_ref(&here));
    let mut paired = Rat::zero();
    for sample in &reach.samples {
        let moved = direction.apply(&sample.feature).unwrap();
        paired += &sample.weight
            * sample
                .covector
                .iter()
                .zip(&moved)
                .map(|(g, m)| g * m)
                .sum::<Rat>();
    }
    assert!(charge.is_positive());
    assert!((-paired - &expected).abs() <= charge);
}

/// **The bank's deposit is certified and its score falls** (module header, "The bank's learning
/// path"; Lean `HNN/BankFace.{bank_score_endpoint, joint_descends_beside}`): a deposit carrying only
/// the bank's returns at the source port steps `E` by a certified step whose curvature is the
/// bank's (`StepReading::bank > 0`, within the trust scale), and at the successor the product of
/// the stations' target masses `Π θ_t` is strictly larger: every station's score
/// `−log θ_t` falls together.
#[test]
fn the_banks_deposit_is_certified_and_its_score_falls() {
    let field = joint();
    let theta = generic(&field, 91);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests: Vec<(Current, SourceMoment)> = [101u64, 102, 103]
        .into_iter()
        .map(|seed| moment(&field, seed, 8))
        .collect();
    let targets = [[0usize, 1, 2, 1], [2, 2, 0, 1], [1, 0, 0, 2]];
    let locked = [false, true, false, false];
    let masses = |theta: &Constitution| -> (Rat, Vec<crate::hnn::prediction::BankStaged>) {
        let images = BankImages::of(&field, theta, &refinement, &bank).unwrap();
        let staged: Vec<_> = requests
            .iter()
            .zip(&targets)
            .map(|((current, request), targets)| {
                stage_bank(&field, current, request, &refinement, &images, targets, &locked)
                    .unwrap()
            })
            .collect();
        let product = staged
            .iter()
            .flat_map(|s| s.stations.iter().map(|r| r.mass.clone()))
            .product();
        (product, staged)
    };
    let (before, staged) = masses(&theta);
    let images = BankImages::of(&field, &theta, &refinement, &bank).unwrap();
    let reach = bank_reach(&images, &staged);
    let deposit = crate::hnn::port::Deposit::new(
        theta.commit(),
        vec![crate::hnn::constitution::LinearStep {
            locus: crate::hnn::constitution::LinearLocus::SourcePort(0),
            samples: Vec::new(),
        }],
        Vec::new(),
        vec![crate::hnn::constitution::Locus::SourcePort(0)],
    )
    .with_reach(refinement.reach(6))
    .with_bank(reach);
    let (next, reading) = theta.deposited(&deposit).unwrap();
    let (_, step) = reading
        .steps
        .iter()
        .find(|(locus, _)| *locus == crate::hnn::constitution::Locus::SourcePort(0))
        .expect("the source port steps");
    assert!(step.bank.is_positive());
    assert!(step.step.holds());
    let (after, _) = masses(&next);
    assert!(after > before);
}

// -------------------------------------------------------------------------------------------
// the release's own comparison (`hnn::executed`)

/// The joint field's requests at drawn moments, with their targets and context.
fn executed_requests(
    field: &Field,
    cases: &[(u64, [usize; 4])],
    context: crate::hnn::executed::Context,
) -> Vec<crate::hnn::executed::Request> {
    cases
        .iter()
        .map(|&(seed, targets)| {
            let (current, moment) = moment(field, seed, 8);
            crate::hnn::executed::Request {
                current,
                moment,
                targets: targets.to_vec(),
                context: context.clone(),
            }
        })
        .collect()
}

/// **The release's own comparison reads the release** (`hnn::executed::compare`): on an open
/// context its release is `generate_by_bank`'s exactly, every refinement's open stations are
/// compared, each station's class and threshold predicates agree with its target's and leading
/// rival's enclosures, a refinement's lock is safe exactly when every station it locked reads its
/// target, and `F` is the sum of the stations' positive parts.
#[test]
fn the_release_comparison_reads_the_bank_release() {
    use crate::hnn::executed::{Context, Predicate, compare};
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests = executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let batch = compare(&field, &theta, &requests, &refinement, &bank, 12).unwrap();
    let mut total = Rat::zero();
    for (request, compared) in requests.iter().zip(&batch.requests) {
        let generated = generate_by_bank(
            &field,
            &theta,
            &request.current,
            &request.moment,
            &refinement,
            &bank,
            12,
        )
        .unwrap();
        assert_eq!(compared.generation.as_ref(), Some(&generated));
        assert_eq!(compared.orders.len(), generated.refinements);
        for station in &compared.stations {
            let (t, r) = (&station.target_growth, &station.rival_growth);
            assert_eq!(station.class == Predicate::Holds, t.exceeds(r));
            assert_eq!(station.threshold == Predicate::Holds, t.is_locked());
            assert!(station.value.lower <= station.value.upper);
            total += station.value.lower.clone().max(Rat::zero());
        }
        for order in &compared.orders {
            if let Some(safe) = order.safe {
                let right = order
                    .locked
                    .iter()
                    .all(|&s| generated.release.classes[s] == request.targets[s]);
                assert_eq!(safe, right);
            }
        }
    }
    assert_eq!(batch.value.lower, total);
}

/// **The proposal's returns are its pullback to `E`** (`hnn::executed`, "The covector"): for a drawn
/// move `ΔE` of the source port, the returns pair with it as the contributions' storage covectors
/// (at their dyadic faces, with their signs) pair with the storage moves `ΔE` places, exactly:
/// `Σ w ⟨g, ΔE f⟩ = −Σ_c sign_c ⟨ĝ_c, δz_c⟩`, each `δz_c` the section's storage read from the
/// contribution's station with `ΔE` at the source port (the storage is linear in `E` at fixed
/// weights). At a transport of modulus one (every weight `ν̂(n + v)`) and at `3/4`, where each
/// contribution's weights are read from its own station (the station-framed law): the returns keep
/// their form, and some contribution's section holds a placed datum after its station, so a
/// two-sided weight enters the identity.
#[test]
fn the_proposals_returns_are_its_pullback_to_e() {
    use crate::hnn::executed::{Context, Request, proposal_returns};
    let field = joint();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let cases: [(u64, [usize; 4]); 3] = [(95, [0, 1, 2, 1]), (97, [2, 0, 1, 1]), (96, [1, 1, 0, 2])];
    for (modulus, cells) in [(Rat::one(), 8usize), (rat(3, 4), 2)] {
        let theta = generic(&field, 94).with_transport(0, modulus.clone()).unwrap();
        let requests: Vec<Request> = cases
            .iter()
            .map(|&(seed, targets)| {
                let (current, moment) = moment(&field, seed, cells);
                Request {
                    current,
                    moment,
                    targets: targets.to_vec(),
                    context: Context::Open,
                }
            })
            .collect();
        let (samples, contributions) =
            proposal_returns(&field, &theta, &requests, &refinement, &bank, 12).unwrap();
        assert!(!contributions.is_empty());
        if !modulus.is_one() {
            assert!(
                contributions
                    .iter()
                    .any(|(_, station, cells, ..)| cells[*station + 1..].iter().any(Option::is_some)),
                "a contribution reads a placed datum after its station"
            );
        }
        let port = theta.source_port(0).unwrap().clone();
        let direction = Draw::new(98).matrix(port.rows(), port.columns());
        let moved = theta
            .clone()
            .with_ports(0, None, Some(direction.clone()), None)
            .unwrap();
        let mut paired = Rat::zero();
        for sample in &samples {
            let image = direction.apply(&sample.feature).unwrap();
            paired += &sample.weight
                * sample
                    .covector
                    .iter()
                    .zip(&image)
                    .map(|(g, m)| g * m)
                    .sum::<Rat>();
        }
        let mut expected = Rat::zero();
        for (request, station, cells, covector, sign) in &contributions {
            let r = &requests[*request];
            let placement =
                BankPlacement::of(&field, &moved, &r.current, &r.moment, &refinement).unwrap();
            let storage = placement.storage(*station, cells);
            expected -= sign * covector.iter().zip(&storage).map(|(g, z)| g * z).sum::<Rat>();
        }
        assert_eq!(paired, expected, "at modulus {modulus}");
    }
}

/// **The committed move descends the release's comparison, or refuses by type**
/// (`hnn::executed::executed_move`): on two requests along the machine's own trajectory the move
/// is adopted, and its successor reads `F` strictly lower by disjoint enclosures, holds every entry
/// of `E` within the bound, certifies its first order, admits every crossing, certifies every lock
/// and counts one commit; every trial before the adopted one names the guard that refused it.
#[test]
fn the_committed_move_descends_or_refuses_by_type() {
    use crate::hnn::executed::{Context, entry_bound, executed_move};
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests = executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let moved = executed_move(&field, &theta, &requests, &refinement, &bank, 12).unwrap();
    for trial in &moved.trials[..moved.trials.len().saturating_sub(1)] {
        assert!(trial.refusal.is_some());
    }
    match &moved.adopted {
        Some((successor, step)) => {
            let last = moved.trials.last().unwrap();
            assert!(last.refusal.is_none());
            let after = last.after.as_ref().unwrap();
            assert!(after.value.upper < moved.before.value.lower);
            assert!(last.first_order.as_ref().unwrap().upper.is_negative());
            assert!(step.largest <= entry_bound());
            assert_eq!(
                &step.largest,
                &successor
                    .source_port(0)
                    .unwrap()
                    .entries()
                    .iter()
                    .map(|x| x.abs())
                    .max()
                    .unwrap()
            );
            assert!(after
                .requests
                .iter()
                .all(|r| r.generation.as_ref().unwrap().uncertified.is_none()));
            assert_eq!(successor.commit(), theta.commit() + 1);
        }
        None => panic!("the move on this instance is adopted: {:?}", moved.refusal),
    }
}

/// **The committed move carries the transport modulus** (`hnn::executed`, "The committed move";
/// `hnn::moment`, "One passage, its transported weights"): from a transport of modulus `3/4` on
/// requests whose span with the stations fills one turn, the move reads the modulus's slope, and an
/// adopted successor keeps a passive modulus on the source port's lattice (the trial's), lowers the
/// comparison by disjoint enclosures with its first order certified negative on the carried move,
/// and holds every lock's certificate; every earlier trial names its guard.
#[test]
fn the_committed_move_carries_the_transport_modulus() {
    use crate::hnn::executed::{Context, Request, executed_move};
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests: Vec<Request> = [(95u64, [0usize, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]
        .iter()
        .map(|&(seed, targets)| {
            let (current, moment) = moment(&field, seed, 2);
            Request {
                current,
                moment,
                targets: targets.to_vec(),
                context: Context::Open,
            }
        })
        .collect();
    let moved = executed_move(&field, &theta, &requests, &refinement, &bank, 12).unwrap();
    assert!(moved.modulus_slope.is_some() || moved.refusal.is_some());
    for trial in &moved.trials[..moved.trials.len().saturating_sub(1)] {
        assert!(trial.refusal.is_some());
    }
    let Some((successor, _)) = &moved.adopted else {
        panic!("the move on this instance is adopted: {:?}", moved.refusal);
    };
    // The modulus's unit move is its least-squares step `−γ_ρ/G_ρ` (Lean
    // `HNN/ExecutedComparison.modulus_least_squares`), proportional to its slope, and its
    // first-order share `γ_ρΔρ = −γ_ρ²/G_ρ` is negative; the adopted trial carries `ρ + ηΔρ`
    // on the port's lattice, nearest.
    {
        let gamma = moved.modulus_slope.clone().unwrap();
        let curvature = moved.modulus_curvature.clone().unwrap();
        let unit = moved.modulus_unit.clone().unwrap();
        assert!(curvature.is_positive());
        assert!(!gamma.is_zero());
        assert_eq!(unit, -&gamma / &curvature);
        assert!((&gamma * &unit).is_negative());
        let last = moved.trials.last().unwrap();
        let lattice = theta
            .lattice(crate::hnn::constitution::Locus::SourcePort(0))
            .unwrap()
            .unit();
        let target = (rat(3, 4) + &last.step * &unit).max(rat(3, 8)).min(Rat::one());
        let carried = ((&target / &lattice) + rat(1, 2)).floor() * &lattice;
        assert_eq!(last.modulus.as_ref(), Some(&carried));
    }
    {
        let last = moved.trials.last().unwrap();
        assert!(last.refusal.is_none());
        let modulus = successor.transport(0);
        assert!(modulus.is_positive() && modulus <= Rat::one());
        // On this instance the modulus moves with `E`: the comparison falls with a newer
        // frontier (the carried modulus below `3/4`).
        assert_eq!(Some(&modulus), last.modulus.as_ref());
        assert!(modulus < rat(3, 4));
        let after = last.after.as_ref().unwrap();
        assert!(after.value.upper < moved.before.value.lower);
        assert!(last.first_order.as_ref().unwrap().upper.is_negative());
        assert!(after
            .requests
            .iter()
            .all(|r| r.generation.as_ref().unwrap().uncertified.is_none()));
    }
}

/// **The face's move is the same ladder on the face's code** (`hnn::executed::face_move`, the
/// matched control): on partition contexts the face's code at an adopted successor lies strictly
/// below its code at `E` by disjoint enclosures, its first order is negative, and `E`'s entries hold
/// the bound; every earlier trial names its guard.
#[test]
fn the_faces_move_is_the_same_ladder_on_the_faces_code() {
    use crate::hnn::executed::{Context, entry_bound, face_move};
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests = executed_requests(
        &field,
        &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])],
        Context::Partition(vec![false, true, false, false]),
    );
    let moved = face_move(&field, &theta, &requests, &refinement, &bank, 12).unwrap();
    for trial in &moved.trials[..moved.trials.len().saturating_sub(1)] {
        assert!(trial.refusal.is_some());
    }
    let (_, step) = moved.adopted.as_ref().expect("the face's move is adopted here");
    let last = moved.trials.last().unwrap();
    assert!(last.value.as_ref().unwrap().upper < moved.before.value.lower);
    assert!(last.first_order.as_ref().unwrap().upper.is_negative());
    assert!(step.largest <= entry_bound());
}
