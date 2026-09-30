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
    injection, stage, stage_bank,
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
        &[&moment],
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
        &[&moment],
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
        &[&moment],
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
        &[&moment],
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
        &[&moment],
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
        &[&moment],
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
        &[&moment],
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

/// **A placed datum is read at its station's residue** (`SourceMoment::section`): the datum locked
/// at station `j` is counted at the receiving ring's residue `τ + 1 + j`, and station `j`'s rotation
/// `P^(1+j)` of its open storage is the datum's column of `E` over its population, `E e_x ν̂(1)`.
#[test]
fn a_placed_datum_is_read_at_its_station_residue() {
    let field = joint();
    let theta = generic(&field, 91);
    let (current, _) = moment(&field, 92, 7);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let phase = current.phase(&field, 0).unwrap() as usize;
    let nu = crate::hnn::moment::PopulationChart::of(&field).value(1);
    let port = theta.source_port(0).unwrap();
    for station in 0..4 {
        for code in 0..field.alphabet() {
            let mut cells = vec![None; 4];
            cells[station] = Some(code);
            let placed = refinement.section(&field, &current, &cells).unwrap();
            assert_eq!(placed.cells(), 1);
            assert_eq!(
                placed.phase_counts(0, (phase + 1 + station) % 6).unwrap()[code],
                1
            );
            let open = placed.open_storage(&field, &theta, &current).unwrap();
            let read = field
                .ring(0)
                .rotate(&open[0], &BigInt::from(station as u64 + 1));
            let column: Vec<Rat> = (0..field.ring(0).width())
                .map(|row| port.get(row, code).unwrap() * &nu)
                .collect();
            assert_eq!(read, column);
        }
    }
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
        let placed = refinement.section(&field, &current, &cells).unwrap();
        Section::refine(
            &field,
            &theta,
            &current,
            &[&moment, &placed],
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
        &[&moment],
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

/// **The bank's placement is the section's injection** (`prediction::BankPlacement`): the receiving
/// ring's storage with any set of stations placed equals `injection` of the request's moment and the
/// section's `SourceMoment::section`, exactly, and with nothing placed it is the request's own.
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
        let section = refinement.section(&field, &current, cells).unwrap();
        let injected = injection(&field, &theta, &current, &[&request, &section]).unwrap();
        assert_eq!(placement.storage(cells), injected[0]);
    }
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
                chart.of_storage(&placement.storage(&cells)).unwrap().reading(&chart)
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
        chart.of_storage(&placement.storage(&cells)).unwrap().reading(&chart)
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
