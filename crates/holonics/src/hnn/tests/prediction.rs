//! Native generation (`hnn::prediction`): the continuing word, the refinement's balance, the
//! section return's exact pairing, the release at width zero, the loci a deposit does not reach,
//! and the path's reading of no landmark tree.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::{OPEN_BUDGET, chain, generic, moment, six_path};
use super::support::Draw;
use crate::compression::landmark::context::Landmarks;
use crate::hnn::chart::Charts;
use crate::hnn::constitution::{Constitution, Steps};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::{PairPort, SourceMoment};
use crate::hnn::prediction::{
    Latent, Refinement, Section, deposit_of, stage, unreached_unchanged,
};
use crate::hnn::propagation::Operands;
use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
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
    let (current, moment) = moment(&field, 76, 9);
    let refinement = declared(&field, 3, 2);
    let section = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        Latent::Rest,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    let mut balance = section.balance().clone();
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
        &mut Charts::new(),
        false,
    )
    .unwrap();
    let deposit = deposit_of(&theta, std::slice::from_ref(&staged.composed)).unwrap();
    let (next, _) = theta.deposited(&deposit).unwrap();
    let before = crate::hnn::word::PowerForm::read(&field, &theta, &current).unwrap();
    let after = crate::hnn::word::PowerForm::read(&field, &next, &current).unwrap();
    balance.commit(&before, &after, section.end()).unwrap();
    assert!(balance.commit.is_some());
    assert!(balance.closes(), "{balance:?}");
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
    let initial = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let plural = Section::refine(
        &field,
        &initial,
        &current,
        &moment,
        Latent::Rest,
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
        Latent::Rest,
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
        &mut Charts::new(),
        false,
    )
    .unwrap();
    let deposit = deposit_of(&theta, std::slice::from_ref(&staged.composed)).unwrap();
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
        Latent::Rest,
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
        Latent::Rest,
        &refinement,
        &mut Charts::new(),
    )
    .unwrap()
    .faces()
    .clone();
    assert_eq!(plain, guarded);
}

/// A keyed latent is a member of the joint family: it opens the receiving ring at one lattice unit
/// a coordinate, and every station is read from its one anchor.
#[test]
fn a_keyed_latent_moves_the_whole_section_from_one_anchor() {
    let field = chain();
    let theta = generic(&field, 85);
    let (current, moment) = moment(&field, 86, 6);
    let refinement = declared(&field, 2, 1);
    let unit = field.word_lattice().unwrap().transient().unit();
    let latent = Latent::Keyed(3).storage(&field, refinement.ring());
    assert!(latent[refinement.ring()].iter().all(|x| x == &unit || x == &-unit.clone()));
    let section = Section::refine(
        &field,
        &theta,
        &current,
        &moment,
        Latent::Keyed(3),
        &refinement,
        &mut Charts::new(),
    )
    .unwrap();
    let ring = field.ring(refinement.ring());
    for (j, read) in section.reads().iter().enumerate() {
        assert_eq!(
            read,
            &ring.rotate(section.anchor(), &BigInt::from(j as u64 + 1))
        );
    }
}
