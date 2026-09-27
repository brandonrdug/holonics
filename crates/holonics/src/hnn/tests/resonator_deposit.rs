//! Loaded resonator gain deposition, its carrier remainders, complete-candidate certification and
//! receiver-relative release.

use super::learning::{chain, chain_declaration, generic, phases};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::{Carrier, Constitution, FactorGradient, FactorStep, Locus, Steps};
use crate::hnn::field::{Current, Field};
use crate::hnn::port::{Deposit, ExecutionPort, Handle};
use crate::hnn::reference::{Reference, one_hot};
use crate::hnn::retention::{collapse, loci, retained};
use crate::hnn::ring::{
    PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands, ResonatorRemainders,
};
use crate::hnn::word::{EndChange, PowerForm};
use crate::holon::parametron::Carrier as PumpAxis;
use crate::ratio::exponentiated::RatioError;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

fn material(field: &Field, ring: usize) -> ResonatorMaterial {
    let width = field.ring(ring).width();
    ResonatorMaterial::new(
        ExactRatMatrix::identity(width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        None,
    )
    .unwrap()
}

fn declared(field: &Field, seed: u64) -> Constitution {
    let theta = generic(field, seed);
    theta
        .with_ring_resonator(field, 0, material(field, 0))
        .unwrap()
}

fn one_gain_step(ring: usize, family: usize, gradient: Rat, energy: Rat) -> Deposit {
    Deposit::new(
        0,
        Vec::new(),
        vec![FactorStep {
            gradient: FactorGradient::Resonator {
                ring,
                family,
                gradient,
            },
            energy,
        }],
        vec![Locus::Resonator(ring)],
    )
}

#[test]
fn a_reached_capacity_gain_changes_the_next_word_local_solve() {
    let field = chain();
    let theta = declared(&field, 301);
    let base = theta.resonator(0).unwrap().clone();
    let (next, reading) = theta
        .deposited(&one_gain_step(0, 0, Rat::one(), Rat::one()))
        .unwrap();
    assert_eq!(reading.contact_growth, Some(Rat::zero()));
    let learned = next.resonator(0).unwrap();
    assert_eq!(learned.gains()[0], rat(5, 4));

    let width = field.ring(0).width();
    let quiet = vec![Rat::zero(); width];
    let mut drive = vec![Rat::zero(); width];
    drive[0] = Rat::one();
    let solve = |material: &ResonatorMaterial| {
        ResonatorOperands::at_cut(0, material, field.ring(0).admittance(), field.step(), None)
            .unwrap()
            .step(
                0,
                &drive,
                [&quiet, &quiet],
                &ResonatorRemainders::default(),
                None,
            )
            .unwrap()
    };
    let before = solve(&base);
    let after = solve(learned);
    assert_ne!(before.rate, after.rate);
    assert_ne!(before.output, after.output);

    let zero_waves: Vec<Vec<Rat>> = field
        .rings()
        .iter()
        .map(|ring| vec![Rat::zero(); ring.width()])
        .collect();
    let arrivals = field
        .contacts()
        .iter()
        .map(|contact| {
            let (from, to) = contact.ends();
            [
                vec![Rat::zero(); field.ring(from).width()],
                vec![Rat::zero(); field.ring(to).width()],
            ]
        })
        .collect();
    let states = field
        .contacts()
        .iter()
        .map(|contact| {
            [
                vec![Rat::zero(); contact.width()],
                vec![Rat::zero(); contact.width()],
            ]
        })
        .collect();
    let resonators = (0..field.rings().len())
        .map(|ring| (ring == 0).then(|| [after.state[0].clone(), after.state[1].clone()]))
        .collect();
    let phases = (0..field.rings().len())
        .map(|ring| (ring == 0).then_some(after.phase))
        .collect();
    let change = EndChange {
        storage: zero_waves,
        arrivals,
        states,
        resonators,
        resonator_phases: phases,
    };
    let current = Current::at_rest(&field);
    let before_form = PowerForm::read(&field, &theta, &current).unwrap();
    let after_form = PowerForm::read(&field, &next, &current).unwrap();
    let end_work = before_form.deposition_work(&after_form, &change).unwrap();
    let resonator_work = learned
        .energy(after.phase, &after.state[0], &after.state[1])
        .unwrap()
        - base
            .energy(after.phase, &after.state[0], &after.state[1])
            .unwrap();
    assert_ne!(end_work, Rat::zero());
    assert_eq!(end_work, resonator_work);
}

#[test]
fn all_gain_families_are_certified_as_one_atomic_candidate() {
    let field = chain();
    let width = field.ring(0).width();
    let base = ResonatorMaterial::new(
        ExactRatMatrix::identity(width).unwrap(),
        ExactRatMatrix::identity(width)
            .unwrap()
            .scaled(&integer(-1)),
        ExactRatMatrix::identity(width).unwrap().scaled(&rat(1, 10)),
        None,
    )
    .unwrap();
    let theta = generic(&field, 302)
        .with_ring_resonator(&field, 0, base)
        .unwrap();
    // The capacity-only intermediate has certificate 0.1−0.5 < 0. Raising the dissipation
    // amplitude in the same comparison makes the complete successor 0.9−0.5 > 0.
    let deposit = Deposit::new(
        0,
        Vec::new(),
        vec![
            FactorStep {
                gradient: FactorGradient::Resonator {
                    ring: 0,
                    family: 0,
                    gradient: integer(-2),
                },
                energy: Rat::zero(),
            },
            FactorStep {
                gradient: FactorGradient::Resonator {
                    ring: 0,
                    family: 2,
                    gradient: integer(4),
                },
                energy: Rat::zero(),
            },
        ],
        vec![Locus::Resonator(0)],
    );
    let (next, _) = theta.deposited(&deposit).unwrap();
    assert_eq!(
        next.resonator(0).unwrap().gains(),
        &[Rat::zero(), Rat::one(), integer(3), Rat::one()]
    );
}

#[test]
fn an_uncertified_pump_gain_refuses_without_publishing_any_part_of_the_candidate() {
    let field = chain();
    let width = field.ring(0).width();
    let pump =
        PumpDeclaration::new(Rat::one(), PumpAxis::at(&Rat::zero()), PumpStep::Half).unwrap();
    let material = ResonatorMaterial::new(
        ExactRatMatrix::identity(width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        Some(pump),
    )
    .unwrap();
    let theta = generic(&field, 303)
        .with_ring_resonator(&field, 0, material)
        .unwrap();
    let before_bits = theta.exact_bits();
    let error = theta
        .deposited(&one_gain_step(0, 3, integer(2), Rat::zero()))
        .unwrap_err();
    assert!(matches!(
        error,
        HnnError::UncertifiedResonator { ring: 0, phase: 0 }
    ));
    assert_eq!(theta.commit(), 0);
    assert_eq!(theta.exact_bits(), before_bits);
    assert!(
        theta
            .resonator(0)
            .unwrap()
            .gains()
            .iter()
            .all(|gain| gain == &Rat::one())
    );
}

#[test]
fn gain_and_scale_remainders_are_carried_counted_and_read_exactly() {
    let field = chain();
    let theta = declared(&field, 304);
    let before = theta
        .carrier_bits_by_locus()
        .into_iter()
        .find(|(locus, _)| *locus == Locus::Resonator(0))
        .unwrap()
        .1;
    let (next, reading) = theta
        .deposited(&one_gain_step(0, 0, rat(1, 3), Rat::one()))
        .unwrap();
    assert!(next.on_lattice());
    let after = next
        .carrier_bits_by_locus()
        .into_iter()
        .find(|(locus, _)| *locus == Locus::Resonator(0))
        .unwrap()
        .1;
    assert!(after.entries > before.entries);
    assert!(after.remainders > 0);
    assert!(
        next.carried_remainders()
            .iter()
            .any(|(locus, carrier, _, _)| {
                *locus == Locus::Resonator(0) && *carrier == Carrier::Resonator(0)
            })
    );
    let exact = next.with_remainders().unwrap();
    let released = reading
        .released
        .iter()
        .filter(|(locus, carrier, _, _)| {
            *locus == Locus::Resonator(0) && *carrier == Carrier::Resonator(0)
        })
        .map(|(.., value)| value.clone())
        .sum::<Rat>();
    let carried = next
        .carried_remainders()
        .into_iter()
        .filter(|(locus, carrier, _, _)| {
            *locus == Locus::Resonator(0) && *carrier == Carrier::Resonator(0)
        })
        .map(|(.., value)| value)
        .sum::<Rat>();
    assert_eq!(
        &exact.resonator(0).unwrap().gains()[0] + &released,
        rat(13, 12)
    );
    assert_eq!(
        &next.resonator(0).unwrap().gains()[0] + &carried + &released,
        rat(13, 12)
    );
}

#[test]
fn resonator_release_follows_the_ring_diamond_and_ignores_empty_slots() {
    let mut field_for_empty = None;
    let mut admitted_for_empty = Vec::new();
    for aperture in [1, 2] {
        let mut declaration = chain_declaration(1 << 16);
        declaration.receivers[0].aperture = aperture;
        let field = Field::declare(declaration).unwrap();
        let mut theta = generic(&field, 305 + aperture as u64);
        for ring in 0..field.rings().len() {
            theta = theta
                .with_ring_resonator(&field, ring, material(&field, ring))
                .unwrap();
        }
        let current = Current::at_rest(&field);
        let admitted = [phases(&field, &theta, &current)];
        let kept = retained(&field, &admitted);
        for ring in 0..field.rings().len() {
            assert_eq!(
                kept.contains(&Locus::Resonator(ring)),
                kept.contains(&Locus::Element(ring))
            );
        }
        let reading = collapse(&field, &mut theta, &admitted).unwrap();
        for ring in 0..field.rings().len() {
            assert_eq!(
                theta.resonator(ring).is_some(),
                kept.contains(&Locus::Resonator(ring))
            );
        }
        assert_eq!(
            reading
                .released
                .iter()
                .any(|locus| *locus == Locus::Resonator(0)),
            !kept.contains(&Locus::Resonator(0))
        );
        if aperture == 1 {
            field_for_empty = Some(field);
            admitted_for_empty = admitted.to_vec();
        }
    }

    let field = field_for_empty.unwrap();
    let mut empty = generic(&field, 306);
    let reading = collapse(&field, &mut empty, &admitted_for_empty).unwrap();
    assert!(
        !reading
            .released
            .iter()
            .any(|locus| matches!(locus, Locus::Resonator(_)))
    );
    let structural_entries: usize = loci(&field)
        .into_iter()
        .filter(|locus| !matches!(locus, Locus::Resonator(_)))
        .map(|locus| locus.entries(&field))
        .sum();
    assert_eq!(reading.total_entries, structural_entries);
}

#[test]
fn an_out_of_range_gain_family_is_a_typed_refusal() {
    let field = chain();
    let theta = declared(&field, 307);
    let error = theta
        .deposited(&one_gain_step(0, 4, Rat::one(), Rat::one()))
        .unwrap_err();
    assert!(matches!(error, HnnError::Resonator { ring: 0, .. }));
}

#[test]
fn a_late_reread_refusal_keeps_the_staged_deposit_and_all_published_state() {
    let field = chain();
    // This coefficient has only 129 bits. It grows a tiny map into an exponent which the next
    // receiver read cannot carry into a machine-word shift; power_of_two checks that bound before
    // allocating the shifted integer. The lattice successor itself remains far below u64::MAX.
    let proxy = Rat::from_integer(BigInt::one() << 128usize);
    let steps = Steps {
        proxy,
        factor: Rat::zero(),
    };
    let constitution = Constitution::initial(&field, steps.clone(), u64::MAX).unwrap();
    let reference = Reference::new(64, steps, u64::MAX);
    let current = Current::at_rest(&field);
    let mut resident = reference
        .mount_with(&field, &current, constitution)
        .unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[0]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (staged, _) = reference
        .compare(&mut resident, pending, &one_hot(&[0, 1]))
        .unwrap();

    let constitution_before = resident.constitution().clone();
    let current_before = resident.current().clone();
    let charts_before = resident.charts().clone();
    let ledger_before = resident.ledger().clone();
    let state_bits_before = resident.state_bits();
    let handles_before = reference.read(&resident).unwrap().2;

    let refusal = reference.deposit(&mut resident, staged).unwrap_err();
    assert!(matches!(
        refusal,
        HnnError::Ratio(RatioError::CarryTooWide { .. })
    ));
    assert!(resident.stopped().is_none());
    assert_eq!(resident.constitution(), &constitution_before);
    assert_eq!(resident.current(), &current_before);
    assert_eq!(resident.charts(), &charts_before);
    assert_eq!(resident.ledger(), &ledger_before);
    assert_eq!(resident.state_bits(), state_bits_before);
    let handles_after = reference.read(&resident).unwrap().2;
    assert_eq!(handles_after, handles_before);
    assert!(
        handles_after
            .iter()
            .any(|(handle, _)| *handle == Handle::Staged(staged))
    );
}
