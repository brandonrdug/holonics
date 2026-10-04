//! Loaded resonator gain deposition, its carrier remainders, complete-candidate certification and
//! receiver-relative release.

use super::learning::{chain, chain_declaration, chain_reach, generic, phases};

use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::{
    Carrier, Constitution, FactorGradient, FactorStep, GainBacktrack, Locus,
};
use crate::hnn::field::{Current, Field};
use crate::hnn::port::{Deposit, ExecutionPort, Handle};
use crate::hnn::reference::{Reference, one_hot};
use crate::hnn::retention::{Opens, collapse, loci, retained};
use crate::hnn::ring::{
    PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands, ResonatorRemainders,
};
use crate::hnn::word::{EndChange, PowerForm};
use crate::holon::parametron::Carrier as PumpAxis;
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

/// **A generic constitution whose receiving map is zero**, so no gain reaches the stations and a
/// gain family's certified step is the covector bound's (`hnn::constitution`, "The factor families'
/// certified step"): at the covector scale [`COVECTOR`] it is `η = ½`, the step these laws of the
/// carry, the backtrack and the candidate's certification read.
fn silent(field: &Field, seed: u64) -> Constitution {
    let receiver = field.receivers()[0].ring;
    let width = field.ring(receiver).width();
    generic(field, seed)
        .with_ports(
            receiver,
            None,
            None,
            Some(ExactRatMatrix::zero(2 * field.alphabet(), width).unwrap()),
        )
        .unwrap()
}

/// The covector scale `c = 2` of the fixtures' gain steps: the certified step `η = 2^⌊log₂(1/c)⌋ = ½`
/// where no gain reaches the stations.
const COVECTOR: i64 = 2;

fn declared(field: &Field, seed: u64) -> Constitution {
    silent(field, seed)
        .with_ring_resonator(field, 0, material(field, 0))
        .unwrap()
}

fn gain_step(ring: usize, family: usize, gradient: Rat, energy: Rat) -> FactorStep {
    FactorStep {
        gradient: FactorGradient::Resonator {
            ring,
            family,
            gradient,
        },
        energy,
        covector: integer(COVECTOR),
    }
}

fn gain_deposit(commit: u64, ring: usize, steps: Vec<FactorStep>) -> Deposit {
    Deposit::new(commit, Vec::new(), steps, vec![Locus::Resonator(ring)]).with_reach(chain_reach())
}

fn one_gain_step(ring: usize, family: usize, gradient: Rat, energy: Rat) -> Deposit {
    gain_deposit(0, ring, vec![gain_step(ring, family, gradient, energy)])
}

#[test]
fn a_reached_capacity_gain_changes_the_next_word_local_solve() {
    let field = chain();
    let theta = declared(&field, 301);
    let base = theta.resonator(0).unwrap().clone();
    let (next, reading) = theta
        .deposited(&one_gain_step(0, 0, Rat::one(), Rat::one()))
        .unwrap();
    assert!(reading.storage_growth >= Rat::from_integer(0.into()));
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
    let theta = silent(&field, 302)
        .with_ring_resonator(&field, 0, base)
        .unwrap();
    // At `h = 1` the certificate is `2g_C² + g_D²/10 − 1/2`. The capacity step alone carries
    // `g_C` from 1 to 1/4, whose intermediate reads `1/8 + 1/10 − 1/2 = −11/40 < 0`. Raising the
    // dissipation amplitude to 3 in the same comparison makes the complete successor
    // `1/8 + 9/10 − 1/2 = 21/40 > 0`, and the candidate is certified once, whole.
    let deposit = gain_deposit(
        0,
        0,
        vec![
            gain_step(0, 0, rat(-3, 2), Rat::zero()),
            gain_step(0, 2, integer(4), Rat::zero()),
        ],
    );
    let (next, reading) = theta.deposited(&deposit).unwrap();
    assert_eq!(
        next.resonator(0).unwrap().gains(),
        &[rat(1, 4), Rat::one(), integer(3), Rat::one()]
    );
    assert!(reading.backtracks.is_empty());
}

/// **A gain never releases by deposition** (`hnn::constitution::GainBacktrack`): a step that would
/// carry an amplitude to `g ≤ 0` backtracks to the midpoint of the admissible side, `g/2`, on the
/// locus's lattice, and the deposit's reading names the substitution. At the lattice's first point
/// the midpoint rounds back to the gain itself (ties upward), so the amplitude stays positive.
#[test]
fn a_step_past_zero_backtracks_to_the_midpoint_and_is_named() {
    let field = chain();
    let theta = declared(&field, 308);
    // The capacity step −1 (gradient −2 at rate 1/2) reaches exactly zero; −2 goes past it.
    for (gradient, candidate) in [(integer(-2), Rat::zero()), (integer(-4), integer(-1))] {
        let (next, reading) = theta
            .deposited(&one_gain_step(0, 0, gradient, Rat::zero()))
            .unwrap();
        assert_eq!(next.resonator(0).unwrap().gains()[0], rat(1, 2));
        assert!(next.on_lattice());
        assert_eq!(
            reading.backtracks,
            vec![GainBacktrack {
                ring: 0,
                family: 0,
                from: Rat::one(),
                candidate,
                to: rat(1, 2),
            }]
        );
    }
    // Repeated backtracks halve the amplitude down to the lattice's first point and hold there.
    let unit = theta.lattice(Locus::Resonator(0)).unwrap().unit();
    let mut current = theta;
    let mut gain = Rat::one();
    while gain > unit {
        let (next, reading) = current
            .deposited(&gain_deposit(
                current.commit(),
                0,
                vec![gain_step(0, 0, integer(-4), Rat::zero())],
            ))
            .unwrap();
        assert_eq!(reading.backtracks.len(), 1);
        let halved = next.resonator(0).unwrap().gains()[0].clone();
        assert_eq!(halved, &gain * rat(1, 2));
        gain = halved;
        current = next;
    }
    let (held, reading) = current
        .deposited(&gain_deposit(
            current.commit(),
            0,
            vec![gain_step(0, 0, integer(-4), Rat::zero())],
        ))
        .unwrap();
    assert_eq!(held.resonator(0).unwrap().gains()[0], unit);
    assert_eq!(reading.backtracks[0].to, unit);
    // The material owner refuses a nonpositive amplitude outright.
    let material = held.resonator(0).unwrap();
    let mut zeroed = material.gains().clone();
    zeroed[0] = Rat::zero();
    assert!(matches!(
        material.with_gains(zeroed),
        Err(HnnError::Resonator { .. })
    ));
}

/// **A pumped ring's own gains are held and named** (`hnn::constitution`, "The pumped medium's
/// reach"): the ring's reach is read by its Floquet bound, but a step of its own gains moves its
/// monodromy along the ray, which no certified reach covers, and its pumped stiffness has no
/// certified storage growth at the commit; so the family is held (nothing of it moves), the deposit
/// is published, and its reading names the ring's reach and the held family.
#[test]
fn a_pumped_rings_own_gain_is_held_and_named() {
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
    let theta = silent(&field, 303)
        .with_ring_resonator(&field, 0, material)
        .unwrap();
    let (next, reading) = theta
        .deposited(&one_gain_step(0, 3, integer(2), Rat::zero()))
        .unwrap();
    assert_eq!(next.commit(), 1);
    assert!(reading.steps.is_empty());
    let pumped = reading.pumped.expect("the pumped ring's reach is read");
    assert_eq!(pumped.rings.len(), 1);
    assert_eq!(pumped.rings[0].ring, 0);
    assert_eq!(
        pumped.held,
        vec![(
            Locus::Resonator(0),
            crate::hnn::constitution::Family::Resonator(3)
        )]
    );
    assert_eq!(
        next.resonator(0).unwrap().gains(),
        theta.resonator(0).unwrap().gains()
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
        let kept = retained(&field, &admitted, Opens::AtRest);
        for ring in 0..field.rings().len() {
            assert_eq!(
                kept.contains(&Locus::Resonator(ring)),
                kept.contains(&Locus::Element(ring))
            );
        }
        let reading = collapse(&field, &mut theta, &admitted, Opens::AtRest).unwrap();
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
    let reading = collapse(&field, &mut empty, &admitted_for_empty, Opens::AtRest).unwrap();
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

/// **A deposit the constitution refuses keeps the staged deposit and all published state**
/// (`hnn::constitution`, "The certified step"): contact 0 declares a certified boost, whose signed
/// stiffness stores indefinite energy, so no step's gain is certified through it and the constitution
/// refuses every deposit that moves a family (`ActiveContact`); the port publishes nothing of it.
/// [historical] The refusal was the committed energy bound's, forced by a 129-bit declared factor
/// step, until the factor families' step was certified (September 29); a storage grown outside its
/// range is refused at the constitution (`tests::constitution`,
/// `a_storage_growth_outside_its_range_is_refused`).
#[test]
fn a_refused_deposit_keeps_the_staged_deposit_and_all_published_state() {
    let field = chain();
    let k = field.contact(0).width();
    let constitution = Constitution::initial(&field, u64::MAX)
        .unwrap()
        .with_contact_signature(&field, 0, (0..k).map(|j| j != 0).collect())
        .unwrap();
    let reference = Reference::new(64, u64::MAX);
    let current = Current::at_rest(&field);
    let mut resident = reference
        .mount_with(&field, &current, constitution)
        .unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[0]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (staged, compared) = reference
        .compare(&mut resident, pending, &one_hot(&[0, 1]))
        .unwrap();
    let deposit = compared.deposit.into_present().unwrap();

    let constitution_before = resident.constitution().clone();
    let current_before = resident.current().clone();
    let charts_before = resident.charts().clone();
    let ledger_before = resident.ledger().clone();
    let state_bits_before = resident.state_bits();
    let handles_before = reference.read(&resident).unwrap().2;

    let refusal = reference.deposit(&mut resident, staged).unwrap_err();
    assert_eq!(refusal, HnnError::ActiveContact { contact: 0 });
    assert_eq!(
        constitution_before.deposited(&deposit),
        Err(HnnError::ActiveContact { contact: 0 })
    );
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
