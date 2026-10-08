//! Exact action-law controls. These physical fixtures are not acquired task solutions.

use std::sync::Arc;

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::receiving::ReceivingPhases;
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::word::action::{ControlFibre, PortPreparation};
use holonics::hnn::{
    Absorption, Constitution, Current, Field, FieldDeclaration, RingDeclaration, SourceMoment,
    Word, WordOpening,
};
use holonics::holon::parametron::Carrier;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, integer, rat};
use num_bigint::BigInt;
use num_traits::{One, Zero};

fn fixture() -> (Field, Constitution, Current) {
    let ring = |source| RingDeclaration {
        period: 2,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..2)
            .map(|node| FieldDeclaration::quarter_turn(node, 2))
            .collect(),
        lock: if source { vec![0, 1] } else { Vec::new() },
        reflector: vec![0, 1],
        admittance: integer(2),
        initial: 0,
    };
    let field = Field::declare(
        FieldDeclaration {
            rings: vec![ring(true), ring(false)],
            contacts: vec![ContactDeclaration {
                from: 0,
                to: 1,
                channel: vec![(0, 0), (1, 1)],
                admittance: integer(2),
                exponent: integer(0),
            }],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 2,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 1,
                aperture: 2,
                tolerance: rat(1, 16),
                depth: 2,
                prior: StopPrior::half(),
                mass: 1,
                base: BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap();
    let mut theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ports(1, None, None, Some(ExactRatMatrix::identity(4).unwrap()))
        .unwrap();
    for g in 0..2 {
        let material = ResonatorMaterial::new(
            ExactRatMatrix::identity(4).unwrap(),
            ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
            ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 16)),
            Some(
                PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap(),
            ),
        )
        .unwrap();
        theta = theta.with_ring_resonator(&field, g, material).unwrap();
    }
    let current = Current::at(&field, vec![BigInt::from(0), BigInt::from(1)]).unwrap();
    (field, theta, current)
}

fn moment(field: &Field, current: &Current) -> Arc<SourceMoment> {
    Arc::new(
        SourceMoment::open(field, current)
            .continued(field, current, 0, &[Some(0), Some(1)])
            .unwrap(),
    )
}

fn open<'f>(
    field: &'f Field,
    theta: &Constitution,
    current: &Current,
    opening: &WordOpening,
) -> Word<'f> {
    Word::open_source_exact_received(field, theta, current, moment(field, current), opening)
        .unwrap()
        .0
}

fn reads(
    word: &Word<'_>,
    field: &Field,
    theta: &Constitution,
    current: &Current,
    phases: &ReceivingPhases,
) -> Vec<Vec<Rat>> {
    phases
        .epochs()
        .map(|k| {
            phases
                .read(
                    field,
                    theta,
                    current,
                    word.anchor(k, phases.ring()).unwrap(),
                )
                .unwrap()
                .logits
        })
        .collect()
}

/// An independent actual forward perturbation supplies this law control's target.
/// The action owner computes its response by the producing reverse law instead.
fn perturbed_target(
    word: &Word<'_>,
    theta: &Constitution,
    current: &Current,
    phases: &ReceivingPhases,
    added: &[Rat],
) -> Vec<Vec<Rat>> {
    let field = word.field();
    let mut injection: Vec<Vec<Rat>> = field
        .rings()
        .iter()
        .map(|r| vec![Rat::zero(); r.width()])
        .collect();
    injection[0] = added.to_vec();
    let mut actual = Word::continuing(
        field,
        word.operands().clone(),
        &word.change().unwrap(),
        &injection,
        word.opened_at(),
    )
    .unwrap();
    actual.run(phases.junction_steps()).unwrap();
    assert!(actual.field_balances().iter().all(|b| b.closes()));
    reads(&actual, field, theta, current, phases)
}

#[test]
fn a_unique_preparation_uses_the_full_loaded_opening_and_actual_pump_clock() {
    let (field, theta, current) = fixture();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let mut prior = open(&field, &theta, &current, &WordOpening::Rest);
    prior.run(3).unwrap();
    let opening = WordOpening::Received {
        carry: prior.reception_end().unwrap(),
        absorption: Absorption::Nothing,
    };
    let baseline = open(&field, &theta, &current, &opening);
    assert_eq!(baseline.opened_at(), 3);
    let before = baseline.change().unwrap();
    assert!(
        before
            .resonators
            .iter()
            .flatten()
            .flatten()
            .flatten()
            .any(|x| !x.is_zero())
    );
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let control = vec![rat(1, 4), rat(-1, 8), rat(1, 16), rat(1, 32)];
    let mut target = perturbed_target(&baseline, &theta, &current, &phases, &control);
    // The unused station is an unconstrained receiving face, not a zero target.
    target[0] = vec![Rat::zero(); 4];
    let prospect = baseline
        .prospective_port_preparation(&phases, &preparation, &target, &[false, true])
        .unwrap();
    assert_eq!(prospect.unique_control(), Some(control.as_slice()));
    assert_eq!(baseline.change().unwrap(), before);
    let (mut actual, receipt, applied) = prospect.prepare(baseline).unwrap();
    let after = actual.change().unwrap();
    assert_eq!(after.arrivals, before.arrivals);
    assert_eq!(after.states, before.states);
    assert_eq!(after.resonators, before.resonators);
    assert_eq!(after.resonator_phases, before.resonator_phases);
    assert_eq!(after.storage[1], before.storage[1]);
    let cross: Rat = before.storage[0]
        .iter()
        .zip(&control)
        .map(|(a, b)| a * b)
        .sum();
    let quadratic: Rat = control.iter().map(|x| x * x).sum();
    // h=1,Y=2 here: hY/2=1 and hY/4=1/2, independent of the owner's work calculation.
    assert_eq!(receipt.cross, cross);
    assert_eq!(receipt.quadratic, quadratic / integer(2));
    assert!(receipt.closes());
    actual.run(phases.junction_steps()).unwrap();
    applied.verify_execution(&actual).unwrap();
    assert!(actual.field_balances().iter().all(|b| b.closes()));
}

#[test]
fn a_plural_preimage_keeps_its_kernel_and_an_unreachable_request_returns_its_obstruction() {
    let (field, theta, current) = fixture();
    let partial = ExactRatMatrix::new(vec![
        vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::one(), Rat::zero(), Rat::zero()],
        vec![Rat::zero(); 4],
        vec![Rat::zero(); 4],
    ])
    .unwrap();
    let theta = theta.with_ports(1, None, None, Some(partial)).unwrap();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let baseline = open(&field, &theta, &current, &WordOpening::Rest);
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let target = perturbed_target(&baseline, &theta, &current, &phases, &vec![rat(1, 4); 4]);
    let prospect = baseline
        .prospective_port_preparation(&phases, &preparation, &target, &[false, true])
        .unwrap();
    match prospect.fibre() {
        ControlFibre::Affine { particular, kernel } => {
            assert_eq!(kernel.len(), 2);
            assert_eq!(
                prospect.response().apply(particular).unwrap(),
                prospect.residual()
            );
            for k in kernel {
                assert!(
                    prospect
                        .response()
                        .apply(k)
                        .unwrap()
                        .iter()
                        .all(Zero::is_zero)
                );
            }
        }
        _ => panic!("the reachable request retains its whole plural control fibre"),
    }
    assert!(prospect.unique_control().is_none());
    assert!(prospect.prepare(baseline).is_err());

    let baseline = open(&field, &theta, &current, &WordOpening::Rest);
    let zero = PortPreparation::new(&field, 0, ExactRatMatrix::zero(4, 1).unwrap()).unwrap();
    let mut target = perturbed_target(&baseline, &theta, &current, &phases, &vec![Rat::zero(); 4]);
    target[1][0] += Rat::one();
    let prospect = baseline
        .prospective_port_preparation(&phases, &zero, &target, &[false, true])
        .unwrap();
    match prospect.fibre() {
        ControlFibre::Obstructed { covector, pairing } => {
            assert!(!pairing.is_zero());
            assert!(
                prospect
                    .response()
                    .apply_transpose(covector)
                    .unwrap()
                    .iter()
                    .all(Zero::is_zero)
            );
        }
        _ => panic!("a missing actuator cannot realize the requested carrier residual"),
    }
    assert!(prospect.prepare(baseline).is_err());
}

#[test]
fn the_current_receiving_material_changes_the_prospect_and_stale_producing_words_refuse() {
    let (field, theta, current) = fixture();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let baseline = open(&field, &theta, &current, &WordOpening::Rest);
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let target = perturbed_target(&baseline, &theta, &current, &phases, &vec![rat(1, 4); 4]);
    assert!(target[1].iter().any(|x| !x.is_zero()));
    let prospect = baseline
        .prospective_port_preparation(&phases, &preparation, &target, &[false, true])
        .unwrap();
    // A physical-law control chart, not a claim that this test acquired the changed map.
    let changed = theta
        .clone()
        .with_ports(
            1,
            None,
            None,
            Some(ExactRatMatrix::identity(4).unwrap().scaled(&integer(2))),
        )
        .unwrap();
    let changed_word = open(&field, &changed, &current, &WordOpening::Rest);
    let changed_prospect = changed_word
        .prospective_port_preparation(&phases, &preparation, &target, &[false, true])
        .unwrap();
    assert_ne!(prospect.response(), changed_prospect.response());
    assert_ne!(prospect.unique_control(), changed_prospect.unique_control());
    assert!(prospect.prepare(changed_word).is_err());
}

#[test]
fn an_unconstrained_request_retains_the_whole_control_domain() {
    let (field, theta, current) = fixture();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let baseline = open(&field, &theta, &current, &WordOpening::Rest);
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let prospect = baseline
        .prospective_port_preparation(
            &phases,
            &preparation,
            &vec![vec![Rat::zero(); 4]; 2],
            &[false, false],
        )
        .unwrap();
    assert_eq!(prospect.response().rows(), 0);
    assert_eq!(prospect.response().columns(), 4);
    match prospect.fibre() {
        ControlFibre::Affine { particular, kernel } => {
            assert_eq!(particular, &vec![Rat::zero(); 4]);
            assert_eq!(kernel.len(), 4);
        }
        _ => panic!("no requested region constrains no control"),
    }
    assert!(prospect.unique_control().is_none());
}
