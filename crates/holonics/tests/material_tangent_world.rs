//! The World-sensitive material tangent (Refs #73 #62; the held-carry record §2 (e), §3).
//!
//! On the World-ask mechanics, with the native contact's factors declared as a test chart, a
//! teaching encounter carries the tangent of one contact-material direction through the actual
//! Word and, at the World port, through the World model's one live key, the World's own law. The
//! World's state tangent `ψ` it returns is checked against the actual World run on `θ ± εH`:
//! `(x(ε) − x(−ε))/2ε − ψ` is `O(ε²)` on the dyadic ladder, as exact inequalities. With two live
//! keys the World's tangent is not located, and the teaching encounter is refused before any
//! physical work.

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::HnnError;
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::physical::PhysicalReceiver;
use holonics::hnn::physical::action::{
    ActionCommunication, AdmittedWaves, BoundJointWorld, ModelKey, PreparedPhysicalProbe,
    WorldModel,
};
use holonics::hnn::propagation::Operands;
use holonics::hnn::ring::ResonatorMaterial;
use holonics::hnn::word::action::PortPreparation;
use holonics::hnn::word::continuation::MaterialDirection;
use holonics::hnn::{
    Constitution, Current, Encoded, Field, FieldDeclaration, RingDeclaration, WordOpening,
};
use holonics::holarchy::terrain::KnownTruth;
use holonics::holon::law::{ReferenceHolon, Scheme};
use holonics::holon::{Holon, HolonState, PortHolon};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::SymmetricForm;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::receipt::{ReceiptLaw, RegionChart};
use holonics::receiver::reception::{JointLaw, ReceiverFace};
use num_traits::{Signed, Zero};

/// Each participant's coordinates: the source's and the receiver's.
const N: usize = 4;

fn fixture() -> (Field, Constitution, Encoded) {
    let ring = |source| RingDeclaration {
        period: 2,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..2)
            .map(|node| FieldDeclaration::quarter_turn(node, 2))
            .collect(),
        lock: if source { vec![0, 1] } else { vec![] },
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
            loops: vec![],
            sources: vec![0],
            offsets: vec![],
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
    // The source is terminated by the actual World; only the receiving ring (ring 1) is loaded.
    let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ports(1, None, None, Some(ExactRatMatrix::identity(4).unwrap()))
        .unwrap()
        .with_ring_resonator(
            &field,
            1,
            ResonatorMaterial::new(
                ExactRatMatrix::identity(4).unwrap(),
                ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
                ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 16)),
                None,
            )
            .unwrap(),
        )
        .unwrap();
    let truth = KnownTruth::uniform(2, 0, 1, 1).unwrap();
    let source = Encoded::identity(&truth, &field).unwrap().remove(0);
    (field, theta, source)
}

/// The fixture's skew gyrator `Ω`, pairing each source coordinate with its receiver coordinate.
fn gyrator() -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..2 * N)
            .map(|i| {
                (0..2 * N)
                    .map(|j| {
                        if i < N && j == N + i {
                            -integer(1)
                        } else if i >= N && j == i - N {
                            integer(1)
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

fn diagonal_form(entries: &[Rat]) -> SymmetricForm {
    SymmetricForm::from_rows(
        (0..entries.len())
            .map(|i| {
                (0..entries.len())
                    .map(|j| {
                        if i == j {
                            entries[i].clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

/// The source ports: `B = [I; 0]` drives the source coordinates, or `B = 0` disconnects them.
fn source_input(connected: bool) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..2 * N)
            .map(|i| {
                (0..N)
                    .map(|j| {
                        if connected && i == j {
                            integer(1)
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

/// The medium `q̇ = (Ω − R) Q e + B e_P` of the fixture, with `R = 0`, at a diagonal storage.
fn medium(storage: &[Rat], input: ExactRatMatrix) -> Holon {
    Holon::new(
        PortHolon::medium(
            &gyrator(),
            &ExactRatMatrix::zero(2 * N, 2 * N).unwrap(),
            diagonal_form(storage),
            &input,
            false,
        )
        .unwrap(),
    )
    .unwrap()
}

fn unit_storage() -> Vec<Rat> {
    vec![integer(1); 2 * N]
}

fn admittance() -> Vec<Rat> {
    vec![integer(2); N]
}

fn key(field: &Field, holon: Holon) -> ModelKey {
    ModelKey::declare(
        ReferenceHolon::new(holon, field.step().clone(), Scheme::Midpoint).unwrap(),
        admittance(),
    )
    .unwrap()
}

/// The fixture's actual World on a declared law, from the source coordinate `e_0` at commit 0.
fn world(field: &Field, chart: Encoded, holon: Holon) -> BoundJointWorld {
    let law = JointLaw::new(
        ReferenceHolon::new(holon, field.step().clone(), Scheme::Midpoint).unwrap(),
        N,
    )
    .unwrap();
    let mut initial = vec![Rat::zero(); 2 * N];
    initial[0] = integer(1);
    let readers = (0..2 * N)
        .map(|i| {
            (0..2 * N)
                .map(|j| if i == j { integer(1) } else { Rat::zero() })
                .collect()
        })
        .collect();
    let receipt = ReceiptLaw::new(
        2 * N,
        readers,
        vec![RegionChart::new(integer(1), field.step().clone(), 0).unwrap(); 2 * N],
    )
    .unwrap();
    BoundJointWorld::new(
        law,
        HolonState::at(initial, 0),
        ReceiverFace::receiver_state(N, N).unwrap(),
        receipt,
        admittance(),
        chart,
        0,
    )
    .unwrap()
}

/// The probe's preparation: one actuator on the source's first coordinate (`B = e_0`, full column
/// rank).
fn actuator(field: &Field) -> PortPreparation {
    let map = ExactRatMatrix::new(
        (0..N)
            .map(|i| vec![if i == 0 { integer(1) } else { Rat::zero() }])
            .collect(),
    )
    .unwrap();
    PortPreparation::new(field, 0, map).unwrap()
}

/// The admitted waves of `2^(−exponent) ℤ` up to the larger model preparation work of a unit wave
/// either way (the acceptance's supply, so the integer lattice holds at least `u = −1, 0, 1`).
fn admitted(probe: &PreparedPhysicalProbe<'_, '_>, exponent: u32) -> AdmittedWaves {
    let feature = probe.feature();
    let up = feature.preparation_work(&[integer(1)]).unwrap();
    let down = feature.preparation_work(&[integer(-1)]).unwrap();
    let supply = if up > down { up } else { down };
    AdmittedWaves::declare(feature, exponent, supply, 1 << 12).unwrap()
}

/// A receiver on the actual World with `keys` founded at commit 0.
fn bound<'f>(
    field: &'f Field,
    theta: Constitution,
    source: &Encoded,
    keys: Vec<ModelKey>,
) -> PhysicalReceiver<'f> {
    let mut receiver =
        PhysicalReceiver::new(field, theta, Current::at_rest(field), WordOpening::Rest).unwrap();
    receiver
        .bind_world(world(
            field,
            source.part(0..0).unwrap(),
            medium(&unit_storage(), source_input(true)),
        ))
        .unwrap();
    receiver
        .bind_world_model(WorldModel::found(keys, 0).unwrap())
        .unwrap();
    receiver
}

/// A `rows × rows` test-chart factor: `diagonal(i)` on the diagonal, `upper` just above it.
fn factor(rows: usize, diagonal: impl Fn(usize) -> Rat, upper: Rat) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..rows)
            .map(|i| {
                (0..rows)
                    .map(|j| {
                        if i == j {
                            diagonal(i)
                        } else if j == i + 1 {
                            upper.clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

fn plus(a: &ExactRatMatrix, b: &ExactRatMatrix, s: &Rat) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..a.rows())
            .map(|i| {
                (0..a.columns())
                    .map(|j| a.get(i, j).unwrap() + s * b.get(i, j).unwrap())
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

/// The fixture's material with the contact's factors declared, at `θ + εH` on its storage factor.
struct Declared {
    base: Constitution,
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    direction: ExactRatMatrix,
}

impl Declared {
    fn new(field: &Field, base: Constitution) -> Self {
        let width = Operands::exact_at_cut(field, &base, &Current::at_rest(field))
            .unwrap()
            .contacts()[0]
            .width();
        Self {
            base,
            storage: factor(width, |i| rat(2 + i as i64, 3), rat(1, 4)),
            stiffness: factor(width, |i| rat(1, 2 + i as i64), rat(1, 8)),
            dissipation: factor(width, |_| rat(1, 3), Rat::zero()),
            direction: factor(
                width,
                |i| if i == 0 { integer(1) } else { Rat::zero() },
                rat(1, 2),
            ),
        }
    }

    fn at(&self, epsilon: &Rat) -> Constitution {
        self.base
            .clone()
            .with_channel(
                0,
                plus(&self.storage, &self.direction, epsilon),
                self.stiffness.clone(),
                self.dissipation.clone(),
            )
            .unwrap()
    }

    /// `δC = (C(1) − C(−1))/2`, read from the executed forms (exact for `c cᵀ`).
    fn storage_direction(&self, field: &Field) -> MaterialDirection {
        let form = |epsilon: &Rat| {
            Operands::exact_at_cut(field, &self.at(epsilon), &Current::at_rest(field))
                .unwrap()
                .contacts()[0]
                .forms()
                .0
                .clone()
        };
        let one = integer(1);
        let difference = plus(&form(&one), &form(&-one.clone()), &-one.clone());
        MaterialDirection {
            contact: 0,
            storage: Some(plus(&difference, &difference, &-rat(1, 2))),
            stiffness: None,
            dissipation: None,
        }
    }
}

fn l1(v: &[Rat]) -> Rat {
    v.iter().map(|x| x.abs()).sum()
}

/// The World's configuration after one encounter at `control` on `theta`, with the World's own key.
fn world_after(field: &Field, theta: Constitution, source: &Encoded, control: &[Rat]) -> Vec<Rat> {
    let keys = vec![key(field, medium(&unit_storage(), source_input(true)))];
    let mut receiver = bound(field, theta, source, keys);
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let reception = probe.encounter(&waves, control).unwrap();
    assert!(matches!(
        reception.reception,
        ActionCommunication::Received(_)
    ));
    receiver
        .participating_world()
        .unwrap()
        .state()
        .configuration
        .clone()
}

/// **The World-sensitive tangent is the actual World's derivative.** One teaching encounter on
/// `θ` carries `χ` through the Word and `ψ` through the World's one live key; the World run on
/// `θ ± εH` confirms `ψ` to second order on `ε = 2⁻⁴ … 2⁻⁸`.
#[test]
fn the_world_sensitive_tangent_is_the_actual_worlds_derivative() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let control = vec![integer(1)];

    let keys = vec![key(&field, medium(&unit_storage(), source_input(true)))];
    let mut receiver = bound(&field, declared.at(&Rat::zero()), &source, keys);
    let preparation = actuator(&field);
    let probe = receiver
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe
        .encounter_teaching(&waves, &control, &[direction])
        .unwrap();
    assert!(matches!(
        reception.reception,
        ActionCommunication::Received(_)
    ));
    let psi = tangents[0]
        .world()
        .expect("the tangent crosses the World port")
        .to_vec();
    assert!(
        psi.iter().any(|x| !x.is_zero()),
        "the native material moves the World"
    );

    let mut residuals: Vec<(Rat, Rat)> = Vec::new();
    for j in 4..9 {
        let epsilon = rat(1, 1i64 << j);
        let up = world_after(&field, declared.at(&epsilon), &source, &control);
        let down = world_after(&field, declared.at(&-epsilon.clone()), &source, &control);
        let two = integer(2) * &epsilon;
        let r = l1(&up
            .iter()
            .zip(&down)
            .zip(&psi)
            .map(|((a, b), t)| (a - b) / &two - t)
            .collect::<Vec<_>>());
        println!("world-sensitive tangent: ε = 2^-{j}: central residual {r}");
        residuals.push((epsilon, r));
    }
    let (first_epsilon, first) = &residuals[0];
    let scaled_first = first / (first_epsilon * first_epsilon);
    for pair in residuals.windows(2) {
        assert!(
            pair[1].1.clone() * integer(2) <= pair[0].1,
            "the residual halves at least"
        );
    }
    for (epsilon, residual) in &residuals {
        assert!(
            residual / (epsilon * epsilon) <= &scaled_first * integer(2),
            "the residual stays O(ε²)"
        );
    }
}

/// **With two live keys the World's tangent is not located**, and the teaching encounter is refused
/// before any physical work: the World's commit does not move.
#[test]
fn a_teaching_encounter_is_refused_until_the_world_is_located() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let keys = vec![
        key(&field, medium(&unit_storage(), source_input(true))),
        key(&field, medium(&unit_storage(), source_input(false))),
    ];
    let mut receiver = bound(&field, declared.at(&Rat::zero()), &source, keys);
    let before = receiver.participating_world().unwrap().state().commit;
    let preparation = actuator(&field);
    let probe = receiver
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let refused = probe.encounter_teaching(&waves, &[integer(1)], &[direction]);
    assert!(
        matches!(refused, Err(HnnError::Unadmitted { .. })),
        "refused: {:?}",
        refused.as_ref().err()
    );
    assert_eq!(
        receiver.participating_world().unwrap().state().commit,
        before
    );
}
