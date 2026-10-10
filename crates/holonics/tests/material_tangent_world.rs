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
    ActionCommunication, ActionReception, AdmittedFuture, AdmittedWaves, BoundJointWorld,
    ModelKey, PreparedPhysicalProbe, WorldLanding, WorldModel,
};
use holonics::hnn::propagation::Operands;
use holonics::hnn::ring::ResonatorMaterial;
use holonics::hnn::word::action::PortPreparation;
use holonics::hnn::field::ConstitutionRead;
use holonics::hnn::word::continuation::{Admitted, MaterialDirection, MaterialTangent};
use holonics::hnn::word::variation::ContactCoordinate;
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

/// The fixture's key, declaring the face the actual World reads (its receiver's own state).
fn faced_key(field: &Field) -> ModelKey {
    key(field, medium(&unit_storage(), source_input(true)))
        .with_face(ReceiverFace::receiver_state(N, N).unwrap(), N)
        .unwrap()
}

/// One station's produced logits and the World's observed raw face, as the encounter executed them.
struct StationLogits {
    station: usize,
    produced: Vec<Rat>,
    observed: Vec<Rat>,
}

/// The compared stations' logits of one encounter at `control` on `theta`.
fn compared_logits(
    field: &Field,
    theta: Constitution,
    source: &Encoded,
    control: &[Rat],
) -> Vec<StationLogits> {
    let mut receiver = bound(field, theta, source, vec![faced_key(field)]);
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let reception = probe.encounter(&waves, control).unwrap();
    let ActionCommunication::Received(received) = reception.reception else {
        panic!("the encounter completes");
    };
    let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
    ratio
        .stations()
        .iter()
        .map(|&station| {
            let read = received
                .boundary
                .readings()
                .iter()
                .find(|read| read.station == station)
                .unwrap();
            StationLogits {
                station,
                produced: read.read.logits.clone(),
                observed: received.encounter.steps()[read.crossing - 1]
                    .joint
                    .face()
                    .to_vec(),
            }
        })
        .collect()
}

/// The comparison's three parts at frozen covector `g`, on one encounter's logits.
fn parts(g: &[Vec<Rat>], logits: &[StationLogits]) -> [Rat; 3] {
    let mut parts = [Rat::zero(), Rat::zero(), Rat::zero()];
    for held in logits {
        let g = &g[held.station];
        for class in 0..g.len() / 2 {
            parts[0] += &g[2 * class] * &held.produced[2 * class];
            parts[1] += &g[2 * class + 1] * &held.produced[2 * class + 1];
            parts[2] -= &g[2 * class + 1] * &held.observed[2 * class + 1];
        }
    }
    parts
}

/// **The encounter's own comparison is credited through the World.** One teaching encounter on `θ`
/// holds, at its compared station, the produced logits' tangent and the observed face's tangent
/// through the located key's declared face, and pairs them with its own comparison's covector. The
/// encounters on `θ ± εH`, read at the frozen covector, confirm each part of the series to second
/// order on `ε = 2⁻⁴ … 2⁻⁸`; the World's face moves with the native material.
#[test]
fn the_encounters_comparison_is_credited_through_the_world() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let control = vec![integer(1)];

    let mut receiver = bound(
        &field,
        declared.at(&Rat::zero()),
        &source,
        vec![faced_key(&field)],
    );
    let preparation = actuator(&field);
    let probe = receiver
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe
        .encounter_teaching(&waves, &control, &[direction])
        .unwrap();
    let ActionCommunication::Received(received) = reception.reception else {
        panic!("the teaching encounter completes");
    };
    let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
    // The read the tangent differentiates is the comparison's produced face: equal phases.
    for &station in ratio.stations() {
        let read = received
            .boundary
            .readings()
            .iter()
            .find(|read| read.station == station)
            .unwrap();
        assert_eq!(ratio.faces().faces[station].phases(), &read.read.phases[..]);
    }
    let credit = tangents[0].comparison_credit(ratio).unwrap();
    let g = ratio.covector().unwrap().logits().to_vec();
    println!(
        "comparison credit: magnitude {}, produced phase {}, observed phase {}; total {}",
        credit.magnitude,
        credit.produced_phase,
        credit.observed_phase,
        credit.total()
    );
    assert!(
        !credit.observed_phase.is_zero(),
        "the World's observed face moves with the native material"
    );
    let tangent = [
        credit.magnitude.clone(),
        credit.produced_phase.clone(),
        credit.observed_phase.clone(),
    ];

    let mut residuals: Vec<(Rat, [Rat; 3])> = Vec::new();
    for j in 4..9 {
        let epsilon = rat(1, 1i64 << j);
        let up = parts(
            &g,
            &compared_logits(&field, declared.at(&epsilon), &source, &control),
        );
        let down = parts(
            &g,
            &compared_logits(&field, declared.at(&-epsilon.clone()), &source, &control),
        );
        let two = integer(2) * &epsilon;
        let r: [Rat; 3] = std::array::from_fn(|k| ((&up[k] - &down[k]) / &two - &tangent[k]).abs());
        println!(
            "comparison credit: ε = 2^-{j}: central residuals {} {} {}",
            r[0], r[1], r[2]
        );
        residuals.push((epsilon, r));
    }
    for k in 0..3 {
        let (first_epsilon, first) = &residuals[0];
        let scaled_first = &first[k] / (first_epsilon * first_epsilon);
        for pair in residuals.windows(2) {
            assert!(
                pair[1].1[k].clone() * integer(2) <= pair[0].1[k],
                "part {k}: the residual halves at least"
            );
        }
        for (epsilon, residual) in &residuals {
            assert!(
                &residual[k] / (epsilon * epsilon) <= &scaled_first * integer(2),
                "part {k}: the residual stays O(ε²)"
            );
        }
    }
}

/// Every raw Gram-factor coordinate of contact 0's three families on `theta`.
fn all_coordinates(theta: &Constitution) -> Vec<ContactCoordinate> {
    let width = theta.contact_storage(0).rows();
    let mut coordinates = Vec::new();
    for family in 0..3 {
        let factor = [
            theta.contact_storage(0),
            theta.contact_stiffness(0),
            theta.contact_dissipation(0),
        ][family];
        for row in 0..width {
            for column in 0..factor.columns() {
                coordinates.push(ContactCoordinate {
                    contact: 0,
                    family,
                    row,
                    column,
                });
            }
        }
    }
    coordinates
}

/// The second encounter's actual comparison code enclosure and its compared station's raw logits
/// and World face.
fn second_comparison(
    receiver: &mut PhysicalReceiver<'_>,
    field: &Field,
    source: &Encoded,
    control: &[Rat],
) -> (
    holonics::ratio::algebraic::ExactInterval,
    Rat,
    Vec<Rat>,
    Vec<Rat>,
) {
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let reception = probe.encounter(&waves, control).unwrap();
    let ActionCommunication::Received(received) = reception.reception else {
        panic!("the second encounter completes");
    };
    let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
    let station = ratio.stations()[0];
    let read = received
        .boundary
        .readings()
        .iter()
        .find(|read| read.station == station)
        .unwrap();
    (
        ratio.code_length().unwrap(),
        ratio.excess().unwrap(),
        read.read.logits.clone(),
        received.encounter.steps()[read.crossing - 1]
            .joint
            .face()
            .to_vec(),
    )
}

/// **The World landing reads the next encounter through the located key** (the held-carry record
/// §5): one teaching encounter on every raw coordinate of contact 0, the World-sensitive descent of
/// its own comparison, a declared step through the native first reach, and the located key's
/// prospect of the next encounter on `θ′` against `θ`. Whatever the decision, it is reported as
/// measured. When admitted, the actual next encounter is read against the key's prospect (equal
/// readings, exactly) and against the matched control without the landing.
#[test]
fn the_world_landing_reads_the_next_encounter() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let control = vec![integer(1)];
    let coordinates = all_coordinates(&theta);
    let directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(&field, &theta, c).unwrap())
        .collect();

    let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let preparation = actuator(&field);
    let probe = receiver
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe
        .encounter_teaching(&waves, &control, &directions)
        .unwrap();
    let ActionCommunication::Received(received) = reception.reception else {
        panic!("the teaching encounter completes");
    };
    let proposal = receiver
        .world_proposal(&coordinates, &[(&tangents[..], &received)])
        .unwrap();
    for step in proposal.steps() {
        println!(
            "world descent: family {:?}, entries {:?}",
            step.gradient.family(),
            step.gradient
                .entries()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
        );
    }
    let landing = receiver
        .land_world_descent(
            proposal,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[&control],
        )
        .unwrap();
    let reading = match landing {
        WorldLanding::Unreached(refusal) => {
            panic!("the measured landing reaches its lattice; it read: {refusal:?}")
        }
        WorldLanding::Read(reading) => reading,
    };
    println!(
        "world landing: grain raise {:?}; producing code {:?} excess {}; proposed code {:?} excess {}; decision {:?}; deposition work {:?}",
        reading.grain_raise,
        reading.waves[0].producing.code_length().unwrap(),
        reading.waves[0].producing.excess().unwrap(),
        reading.waves[0].proposed.code_length().unwrap(),
        reading.waves[0].proposed.excess().unwrap(),
        reading.decision,
        reading.deposition_work.as_ref().map(|w| w.to_string()),
    );
    // [measured, October 9; the record §5a] Under the lexicographic descent this fixture's landing is
    // admitted; kept as the fixture's regression of the measured outcome.
    assert!(reading.decision.is_ok(), "the measured landing is admitted");
    // The actual next encounter on θ′, against the key's prospect and the matched control.
    let landed = second_comparison(&mut receiver, &field, &source, &control);
    assert_eq!(
        landed.0,
        reading.waves[0].proposed.code_length().unwrap(),
        "the located key's prospect is the actual next comparison"
    );
    assert_eq!(landed.1, reading.waves[0].proposed.excess().unwrap());
    let mut matched = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    {
        let probe = matched
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        probe.encounter(&waves, &control).unwrap();
    }
    let unlanded = second_comparison(&mut matched, &field, &source, &control);
    println!(
        "world production: landed code {:?} excess {}; matched control code {:?} excess {}",
        landed.0, landed.1, unlanded.0, unlanded.1
    );
    assert_eq!(unlanded.0, reading.waves[0].producing.code_length().unwrap());
    assert_eq!(unlanded.1, reading.waves[0].producing.excess().unwrap());
    // Production in the admission's own order: strictly below in code, or an exactly equal code
    // (the prospects' witness) with a strictly smaller phase excess.
    assert!(
        landed.0.upper < unlanded.0.lower
            || (matches!(reading.decision, Ok(Admitted::Phase)) && landed.1 < unlanded.1),
        "the landed next comparison is better than the matched control's in the admission's order"
    );
}

/// One round of the loop on `receiver`: a teaching encounter on every raw coordinate of contact 0,
/// its World-sensitive descent, and the World landing read on the next encounter at the same
/// control. Returns the encounter's actual code enclosure and excess, and the landing's decision.
fn loop_round(
    receiver: &mut PhysicalReceiver<'_>,
    field: &Field,
    source: &Encoded,
    control: &[Rat],
) -> (
    holonics::ratio::algebraic::ExactInterval,
    Rat,
    String,
) {
    let theta = receiver.constitution().clone();
    let coordinates = all_coordinates(&theta);
    let directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(&field, &theta, c).unwrap())
        .collect();
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe
        .encounter_teaching(&waves, control, &directions)
        .unwrap();
    let ActionCommunication::Received(received) = reception.reception else {
        panic!("the teaching encounter completes");
    };
    let returned = &received.comparison.as_ref().unwrap().returned;
    let code = returned.ratio.code_length().unwrap();
    let excess = returned.ratio.excess().unwrap();
    let proposal = receiver
        .world_proposal(&coordinates, &[(&tangents[..], &received)])
        .unwrap();
    let landing = receiver
        .land_world_descent(
            proposal,
            source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[control],
        )
        .unwrap();
    let decision = match landing {
        WorldLanding::Unreached(refusal) => format!("unreached {refusal:?}"),
        WorldLanding::Read(reading) => {
            format!("{:?} at grain raise {:?}", reading.decision, reading.grain_raise)
        }
    };
    (code, excess, decision)
}

/// **The loop over six encounters, against its twin without landings.** Each round on the
/// learner is a teaching encounter, its World-sensitive descent and the landing read on the next
/// encounter; the twin runs the same encounters at the same control with no landing. Every round's
/// actual comparison is reported for both, as measured: the learner's material changes only where a
/// landing was admitted.
#[test]
fn the_world_loop_is_read_against_its_twin_over_encounters() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let control = vec![integer(1)];
    let mut learner = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let mut twin = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    for round in 0..6 {
        let (code, excess, decision) = loop_round(&mut learner, &field, &source, &control);
        let preparation = actuator(&field);
        let probe = twin
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, &control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the twin's encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        let (twin_code, twin_excess) = (ratio.code_length().unwrap(), ratio.excess().unwrap());
        println!(
            "world loop: round {round}: learner code {code:?} excess {excess}; twin code {twin_code:?} excess {twin_excess}; landing {decision}"
        );
    }
}

/// **The same landing without the asked history** (the second matched control of (d)): the
/// contemporary constitution before the landing and the landed one, each on a fresh World with no
/// earlier encounter, read at the same control.
#[test]
fn the_landed_material_is_read_without_its_history() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let control = vec![integer(1)];
    let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let before_landing = {
        // The teaching round's own receiving deposit precedes the landing; read the constitution
        // the landing staged its step on.
        let mut probe_receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
        let preparation = actuator(&field);
        let probe = probe_receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        probe.encounter(&waves, &control).unwrap();
        probe_receiver.constitution().clone()
    };
    let (_, _, decision) = loop_round(&mut receiver, &field, &source, &control);
    let landed = receiver.constitution().clone();
    println!("world history control: landing {decision}");
    for (name, material) in [("contemporary", before_landing), ("landed", landed)] {
        let mut fresh = bound(&field, material, &source, vec![faced_key(&field)]);
        let preparation = actuator(&field);
        let probe = fresh
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, &control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the fresh encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        println!(
            "world history control: {name} on a fresh World: code {:?} excess {}",
            ratio.code_length().unwrap(),
            ratio.excess().unwrap()
        );
    }
}

/// **A proposal binds its tangents to its own encounter.** The tangents of a first teaching encounter
/// with the reception of a second one are refused, before any step is staged.
#[test]
fn a_world_proposal_refuses_another_encounters_tangents() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let control = vec![integer(1)];
    let coordinates = all_coordinates(&theta);
    let directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(&field, &theta, c).unwrap())
        .collect();
    let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let preparation = actuator(&field);
    let teach = |receiver: &mut PhysicalReceiver<'_>, directions: &[MaterialDirection]| {
        let probe = receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        probe
            .encounter_teaching(&waves, &control, directions)
            .unwrap()
    };
    let (_, first_tangents) = teach(&mut receiver, &directions);
    let present = receiver.constitution().clone();
    let second_directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(&field, &present, c).unwrap())
        .collect();
    let (reception, _) = teach(&mut receiver, &second_directions);
    let ActionCommunication::Received(received) = reception.reception else {
        panic!("the second teaching encounter completes");
    };
    let refused = receiver.world_proposal(&coordinates, &[(&first_tangents[..], &received)]);
    assert!(
        matches!(refused, Err(HnnError::Unadmitted { .. })),
        "refused: {:?}",
        refused.as_ref().err()
    );
}

/// A change's coordinates in one exact list: storage, arrivals, contact states, resonator states.
fn flat(change: &holonics::hnn::word::EndChange) -> Vec<Rat> {
    let mut out: Vec<Rat> = change.storage.iter().flatten().cloned().collect();
    for [a, b] in change.arrivals.iter().chain(&change.states) {
        out.extend(a.iter().cloned());
        out.extend(b.iter().cloned());
    }
    for [a, b] in change.resonators.iter().flatten() {
        out.extend(a.iter().cloned());
        out.extend(b.iter().cloned());
    }
    out
}

/// The World's configuration and the native carry after two encounters at `control` on `theta`.
fn after_two(
    field: &Field,
    theta: Constitution,
    source: &Encoded,
    control: &[Rat],
) -> (Vec<Rat>, Vec<Rat>) {
    let mut receiver = bound(field, theta, source, vec![faced_key(field)]);
    let preparation = actuator(field);
    let mut carry = None;
    for _ in 0..2 {
        let probe = receiver
            .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        carry = Some(received.carry.change.clone());
    }
    (
        receiver
            .participating_world()
            .unwrap()
            .state()
            .configuration
            .clone(),
        flat(&carry.unwrap()),
    )
}

/// **The tangent continues into the next encounter** (the held-carry record §6): one teaching
/// encounter, its tangent crossed into the next opening with the World's state tangent carried, and
/// the next encounter carrying it. The World's state and the native carry after both encounters, run
/// on `θ ± εH`, confirm `ψ` and `χ` to second order on `ε = 2⁻⁴ … 2⁻⁸`. The receiving publication
/// between the encounters is a readout and moves neither.
#[test]
fn the_tangent_continues_into_the_next_encounter() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let control = vec![integer(1)];
    let mut receiver = bound(
        &field,
        declared.at(&Rat::zero()),
        &source,
        vec![faced_key(&field)],
    );
    let preparation = actuator(&field);
    let probe = receiver
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe
        .encounter_teaching(&waves, &control, &[direction])
        .unwrap();
    let ActionCommunication::Received(first) = reception.reception else {
        panic!("the first encounter completes");
    };
    let continued: Vec<_> = tangents
        .iter()
        .map(|t| {
            t.continued(&first.carry, &first.carry.conductances, &field)
                .unwrap()
        })
        .collect();
    let probe = receiver
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe.encounter_continued(&waves, &control, continued).unwrap();
    assert!(matches!(
        reception.reception,
        ActionCommunication::Received(_)
    ));
    let psi = tangents[0].world().unwrap().to_vec();
    let chi = flat(tangents[0].tangent());
    let mut residuals: Vec<(Rat, Rat, Rat)> = Vec::new();
    for j in 4..9 {
        let epsilon = rat(1, 1i64 << j);
        let (up_world, up_carry) = after_two(&field, declared.at(&epsilon), &source, &control);
        let (down_world, down_carry) =
            after_two(&field, declared.at(&-epsilon.clone()), &source, &control);
        let two = integer(2) * &epsilon;
        let central = |up: &[Rat], down: &[Rat], t: &[Rat]| {
            l1(&up
                .iter()
                .zip(down)
                .zip(t)
                .map(|((a, b), t)| (a - b) / &two - t)
                .collect::<Vec<_>>())
        };
        let rw = central(&up_world, &down_world, &psi);
        let rc = central(&up_carry, &down_carry, &chi);
        println!("continued tangent: ε = 2^-{j}: World residual {rw}; carry residual {rc}");
        residuals.push((epsilon, rw, rc));
    }
    let picks: [fn(&(Rat, Rat, Rat)) -> Rat; 2] = [|r| r.1.clone(), |r| r.2.clone()];
    for pick in picks {
        let (first_epsilon, _, _) = &residuals[0];
        let scaled_first = pick(&residuals[0]) / (first_epsilon * first_epsilon);
        for pair in residuals.windows(2) {
            assert!(
                pick(&pair[1]) * integer(2) <= pick(&pair[0]),
                "the residual halves at least"
            );
        }
        for r in &residuals {
            assert!(
                pick(r) / (&r.0 * &r.0) <= &scaled_first * integer(2),
                "the residual stays O(ε²)"
            );
        }
    }
}

/// **Co-clock twins at different controls cannot swap tangents.** Two fresh receivers at the same
/// producing commit and clock, taught at different admitted controls: the first's tangents with the
/// second's reception are refused, because each tangent is bound to its encounter's applied source
/// wave.
#[test]
fn co_clock_twins_cannot_swap_tangents() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let coordinates = all_coordinates(&theta);
    let directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(&field, &theta, c).unwrap())
        .collect();
    let preparation = actuator(&field);
    let teach = |control: &[Rat]| {
        let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
        let probe = receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let (reception, tangents) = probe
            .encounter_teaching(&waves, control, &directions)
            .unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the teaching encounter completes");
        };
        (receiver, received, tangents)
    };
    let (_, _, first_tangents) = teach(&[integer(1)]);
    let (second, second_received, second_tangents) = teach(&[integer(-1)]);
    assert!(second
        .world_proposal(&coordinates, &[(&second_tangents[..], &second_received)])
        .is_ok());
    let refused = second.world_proposal(&coordinates, &[(&first_tangents[..], &second_received)]);
    assert!(
        matches!(refused, Err(HnnError::Unadmitted { .. })),
        "refused: {:?}",
        refused.as_ref().err()
    );
}

/// A second declared World medium: a non-uniform diagonal storage, declared before any reading.
fn second_storage() -> Vec<Rat> {
    [1, 2, 1, 3, 2, 1, 3, 1].iter().map(|&n| integer(n)).collect()
}

/// A receiver on the second World, with its own key (the World's law) declaring the World's face.
fn bound_second<'f>(field: &'f Field, theta: Constitution, source: &Encoded) -> PhysicalReceiver<'f> {
    let mut receiver =
        PhysicalReceiver::new(field, theta, Current::at_rest(field), WordOpening::Rest).unwrap();
    receiver
        .bind_world(world(
            field,
            source.part(0..0).unwrap(),
            medium(&second_storage(), source_input(true)),
        ))
        .unwrap();
    let key = key(field, medium(&second_storage(), source_input(true)))
        .with_face(ReceiverFace::receiver_state(N, N).unwrap(), N)
        .unwrap();
    receiver
        .bind_world_model(WorldModel::found(vec![key], 0).unwrap())
        .unwrap();
    receiver
}

/// The second fixture's native contact factors, declared before any reading.
fn second_material(field: &Field, base: Constitution) -> Constitution {
    let width = Operands::exact_at_cut(field, &base, &Current::at_rest(field))
        .unwrap()
        .contacts()[0]
        .width();
    base.with_channel(
        0,
        factor(width, |i| rat(3 + i as i64, 4), rat(1, 8)),
        factor(width, |i| rat(1, 1 + i as i64), rat(1, 16)),
        factor(width, |_| rat(1, 4), Rat::zero()),
    )
    .unwrap()
}

/// **The loop on a second fixture, against its twin** (the record §5c): a different World medium
/// and different native contact factors, the same laws and the same reading as the first fixture's
/// loop. Reported as measured.
#[test]
fn the_world_loop_is_read_on_a_second_fixture() {
    let (field, base, source) = fixture();
    let theta = second_material(&field, base);
    let control = vec![integer(1)];
    let mut learner = bound_second(&field, theta.clone(), &source);
    let mut twin = bound_second(&field, theta.clone(), &source);
    for round in 0..6 {
        let (code, excess, decision) = loop_round(&mut learner, &field, &source, &control);
        let preparation = actuator(&field);
        let probe = twin
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, &control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the twin's encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        let (twin_code, twin_excess) = (ratio.code_length().unwrap(), ratio.excess().unwrap());
        println!(
            "second loop: round {round}: learner code {code:?} excess {excess}; twin code {twin_code:?} excess {twin_excess}; landing {decision}"
        );
    }
}

/// The fixture's actual World on a declared law, at a given state and native origin (the World's
/// owner rebinding it after a cold restore of the native side).
fn world_at(field: &Field, chart: Encoded, holon: Holon, state: HolonState, origin: usize) -> BoundJointWorld {
    let law = JointLaw::new(
        ReferenceHolon::new(holon, field.step().clone(), Scheme::Midpoint).unwrap(),
        N,
    )
    .unwrap();
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
        state,
        ReceiverFace::receiver_state(N, N).unwrap(),
        receipt,
        admittance(),
        chart,
        origin,
    )
    .unwrap()
}

/// **The landed material survives a cold restore** (acceptance (c)): after a teaching encounter and
/// its admitted landing, the receiver's constitution and carry are saved as exact text and mounted
/// on the declared founding (the material before any learning). The restored material and carry
/// equal the live ones. The World model's learned part is saved as its own exact text and restored
/// on its declared keys. The World, exterior to the machine, is rebound by its owner at its live
/// state. The next encounter then reads the same comparison on the restored receiver as on the live
/// one.
#[test]
fn the_landed_material_survives_a_cold_restore() {
    use holonics::hnn::Reference;
    use holonics::hnn::constitution::ContinuingState;
    let (field, base, source) = fixture();
    // A continued state mounts only material on its loci's lattices, so this fixture declares
    // dyadic contact factors (the first fixture's `2/3` is off every dyadic lattice).
    let width = Operands::exact_at_cut(&field, &base, &Current::at_rest(&field))
        .unwrap()
        .contacts()[0]
        .width();
    let theta = base
        .with_channel(
            0,
            factor(width, |i| rat(3 + i as i64, 4), rat(1, 8)),
            factor(width, |i| rat(1, 1i64 << (i + 1)), rat(1, 16)),
            factor(width, |_| rat(1, 4), Rat::zero()),
        )
        .unwrap();
    let control = vec![integer(1)];
    let mut live = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let mut admitted_round = None;
    for round in 0..6 {
        let (_, _, decision) = loop_round(&mut live, &field, &source, &control);
        println!("cold restore fixture: round {round}: landing {decision}");
        if decision.starts_with("Ok(") {
            admitted_round = Some(round);
            break;
        }
    }
    assert!(admitted_round.is_some(), "a landing is admitted within six rounds");
    assert_ne!(live.constitution(), &theta);

    let resident = live.resident();
    let text = resident
        .constitution()
        .continuing_state(field.sources()[0])
        .unwrap()
        .with_carry(resident.carried().cloned())
        .to_text();
    let state = ContinuingState::from_text(&text).unwrap();
    let restored = Reference::campaign_one()
        .mount_continued(&field, &Current::at_rest(&field), theta.clone(), &state)
        .unwrap();
    assert_eq!(restored.constitution(), resident.constitution(), "the material returns");
    assert_eq!(restored.carried(), resident.carried(), "the carry returns");
    let mut cold = PhysicalReceiver::from_resident(&field, restored).unwrap();
    let world_state = live.participating_world().unwrap().state().clone();
    let origin = live.resident().carried().unwrap().ticks;
    cold.bind_world(world_at(
        &field,
        source.part(0..0).unwrap(),
        medium(&unit_storage(), source_input(true)),
        world_state,
        origin,
    ))
    .unwrap();
    let model_text = live.world_model().unwrap().to_text();
    let model = WorldModel::restored(vec![faced_key(&field)], &model_text).unwrap();
    assert_eq!(&model, live.world_model().unwrap(), "the World model returns");
    cold.bind_world_model(model).unwrap();

    let read = |receiver: &mut PhysicalReceiver<'_>| {
        let preparation = actuator(&field);
        let probe = receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, &control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        (ratio.code_length().unwrap(), ratio.excess().unwrap())
    };
    let cold_next = read(&mut cold);
    let live_next = read(&mut live);
    println!(
        "cold restore: {} text bytes, World model {} text bytes; next comparison code {:?} excess {}",
        text.len(),
        model_text.len(),
        live_next.0,
        live_next.1
    );
    assert_eq!(cold_next, live_next, "the restored receiver reads the live comparison");
}

// ---- The credit of two observations (the held-carry record §7) ----

/// The two admitted waves of the chain: `u₁ = 1`, then `u₂ = −1`.
fn chain_controls() -> [Vec<Rat>; 2] {
    [vec![integer(1)], vec![integer(-1)]]
}

/// One observation: the tangents an encounter carried and its reception.
type Observation = (Vec<MaterialTangent>, ActionReception);

/// Two encounters on `receiver`, the first teaching `directions` at `first`, the second carrying the
/// first's tangents continued at `second`, with nothing landed between them.
fn teach_chain(
    receiver: &mut PhysicalReceiver<'_>,
    field: &Field,
    source: &Encoded,
    directions: &[MaterialDirection],
    first: &[Rat],
    second: &[Rat],
) -> [Observation; 2] {
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, tangents) = probe.encounter_teaching(&waves, first, directions).unwrap();
    let ActionCommunication::Received(one) = reception.reception else {
        panic!("the first encounter completes");
    };
    let continued: Vec<MaterialTangent> = tangents
        .iter()
        .map(|t| t.continued(&one.carry, &one.carry.conductances, field).unwrap())
        .collect();
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let (reception, continued) = probe.encounter_continued(&waves, second, continued).unwrap();
    let ActionCommunication::Received(two) = reception.reception else {
        panic!("the second encounter completes");
    };
    [(tangents, one), (continued, two)]
}

/// One plain encounter at `control` (no tangents).
fn plain(receiver: &mut PhysicalReceiver<'_>, field: &Field, source: &Encoded, control: &[Rat]) {
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    probe.encounter(&waves, control).unwrap();
}

/// **A two-observation proposal binds a chain** (§7 (b)): the chain in its order is admitted; the
/// swapped order, fresh tangents at the second encounter in place of continued ones, and a
/// continued tangent offered across a gap are refused.
#[test]
fn a_two_observation_proposal_binds_a_chain() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let [first, second] = chain_controls();
    let coordinates = all_coordinates(&theta);
    let directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(&field, &theta, c).unwrap())
        .collect();
    let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let [(t1, r1), (t2, r2)] =
        teach_chain(&mut receiver, &field, &source, &directions, &first, &second);
    assert!(
        receiver
            .world_proposal(&coordinates, &[(&t1[..], &r1), (&t2[..], &r2)])
            .is_ok(),
        "the chain in its order binds"
    );
    let swapped = receiver.world_proposal(&coordinates, &[(&t2[..], &r2), (&t1[..], &r1)]);
    assert!(matches!(swapped, Err(HnnError::Unadmitted { .. })), "{swapped:?}");

    // Fresh tangents at the second encounter: the same clocks, another origin.
    let mut fresh = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let preparation = actuator(&field);
    let teach = |receiver: &mut PhysicalReceiver<'_>, control: &[Rat]| {
        let probe = receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let (reception, tangents) = probe.encounter_teaching(&waves, control, &directions).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        (tangents, received)
    };
    let (f1, q1) = teach(&mut fresh, &first);
    let present = fresh.constitution().clone();
    let (f2, q2) = {
        let directions: Vec<MaterialDirection> = coordinates
            .iter()
            .map(|c| MaterialDirection::of_coordinate(&field, &present, c).unwrap())
            .collect();
        let probe = fresh
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let (reception, tangents) = probe.encounter_teaching(&waves, &second, &directions).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        (tangents, received)
    };
    let refused = fresh.world_proposal(&coordinates, &[(&f1[..], &q1), (&f2[..], &q2)]);
    assert!(matches!(refused, Err(HnnError::Unadmitted { .. })), "{refused:?}");

    // A gap: the first encounter's tangents continued, then a plain encounter, then the continued
    // tangents offered to the next: the continued tangent rides only the Word that opens on its carry.
    let mut gapped = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let (g1, p1) = teach(&mut gapped, &first);
    let continued: Vec<MaterialTangent> = g1
        .iter()
        .map(|t| t.continued(&p1.carry, &p1.carry.conductances, &field).unwrap())
        .collect();
    plain(&mut gapped, &field, &source, &first);
    let probe = gapped
        .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let refused = probe.encounter_continued(&waves, &second, continued);
    assert!(matches!(refused, Err(HnnError::Unadmitted { .. })), "{:?}", refused.err());
}

/// Both encounters' compared logits, the first at `first`, the second at `second`, on `theta`.
fn chain_logits(
    field: &Field,
    theta: Constitution,
    source: &Encoded,
    first: &[Rat],
    second: &[Rat],
) -> ([Vec<StationLogits>; 2], ExactRatMatrix) {
    let mut receiver = bound(field, theta, source, vec![faced_key(field)]);
    let read = |receiver: &mut PhysicalReceiver<'_>, control: &[Rat]| {
        let preparation = actuator(field);
        let probe = receiver
            .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        ratio
            .stations()
            .iter()
            .map(|&station| {
                let read = received
                    .boundary
                    .readings()
                    .iter()
                    .find(|read| read.station == station)
                    .unwrap();
                StationLogits {
                    station,
                    produced: read.read.logits.clone(),
                    observed: received.encounter.steps()[read.crossing - 1]
                        .joint
                        .face()
                        .to_vec(),
                }
            })
            .collect::<Vec<_>>()
    };
    let one = read(&mut receiver, first);
    let published = receiver
        .constitution()
        .receiving_map(field.receivers()[0].ring)
        .unwrap()
        .clone();
    let two = read(&mut receiver, second);
    ([one, two], published)
}

/// **The two-observation credit at its consumer** (§7 (a)): the credit `credit(T₁; r₁) +
/// credit(T₂; r₂)` on one storage direction. On `θ ± εH`, `ε = 2⁻⁴ … 2⁻⁸`, the two encounters' parts
/// at the frozen covectors are differenced centrally. The observed-phase part (the World's face, which
/// does not read the receiving relation) is confirmed to second order. The produced parts' central
/// residuals, which include the path through the receiving relation the first encounter published
/// (held exterior by the credit), are reported as measured.
#[test]
fn the_two_observation_credit_is_read_at_its_consumer() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let [first, second] = chain_controls();
    let mut receiver = bound(
        &field,
        declared.at(&Rat::zero()),
        &source,
        vec![faced_key(&field)],
    );
    let [(t1, r1), (t2, r2)] =
        teach_chain(&mut receiver, &field, &source, &[direction], &first, &second);
    let ratio = |r: &ActionReception| r.comparison.as_ref().unwrap().returned.ratio.clone();
    let (ratio1, ratio2) = (ratio(&r1), ratio(&r2));
    let c1 = t1[0].comparison_credit(&ratio1).unwrap();
    let c2 = t2[0].comparison_credit(&ratio2).unwrap();
    let g1 = ratio1.covector().unwrap().logits().to_vec();
    let g2 = ratio2.covector().unwrap().logits().to_vec();
    println!(
        "two-observation credit: first: magnitude {}, produced phase {}, observed phase {}; second (continued): magnitude {}, produced phase {}, observed phase {}",
        c1.magnitude, c1.produced_phase, c1.observed_phase, c2.magnitude, c2.produced_phase, c2.observed_phase
    );
    let credit = [
        &c1.magnitude + &c2.magnitude,
        &c1.produced_phase + &c2.produced_phase,
        &c1.observed_phase + &c2.observed_phase,
    ];
    let second_only = [
        c2.magnitude.clone(),
        c2.produced_phase.clone(),
        c2.observed_phase.clone(),
    ];
    let mut residuals: Vec<(Rat, [Rat; 3], [Rat; 3])> = Vec::new();
    for j in 4..9 {
        let epsilon = rat(1, 1i64 << j);
        let ([up1, up2], up_map) =
            chain_logits(&field, declared.at(&epsilon), &source, &first, &second);
        let ([down1, down2], down_map) =
            chain_logits(&field, declared.at(&-epsilon.clone()), &source, &first, &second);
        // The receiving relation the first encounter published, read on both sides.
        let moved: Vec<Rat> = (0..up_map.rows())
            .flat_map(|i| (0..up_map.columns()).map(move |j| (i, j)))
            .map(|(i, j)| (up_map.get(i, j).unwrap() - down_map.get(i, j).unwrap()).abs())
            .collect();
        println!(
            "two-observation credit: ε = 2^-{j}: the published receiving relation's central change (l1) {}",
            l1(&moved)
        );
        let two = integer(2) * &epsilon;
        let total = |a: [Rat; 3], b: [Rat; 3]| -> [Rat; 3] { std::array::from_fn(|k| &a[k] + &b[k]) };
        let up = total(parts(&g1, &up1), parts(&g2, &up2));
        let down = total(parts(&g1, &down1), parts(&g2, &down2));
        let r: [Rat; 3] = std::array::from_fn(|k| ((&up[k] - &down[k]) / &two - &credit[k]).abs());
        let up_second = parts(&g2, &up2);
        let down_second = parts(&g2, &down2);
        let s: [Rat; 3] = std::array::from_fn(|k| {
            ((&up_second[k] - &down_second[k]) / &two - &second_only[k]).abs()
        });
        println!(
            "two-observation credit: ε = 2^-{j}: central residuals (both) {} {} {}; (second alone) {} {} {}",
            r[0], r[1], r[2], s[0], s[1], s[2]
        );
        residuals.push((epsilon, r, s));
    }
    // [measured, October 10] Every part, both observations and the second alone, to second order: the
    // acceptance required it of the observed phase and reported the produced parts; they hold too.
    let picks: [fn(&(Rat, [Rat; 3], [Rat; 3])) -> Rat; 6] = [
        |r| r.1[0].clone(),
        |r| r.1[1].clone(),
        |r| r.1[2].clone(),
        |r| r.2[0].clone(),
        |r| r.2[1].clone(),
        |r| r.2[2].clone(),
    ];
    for pick in picks {
        let first_epsilon = residuals[0].0.clone();
        let scaled_first = pick(&residuals[0]) / (&first_epsilon * &first_epsilon);
        for pair in residuals.windows(2) {
            assert!(
                pick(&pair[1]) * integer(2) <= pick(&pair[0]),
                "the residual halves at least"
            );
        }
        for r in &residuals {
            assert!(
                pick(r) / (&r.0 * &r.0) <= &scaled_first * integer(2),
                "the residual stays O(ε²)"
            );
        }
    }
}

/// The two chain encounters' comparison code enclosures and excesses on `theta`, plain.
fn chain_readings(
    field: &Field,
    theta: Constitution,
    source: &Encoded,
) -> Vec<(holonics::ratio::algebraic::ExactInterval, Rat)> {
    let mut receiver = bound(field, theta, source, vec![faced_key(field)]);
    chain_controls()
        .iter()
        .map(|control| {
            let preparation = actuator(field);
            let probe = receiver
                .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
                .unwrap();
            let waves = admitted(&probe, 0);
            let reception = probe.encounter(&waves, control).unwrap();
            let ActionCommunication::Received(received) = reception.reception else {
                panic!("the encounter completes");
            };
            let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
            (ratio.code_length().unwrap(), ratio.excess().unwrap())
        })
        .collect()
}

/// The second encounter's chain on a fresh learner at `theta`, its proposal over `observations`
/// (both, or the continued one alone) and its landing over both waves.
fn land_chain<'f>(
    field: &'f Field,
    theta: &Constitution,
    source: &Encoded,
    both: bool,
) -> (PhysicalReceiver<'f>, WorldLanding) {
    let [first, second] = chain_controls();
    let coordinates = all_coordinates(theta);
    let directions: Vec<MaterialDirection> = coordinates
        .iter()
        .map(|c| MaterialDirection::of_coordinate(field, theta, c).unwrap())
        .collect();
    let mut receiver = bound(field, theta.clone(), source, vec![faced_key(field)]);
    let [(t1, r1), (t2, r2)] =
        teach_chain(&mut receiver, field, source, &directions, &first, &second);
    let observations: Vec<(&[MaterialTangent], &ActionReception)> = if both {
        vec![(&t1[..], &r1), (&t2[..], &r2)]
    } else {
        vec![(&t2[..], &r2)]
    };
    let proposal = receiver.world_proposal(&coordinates, &observations).unwrap();
    let preparation = actuator(field);
    let landing = receiver
        .land_world_descent(
            proposal,
            source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[&first, &second],
        )
        .unwrap();
    (receiver, landing)
}

/// **The landing over both waves** (§7 (c), (d)): the credit of both observations, and the
/// continued credit alone, each landed as one step and read at both waves' prospects. Each decision
/// is reported as measured. When admitted, the actual next encounter at each wave (on identical
/// replays) equals its prospect exactly, and is read against the no-deposit twin at that wave.
#[test]
fn the_two_observation_landing_reads_both_waves() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let controls = chain_controls();
    for (name, both) in [("both observations", true), ("continued credit alone", false)] {
        let (_, landing) = land_chain(&field, &theta, &source, both);
        let reading = match landing {
            WorldLanding::Unreached(refusal) => {
                println!("two-observation landing ({name}): unreached {refusal:?}");
                continue;
            }
            WorldLanding::Read(reading) => reading,
        };
        println!(
            "two-observation landing ({name}): grain raise {:?}; decision {:?}; deposition work {:?}",
            reading.grain_raise,
            reading.decision,
            reading.deposition_work.as_ref().map(|w| w.to_string())
        );
        for wave in &reading.waves {
            println!(
                "two-observation landing ({name}): wave {:?}: producing code {:?} excess {}; proposed code {:?} excess {}; decision {:?}",
                wave.control.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
                wave.producing.code_length().unwrap(),
                wave.producing.excess().unwrap(),
                wave.proposed.code_length().unwrap(),
                wave.proposed.excess().unwrap(),
                wave.decision
            );
        }
        // [measured diagnostic] The credited objective itself at the declared step: the same two
        // encounters from the initial material, with only the contact factors of the candidate.
        let stepped = theta
            .clone()
            .with_channel(
                0,
                reading.candidate.contact_storage(0).clone(),
                reading.candidate.contact_stiffness(0).clone(),
                reading.candidate.contact_dissipation(0).clone(),
            )
            .unwrap();
        let base_chain = chain_readings(&field, theta.clone(), &source);
        let stepped_chain = chain_readings(&field, stepped, &source);
        for (k, ((code, excess), (s_code, s_excess))) in
            base_chain.iter().zip(&stepped_chain).enumerate()
        {
            println!(
                "two-observation credited objective ({name}): encounter {k}: code {code:?} -> {s_code:?}; excess change {}",
                s_excess - excess
            );
        }
        if reading.decision.is_err() {
            continue;
        }
        for (index, control) in controls.iter().enumerate() {
            // An identical replay, then the actual next encounter at this wave.
            let (mut replay, _) = land_chain(&field, &theta, &source, both);
            let landed = second_comparison(&mut replay, &field, &source, control);
            let wave = &reading.waves[index];
            assert_eq!(
                landed.0,
                wave.proposed.code_length().unwrap(),
                "the located key's prospect is the actual next comparison"
            );
            assert_eq!(landed.1, wave.proposed.excess().unwrap());
            // The no-deposit twin: the same two encounters, no landing.
            let mut twin = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
            plain(&mut twin, &field, &source, &controls[0]);
            plain(&mut twin, &field, &source, &controls[1]);
            let unlanded = second_comparison(&mut twin, &field, &source, control);
            println!(
                "two-observation production ({name}): wave {index}: landed code {:?} excess {}; twin code {:?} excess {}",
                landed.0, landed.1, unlanded.0, unlanded.1
            );
        }
    }
}

// ---- The admitted future descended: the prospect's own credit (the held-carry record §7b) ----

impl Declared {
    /// The contact material of `at(ε)` on another constitution (its receiving relation kept).
    fn on(&self, material: &Constitution, epsilon: &Rat) -> Constitution {
        material
            .clone()
            .with_channel(
                0,
                plus(&self.storage, &self.direction, epsilon),
                self.stiffness.clone(),
                self.dissipation.clone(),
            )
            .unwrap()
    }
}

/// The two chain encounters, plain, the second kept as the receiver's latest reception.
fn experience(receiver: &mut PhysicalReceiver<'_>, field: &Field, source: &Encoded) -> ActionReception {
    let [first, second] = chain_controls();
    plain(receiver, field, source, &first);
    let preparation = actuator(field);
    let probe = receiver
        .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
        .unwrap();
    let waves = admitted(&probe, 0);
    let reception = probe.encounter(&waves, &second).unwrap();
    let ActionCommunication::Received(last) = reception.reception else {
        panic!("the second encounter completes");
    };
    last
}

/// **The prospect's credit at its consumer** (§7b): after two encounters, the located key's
/// prospect of the next encounter at each wave, taught along one storage direction from the present
/// opening. On `θ ± εH` (the present receiving relation kept), the prospects' parts at the frozen
/// covector confirm the credit to second order on `ε = 2⁻⁴ … 2⁻⁸`.
#[test]
fn the_prospect_is_credited_at_its_consumer() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let mut receiver = bound(
        &field,
        declared.at(&Rat::zero()),
        &source,
        vec![faced_key(&field)],
    );
    experience(&mut receiver, &field, &source);
    let present = receiver.constitution().clone();
    let preparation = actuator(&field);
    for control in chain_controls() {
        let (ratio, tangents) = receiver
            .world_prospect_taught(
                &present,
                &source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                &control,
                &[direction.clone()],
            )
            .unwrap();
        let credit = tangents[0].comparison_credit(&ratio).unwrap();
        println!(
            "prospect credit: wave {}: magnitude {}, produced phase {}, observed phase {}",
            control[0], credit.magnitude, credit.produced_phase, credit.observed_phase
        );
        let g = ratio.covector().unwrap().logits().to_vec();
        let tangent = [credit.magnitude, credit.produced_phase, credit.observed_phase];
        let logits_at = |epsilon: &Rat| -> Vec<StationLogits> {
            let (prospect, _) = receiver
                .located_prospect(
                    &declared.on(&present, epsilon),
                    &source,
                    &field.receivers()[0],
                    &preparation,
                    &[false, true],
                    &control,
                )
                .unwrap();
            prospect
                .point
                .features
                .iter()
                .zip(&prospect.faces)
                .enumerate()
                // numbered as the prospect's comparison numbers its stations
                .map(|(rank, ((_, _, logits), (_, face)))| StationLogits {
                    station: rank,
                    produced: logits.clone(),
                    observed: face.clone(),
                })
                .collect()
        };
        let mut residuals: Vec<(Rat, [Rat; 3])> = Vec::new();
        for j in 4..9 {
            let epsilon = rat(1, 1i64 << j);
            let up = parts(&g, &logits_at(&epsilon));
            let down = parts(&g, &logits_at(&-epsilon.clone()));
            let two = integer(2) * &epsilon;
            let r: [Rat; 3] =
                std::array::from_fn(|k| ((&up[k] - &down[k]) / &two - &tangent[k]).abs());
            println!(
                "prospect credit: wave {}: ε = 2^-{j}: central residuals {} {} {}",
                control[0], r[0], r[1], r[2]
            );
            residuals.push((epsilon, r));
        }
        for k in 0..3 {
            let (first_epsilon, first) = &residuals[0];
            let scaled_first = &first[k] / (first_epsilon * first_epsilon);
            for pair in residuals.windows(2) {
                assert!(
                    pair[1].1[k].clone() * integer(2) <= pair[0].1[k],
                    "part {k}: the residual halves at least"
                );
            }
            for (epsilon, residual) in &residuals {
                assert!(
                    &residual[k] / (epsilon * epsilon) <= &scaled_first * integer(2),
                    "part {k}: the residual stays O(ε²)"
                );
            }
        }
    }
}

/// Two encounters on a fresh learner at `theta`, then the proposal descending both waves'
/// prospects and its landing over both waves.
fn land_prospect<'f>(
    field: &'f Field,
    theta: &Constitution,
    source: &Encoded,
) -> (PhysicalReceiver<'f>, WorldLanding) {
    let [first, second] = chain_controls();
    let mut receiver = bound(field, theta.clone(), source, vec![faced_key(field)]);
    let last = experience(&mut receiver, field, source);
    let present = receiver.constitution().clone();
    let coordinates = all_coordinates(&present);
    let preparation = actuator(field);
    let proposal = receiver
        .world_prospect_proposal(
            &coordinates,
            source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[&first, &second],
            &last,
        )
        .unwrap();
    let landing = receiver
        .land_world_descent(
            proposal,
            source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[&first, &second],
        )
        .unwrap();
    (receiver, landing)
}

/// **The admitted future, descended** (§7b): after the same two encounters, the step descends the
/// located key's prospects at both waves and lands through the same admission. The decision is
/// reported as measured; when admitted, the actual next encounter at each wave (on identical
/// replays) equals its prospect exactly and is read against the no-deposit twin at that wave.
#[test]
fn the_prospect_landing_reads_both_waves() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let controls = chain_controls();
    let (_, landing) = land_prospect(&field, &theta, &source);
    let reading = match landing {
        WorldLanding::Unreached(refusal) => {
            println!("prospect landing: unreached {refusal:?}");
            return;
        }
        WorldLanding::Read(reading) => reading,
    };
    println!(
        "prospect landing: grain raise {:?}; decision {:?}; deposition work {:?}",
        reading.grain_raise,
        reading.decision,
        reading.deposition_work.as_ref().map(|w| w.to_string())
    );
    for wave in &reading.waves {
        println!(
            "prospect landing: wave {:?}: producing code {:?} excess {}; proposed code {:?} excess {}; decision {:?}",
            wave.control.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
            wave.producing.code_length().unwrap(),
            wave.producing.excess().unwrap(),
            wave.proposed.code_length().unwrap(),
            wave.proposed.excess().unwrap(),
            wave.decision
        );
    }
    // [measured, October 10; the record §7b] On this fixture the landing over both waves is
    // admitted; kept as the fixture's regression of the measured outcome.
    assert!(reading.decision.is_ok(), "the measured prospect landing is admitted");
    for (index, control) in controls.iter().enumerate() {
        let (mut replay, _) = land_prospect(&field, &theta, &source);
        let landed = second_comparison(&mut replay, &field, &source, control);
        let wave = &reading.waves[index];
        assert_eq!(
            landed.0,
            wave.proposed.code_length().unwrap(),
            "the located key's prospect is the actual next comparison"
        );
        assert_eq!(landed.1, wave.proposed.excess().unwrap());
        let mut twin = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
        experience(&mut twin, &field, &source);
        let unlanded = second_comparison(&mut twin, &field, &source, control);
        println!(
            "prospect production: wave {index}: landed code {:?} excess {}; twin code {:?} excess {}",
            landed.0, landed.1, unlanded.0, unlanded.1
        );
        // Production in the admission's own order, at this wave: strictly below in code, or an
        // equal code (the wave's witness) with a strictly smaller phase excess.
        assert_eq!(unlanded.0, wave.producing.code_length().unwrap());
        assert_eq!(unlanded.1, wave.producing.excess().unwrap());
        assert!(
            landed.0.upper < unlanded.0.lower
                || (matches!(wave.decision, Ok(Admitted::Phase)) && landed.1 < unlanded.1),
            "the landed next comparison is better than the twin's at wave {index}"
        );
    }
}

/// **The prospect landing without its history** (§7b, the no-history control): the contemporary
/// material the landing staged on (after the two encounters) and the landed one, each on a fresh
/// World with no earlier encounter, read at both waves. Reported as measured.
#[test]
fn the_prospect_landed_material_is_read_without_its_history() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let contemporary = {
        let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
        experience(&mut receiver, &field, &source);
        receiver.constitution().clone()
    };
    let (landed_receiver, landing) = land_prospect(&field, &theta, &source);
    let WorldLanding::Read(reading) = landing else {
        panic!("the measured prospect landing reaches its lattice");
    };
    assert!(reading.decision.is_ok(), "the measured prospect landing is admitted");
    let landed = landed_receiver.constitution().clone();
    for (index, control) in chain_controls().iter().enumerate() {
        let read = |material: &Constitution| {
            let mut fresh = bound(&field, material.clone(), &source, vec![faced_key(&field)]);
            let comparison = second_comparison(&mut fresh, &field, &source, control);
            (comparison.0, comparison.1)
        };
        let (c_code, c_excess) = read(&contemporary);
        let (l_code, l_excess) = read(&landed);
        println!(
            "prospect history control: wave {index}: contemporary on a fresh World code {c_code:?} excess {c_excess}; landed on a fresh World code {l_code:?} excess {l_excess}"
        );
    }
}

/// **One observation or two** (§7b): the same prospect landing after only the first encounter
/// (`u = 1`), read at both waves. Reported as measured: it says whether the second observation
/// changes the step on this fixture.
#[test]
fn the_prospect_landing_after_one_observation() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let theta = declared.at(&Rat::zero());
    let [first, second] = chain_controls();
    let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
    let preparation = actuator(&field);
    let last = {
        let probe = receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, &first).unwrap();
        let ActionCommunication::Received(last) = reception.reception else {
            panic!("the encounter completes");
        };
        last
    };
    let coordinates = all_coordinates(receiver.constitution());
    let proposal = receiver.world_prospect_proposal(
        &coordinates,
        &source,
        &field.receivers()[0],
        &preparation,
        &[false, true],
        &[&first, &second],
        &last,
    );
    let proposal = match proposal {
        Ok(proposal) => proposal,
        Err(refusal) => {
            println!("prospect after one observation: proposal refused {refusal:?}");
            return;
        }
    };
    let landing = receiver
        .land_world_descent(
            proposal,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[&first, &second],
        )
        .unwrap();
    match landing {
        WorldLanding::Unreached(refusal) => {
            println!("prospect after one observation: unreached {refusal:?}")
        }
        WorldLanding::Read(reading) => {
            println!(
                "prospect after one observation: grain raise {:?}; decision {:?}",
                reading.grain_raise, reading.decision
            );
            for wave in &reading.waves {
                println!(
                    "prospect after one observation: wave {:?}: producing code {:?} excess {}; proposed code {:?} excess {}; decision {:?}",
                    wave.control.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
                    wave.producing.code_length().unwrap(),
                    wave.producing.excess().unwrap(),
                    wave.proposed.code_length().unwrap(),
                    wave.proposed.excess().unwrap(),
                    wave.decision
                );
            }
        }
    }
}

/// One round of the prospect loop on `receiver`: the two chain encounters, then the step descending
/// both waves' prospects and its landing. Returns each encounter's actual code and excess, and the
/// landing's decision.
fn prospect_round(
    receiver: &mut PhysicalReceiver<'_>,
    field: &Field,
    source: &Encoded,
) -> (
    Vec<(holonics::ratio::algebraic::ExactInterval, Rat)>,
    String,
) {
    let [first, second] = chain_controls();
    let preparation = actuator(field);
    let mut read = Vec::new();
    let mut last = None;
    for control in [&first, &second] {
        let probe = receiver
            .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        read.push((ratio.code_length().unwrap(), ratio.excess().unwrap()));
        last = Some(received);
    }
    let last = last.unwrap();
    let coordinates = all_coordinates(receiver.constitution());
    let decision = match receiver.world_prospect_proposal(
        &coordinates,
        source,
        &field.receivers()[0],
        &preparation,
        &[false, true],
        &[&first, &second],
        &last,
    ) {
        Err(refusal) => format!("proposal refused {refusal:?}"),
        Ok(proposal) => match receiver
            .land_world_descent(
                proposal,
                source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                &[&first, &second],
            )
            .unwrap()
        {
            WorldLanding::Unreached(refusal) => format!("unreached {refusal:?}"),
            WorldLanding::Read(reading) => format!(
                "{:?} at grain raise {:?} (waves {:?})",
                reading.decision,
                reading.grain_raise,
                reading.waves.iter().map(|w| w.decision).collect::<Vec<_>>()
            ),
        },
    };
    (read, decision)
}

/// One fixture's prospect loop over five rounds, against its twin with no landing (§7c).
fn prospect_loop(name: &str, second: bool) {
    let (field, base, source) = fixture();
    let theta = if second {
        second_material(&field, base)
    } else {
        Declared::new(&field, base).at(&Rat::zero())
    };
    let make = |theta: &Constitution| {
        if second {
            bound_second(&field, theta.clone(), &source)
        } else {
            bound(&field, theta.clone(), &source, vec![faced_key(&field)])
        }
    };
    let mut learner = make(&theta);
    let mut twin = make(&theta);
    for round in 0..5 {
        let (read, decision) = prospect_round(&mut learner, &field, &source);
        let mut twin_read = Vec::new();
        for control in chain_controls() {
            let comparison = second_comparison(&mut twin, &field, &source, &control);
            twin_read.push((comparison.0, comparison.1));
        }
        for (wave, ((code, excess), (t_code, t_excess))) in read.iter().zip(&twin_read).enumerate() {
            println!(
                "prospect loop ({name}): round {round}: wave {wave}: learner code {code:?} excess {excess}; twin code {t_code:?} excess {t_excess}"
            );
        }
        println!("prospect loop ({name}): round {round}: landing {decision}");
    }
}

/// **The prospect loop over rounds, against its twin** (§7c), first fixture: each round on the
/// learner is the two chain encounters and the prospect landing; the twin runs the same encounters
/// with no landing. Every round's actual comparisons at both waves are reported, as measured.
#[test]
fn the_prospect_loop_is_read_against_its_twin() {
    prospect_loop("first", false);
}

/// The same loop on the second fixture (§7c).
#[test]
fn the_prospect_loop_is_read_on_a_second_fixture() {
    prospect_loop("second", true);
}

/// One fixture's schedule-consistent loop (§7d): before every encounter after the first, a landing
/// on that very encounter's prospect (one wave, the one that comes next), then the encounter. The
/// twin runs the same encounters with no landing. Each encounter is reported against the twin.
fn per_encounter_loop(name: &str, second: bool) {
    let (field, base, source) = fixture();
    let theta = if second {
        second_material(&field, base)
    } else {
        Declared::new(&field, base).at(&Rat::zero())
    };
    let make = |theta: &Constitution| {
        if second {
            bound_second(&field, theta.clone(), &source)
        } else {
            bound(&field, theta.clone(), &source, vec![faced_key(&field)])
        }
    };
    let mut learner = make(&theta);
    let mut twin = make(&theta);
    let preparation = actuator(&field);
    let schedule: Vec<Vec<Rat>> = (0..5).flat_map(|_| chain_controls()).collect();
    let mut last: Option<ActionReception> = None;
    for (k, control) in schedule.iter().enumerate() {
        let decision = match &last {
            None => "none (first encounter)".to_string(),
            Some(last) => {
                let coordinates = all_coordinates(learner.constitution());
                match learner.world_prospect_proposal(
                    &coordinates,
                    &source,
                    &field.receivers()[0],
                    &preparation,
                    &[false, true],
                    &[control],
                    last,
                ) {
                    Err(refusal) => format!("proposal refused {refusal:?}"),
                    Ok(proposal) => match learner
                        .land_world_descent(
                            proposal,
                            &source,
                            &field.receivers()[0],
                            &preparation,
                            &[false, true],
                            &[control],
                        )
                        .unwrap()
                    {
                        WorldLanding::Unreached(refusal) => format!("unreached {refusal:?}"),
                        WorldLanding::Read(reading) => {
                            format!("{:?} at grain raise {:?}", reading.decision, reading.grain_raise)
                        }
                    },
                }
            }
        };
        let probe = learner
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
        let (code, excess) = (ratio.code_length().unwrap(), ratio.excess().unwrap());
        last = Some(received);
        let (t_code, t_excess, _, _) = second_comparison(&mut twin, &field, &source, control);
        println!(
            "per-encounter loop ({name}): encounter {k} (u = {}): landing before it {decision}; learner code {code:?} excess {excess}; twin code {t_code:?} excess {t_excess}",
            control[0]
        );
    }
}

/// **The schedule-consistent loop** (§7d), first fixture: a landing on each next encounter's own
/// prospect before it, over ten encounters alternating `u = 1, −1`, against the twin.
#[test]
fn the_per_encounter_loop_is_read_against_its_twin() {
    per_encounter_loop("first", false);
}

/// The same on the second fixture (§7d).
#[test]
fn the_per_encounter_loop_is_read_on_a_second_fixture() {
    per_encounter_loop("second", true);
}

/// **Does the receiving relation move between encounters?** (§7d, a design read for the cycle):
/// over ten plain encounters alternating `u = 1, −1` on both fixtures, whether each encounter's
/// receiving publication changed `R`, reported as measured.
#[test]
fn the_receiving_relation_between_encounters() {
    let (field, base, source) = fixture();
    for (name, second) in [("first", false), ("second", true)] {
        let theta = if second {
            second_material(&field, base.clone())
        } else {
            Declared::new(&field, base.clone()).at(&Rat::zero())
        };
        let mut receiver = if second {
            bound_second(&field, theta, &source)
        } else {
            bound(&field, theta, &source, vec![faced_key(&field)])
        };
        let preparation = actuator(&field);
        let mut moved = Vec::new();
        for k in 0..10 {
            let control = &chain_controls()[k % 2];
            let probe = receiver
                .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
                .unwrap();
            let waves = admitted(&probe, 0);
            let reception = probe.encounter(&waves, control).unwrap();
            let ActionCommunication::Received(received) = reception.reception else {
                panic!("the encounter completes");
            };
            let comparison = received.comparison.as_ref().unwrap();
            moved.push(comparison.receiving_before != comparison.receiving_after);
        }
        println!("receiving relation ({name}): moved at encounters {moved:?}");
    }
}

/// **Does the passage settle?** (§7e, a design read for the cycle): forty plain encounters
/// alternating `u = 1, −1` on the first fixture, each encounter's comparison and whether its
/// receiving publication moved `R`, reported as measured.
#[test]
fn the_passage_over_forty_encounters() {
    let (field, base, source) = fixture();
    let theta = Declared::new(&field, base).at(&Rat::zero());
    let mut receiver = bound(&field, theta, &source, vec![faced_key(&field)]);
    let preparation = actuator(&field);
    for k in 0..40 {
        let control = &chain_controls()[k % 2];
        let probe = receiver
            .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        let comparison = received.comparison.as_ref().unwrap();
        let ratio = &comparison.returned.ratio;
        println!(
            "passage: encounter {k} (u = {}): code {:?} excess {}; R moved {}",
            control[0],
            ratio.code_length().unwrap(),
            ratio.excess().unwrap(),
            comparison.receiving_before != comparison.receiving_after
        );
    }
}

// ---- The schedule's chained prospect (the held-carry record §7f) ----

/// `count` plain encounters alternating `u = 1, −1`, the last kept as the latest reception.
fn plain_passage(
    receiver: &mut PhysicalReceiver<'_>,
    field: &Field,
    source: &Encoded,
    count: usize,
) -> ActionReception {
    let preparation = actuator(field);
    let mut last = None;
    for k in 0..count {
        let control = &chain_controls()[k % 2];
        let probe = receiver
            .prepare_probe(source, &field.receivers()[0], &preparation, &[false, true])
            .unwrap();
        let waves = admitted(&probe, 0);
        let reception = probe.encounter(&waves, control).unwrap();
        let ActionCommunication::Received(received) = reception.reception else {
            panic!("the encounter completes");
        };
        last = Some(received);
    }
    last.unwrap()
}

/// **The schedule's chained prospect is the actual schedule** (§7f, §7h): after `count` encounters,
/// the located key's prospect of the next two encounters (`u = 1`, then `u = −1`) is read, with the
/// receiving publication between them joined, then the two encounters actually run. Both are asserted
/// equal to their prospects, after two encounters (while the receiving relation still moves) and after
/// twelve.
#[test]
fn the_schedule_prospect_is_the_actual_schedule() {
    let (field, base, source) = fixture();
    let theta = Declared::new(&field, base).at(&Rat::zero());
    let preparation = actuator(&field);
    let [first, second] = chain_controls();
    for count in [2, 12] {
        let mut receiver = bound(&field, theta.clone(), &source, vec![faced_key(&field)]);
        plain_passage(&mut receiver, &field, &source, count);
        let present = receiver.constitution().clone();
        let prospects = receiver
            .world_prospect_schedule(
                &present,
                &source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                &[&first, &second],
                &[],
            )
            .unwrap();
        for (k, control) in [&first, &second].iter().enumerate() {
            let actual = second_comparison(&mut receiver, &field, &source, control);
            let prospect = &prospects[k].ratio;
            let equal = actual.0 == prospect.code_length().unwrap()
                && actual.1 == prospect.excess().unwrap();
            println!(
                "schedule prospect: after {count} encounters: encounter {k}: actual equals prospect {equal}"
            );
            assert!(equal, "the chained prospect is the actual encounter {k} after {count}");
        }
    }
}

/// **The schedule's credit at its consumer** (§7f): after twelve encounters, the chained prospect of
/// `u = 1` then `u = −1` taught along one storage direction; the two encounters' credits summed. On
/// `θ ± εH` (the present receiving relation kept) the two prospects' parts at their frozen covectors
/// confirm it to second order on `ε = 2⁻⁴ … 2⁻⁸`.
#[test]
fn the_schedule_is_credited_at_its_consumer() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let mut receiver = bound(
        &field,
        declared.at(&Rat::zero()),
        &source,
        vec![faced_key(&field)],
    );
    plain_passage(&mut receiver, &field, &source, 12);
    let present = receiver.constitution().clone();
    let preparation = actuator(&field);
    let [first, second] = chain_controls();
    let taught = receiver
        .world_prospect_schedule(
            &present,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &[&first, &second],
            &[direction],
        )
        .unwrap();
    let mut credit = [Rat::zero(), Rat::zero(), Rat::zero()];
    let mut covectors = Vec::new();
    for scheduled in &taught {
        let c = scheduled.tangents[0].comparison_credit(&scheduled.ratio).unwrap();
        credit[0] += &c.magnitude;
        credit[1] += &c.produced_phase;
        credit[2] += &c.observed_phase;
        covectors.push(scheduled.ratio.covector().unwrap().logits().to_vec());
    }
    println!(
        "schedule credit: magnitude {}, produced phase {}, observed phase {}",
        credit[0], credit[1], credit[2]
    );
    let parts_at = |epsilon: &Rat| -> [Rat; 3] {
        let scheduled = receiver
            .world_prospect_schedule(
                &declared.on(&present, epsilon),
                &source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                &[&first, &second],
                &[],
            )
            .unwrap();
        let mut total = [Rat::zero(), Rat::zero(), Rat::zero()];
        for (k, scheduled) in scheduled.iter().enumerate() {
            let logits: Vec<StationLogits> = scheduled
                .prospect
                .point
                .features
                .iter()
                .zip(&scheduled.prospect.faces)
                .enumerate()
                .map(|(rank, ((_, _, logits), (_, face)))| StationLogits {
                    station: rank,
                    produced: logits.clone(),
                    observed: face.clone(),
                })
                .collect();
            let p = parts(&covectors[k], &logits);
            for i in 0..3 {
                total[i] += &p[i];
            }
        }
        total
    };
    let mut residuals: Vec<(Rat, [Rat; 3])> = Vec::new();
    for j in 4..9 {
        let epsilon = rat(1, 1i64 << j);
        let up = parts_at(&epsilon);
        let down = parts_at(&-epsilon.clone());
        let two = integer(2) * &epsilon;
        let r: [Rat; 3] = std::array::from_fn(|k| ((&up[k] - &down[k]) / &two - &credit[k]).abs());
        println!("schedule credit: ε = 2^-{j}: central residuals {} {} {}", r[0], r[1], r[2]);
        residuals.push((epsilon, r));
    }
    for k in 0..3 {
        let (first_epsilon, first) = &residuals[0];
        let scaled_first = &first[k] / (first_epsilon * first_epsilon);
        for pair in residuals.windows(2) {
            assert!(
                pair[1].1[k].clone() * integer(2) <= pair[0].1[k],
                "part {k}: the residual halves at least"
            );
        }
        for (epsilon, residual) in &residuals {
            assert!(
                &residual[k] / (epsilon * epsilon) <= &scaled_first * integer(2),
                "part {k}: the residual stays O(ε²)"
            );
        }
    }
}

/// One fixture's schedule loop (§7f): learner and twin each run twelve plain encounters (the
/// receiving relation settles); then each round the learner lands on the chained prospect of the
/// round's two encounters (`u = 1`, then `u = −1`) and runs them; the twin runs them with no landing.
fn schedule_loop(name: &str, second: bool) {
    let (field, base, source) = fixture();
    let theta = if second {
        second_material(&field, base)
    } else {
        Declared::new(&field, base).at(&Rat::zero())
    };
    let make = |theta: &Constitution| {
        if second {
            bound_second(&field, theta.clone(), &source)
        } else {
            bound(&field, theta.clone(), &source, vec![faced_key(&field)])
        }
    };
    let mut learner = make(&theta);
    let mut twin = make(&theta);
    let mut last = plain_passage(&mut learner, &field, &source, 12);
    plain_passage(&mut twin, &field, &source, 12);
    let preparation = actuator(&field);
    let [first, second_wave] = chain_controls();
    let schedule: [&[Rat]; 2] = [&first, &second_wave];
    for round in 0..4 {
        let coordinates = all_coordinates(learner.constitution());
        let decision = match learner.world_schedule_proposal(
            &coordinates,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &schedule,
            &last,
        ) {
            Err(refusal) => format!("proposal refused {refusal:?}"),
            Ok(proposal) => match learner.land_world_descent_on(
                proposal,
                &source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                AdmittedFuture::Schedule(&schedule),
            ) {
                Err(refusal) => format!("landing refused {refusal:?}"),
                Ok(WorldLanding::Unreached(refusal)) => format!("unreached {refusal:?}"),
                Ok(WorldLanding::Read(reading)) => format!(
                    "{:?} at grain raise {:?} (encounters {:?})",
                    reading.decision,
                    reading.grain_raise,
                    reading.waves.iter().map(|w| w.decision).collect::<Vec<_>>()
                ),
            },
        };
        println!("schedule loop ({name}): round {round}: landing {decision}");
        for (k, control) in schedule.iter().enumerate() {
            let probe = learner
                .prepare_probe(&source, &field.receivers()[0], &preparation, &[false, true])
                .unwrap();
            let waves = admitted(&probe, 0);
            let reception = probe.encounter(&waves, control).unwrap();
            let ActionCommunication::Received(received) = reception.reception else {
                panic!("the encounter completes");
            };
            let ratio = &received.comparison.as_ref().unwrap().returned.ratio;
            let (code, excess) = (ratio.code_length().unwrap(), ratio.excess().unwrap());
            last = received;
            let (t_code, t_excess, _, _) = second_comparison(&mut twin, &field, &source, control);
            println!(
                "schedule loop ({name}): round {round}: encounter {k}: learner code {code:?} excess {excess}; twin code {t_code:?} excess {t_excess}"
            );
        }
    }
}

/// **The schedule loop against its twin** (§7f), first fixture.
#[test]
fn the_schedule_loop_is_read_against_its_twin() {
    schedule_loop("first", false);
}

/// The same on the second fixture (§7f).
#[test]
fn the_schedule_loop_is_read_on_a_second_fixture() {
    schedule_loop("second", true);
}

// ---- The cycle of the schedule (the held-carry record §7g) ----

/// **The cycle closes, and its credit is exact** (§7g): after twelve encounters, the closed orbit of
/// the repeated schedule (`u = 1`, `u = −1`) on the present material, with the orbit's credit along
/// one storage direction. On `θ ± εH` (the present receiving relation kept) the two orbit encounters'
/// parts at their frozen covectors confirm the credit to second order on `ε = 2⁻⁴ … 2⁻⁸`.
#[test]
fn the_cycle_closes_and_is_credited_at_its_consumer() {
    let (field, base, source) = fixture();
    let declared = Declared::new(&field, base);
    let direction = declared.storage_direction(&field);
    let mut receiver = bound(
        &field,
        declared.at(&Rat::zero()),
        &source,
        vec![faced_key(&field)],
    );
    plain_passage(&mut receiver, &field, &source, 12);
    let present = receiver.constitution().clone();
    let preparation = actuator(&field);
    let [first, second] = chain_controls();
    let schedule: [&[Rat]; 2] = [&first, &second];
    let reading = receiver
        .world_cycle(
            &present,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &schedule,
            &[direction],
        )
        .unwrap();
    println!("cycle: dimension {}", reading.dimension);
    let mut credit = [Rat::zero(), Rat::zero()];
    let mut covectors = Vec::new();
    for (k, encounter) in reading.encounters.iter().enumerate() {
        credit[0] += &reading.credits[k][0].0;
        credit[1] += &reading.credits[k][0].1;
        covectors.push(encounter.ratio.covector().unwrap().logits().to_vec());
        println!(
            "cycle: orbit encounter {k}: code {:?} excess {}",
            encounter.ratio.code_length().unwrap(),
            encounter.ratio.excess().unwrap()
        );
    }
    println!("cycle credit: classical {}, phase {}", credit[0], credit[1]);
    let parts_at = |epsilon: &Rat| -> [Rat; 2] {
        let reading = receiver
            .world_cycle(
                &declared.on(&present, epsilon),
                &source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                &schedule,
                &[],
            )
            .unwrap();
        let mut total = [Rat::zero(), Rat::zero()];
        for (k, encounter) in reading.encounters.iter().enumerate() {
            let logits: Vec<StationLogits> = encounter
                .prospect
                .point
                .features
                .iter()
                .zip(&encounter.prospect.faces)
                .enumerate()
                .map(|(rank, ((_, _, logits), (_, face)))| StationLogits {
                    station: rank,
                    produced: logits.clone(),
                    observed: face.clone(),
                })
                .collect();
            let p = parts(&covectors[k], &logits);
            total[0] += &p[0];
            total[1] += &p[1] + &p[2];
        }
        total
    };
    let mut residuals: Vec<(Rat, [Rat; 2])> = Vec::new();
    for j in 4..9 {
        let epsilon = rat(1, 1i64 << j);
        let up = parts_at(&epsilon);
        let down = parts_at(&-epsilon.clone());
        let two = integer(2) * &epsilon;
        let r: [Rat; 2] = std::array::from_fn(|k| ((&up[k] - &down[k]) / &two - &credit[k]).abs());
        println!("cycle credit: ε = 2^-{j}: central residuals {} {}", r[0], r[1]);
        residuals.push((epsilon, r));
    }
    for k in 0..2 {
        let (first_epsilon, first) = &residuals[0];
        let scaled_first = &first[k] / (first_epsilon * first_epsilon);
        for pair in residuals.windows(2) {
            assert!(
                pair[1].1[k].clone() * integer(2) <= pair[0].1[k],
                "part {k}: the residual halves at least"
            );
        }
        for (epsilon, residual) in &residuals {
            assert!(
                &residual[k] / (epsilon * epsilon) <= &scaled_first * integer(2),
                "part {k}: the residual stays O(ε²)"
            );
        }
    }
}

/// **Where the passage goes** (§7g): the orbit computed after twelve encounters, against the actual
/// readings of encounters 38 and 39 of the same passage (no landing). Reported as measured: whether
/// the actual readings reach the orbit's at the receiver's grain, and their exact differences.
#[test]
fn the_cycle_is_where_the_passage_goes() {
    let (field, base, source) = fixture();
    let theta = Declared::new(&field, base).at(&Rat::zero());
    let mut receiver = bound(&field, theta, &source, vec![faced_key(&field)]);
    plain_passage(&mut receiver, &field, &source, 12);
    let present = receiver.constitution().clone();
    let preparation = actuator(&field);
    let [first, second] = chain_controls();
    let schedule: [&[Rat]; 2] = [&first, &second];
    let reading = receiver
        .world_cycle(
            &present,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &schedule,
            &[],
        )
        .unwrap();
    plain_passage(&mut receiver, &field, &source, 26);
    for (k, control) in schedule.iter().enumerate() {
        let actual = second_comparison(&mut receiver, &field, &source, control);
        let orbit = &reading.encounters[k].ratio;
        println!(
            "cycle limit: encounter {}: actual code {:?} excess {}; orbit code {:?} excess {}; equal code {}",
            38 + k,
            actual.0,
            actual.1,
            orbit.code_length().unwrap(),
            orbit.excess().unwrap(),
            actual.0 == orbit.code_length().unwrap()
        );
    }
}

/// One fixture's cycle landing over the trajectory (§7g, §7h): learner and twin each run twelve
/// plain encounters; the learner lands once on the fixed-readout cycle of the schedule
/// (`AdmittedFuture::Cycle`); then both run fourteen rounds of the schedule with no further landing.
/// Every round is reported learner against twin, and the last round against the orbits the landing
/// read (the candidate's and the contemporary's).
fn cycle_trajectory(name: &str, second: bool) {
    let (field, base, source) = fixture();
    let theta = if second {
        second_material(&field, base)
    } else {
        Declared::new(&field, base).at(&Rat::zero())
    };
    let make = |theta: &Constitution| {
        if second {
            bound_second(&field, theta.clone(), &source)
        } else {
            bound(&field, theta.clone(), &source, vec![faced_key(&field)])
        }
    };
    let mut learner = make(&theta);
    let mut twin = make(&theta);
    let last = plain_passage(&mut learner, &field, &source, 12);
    plain_passage(&mut twin, &field, &source, 12);
    let preparation = actuator(&field);
    let [first, second_wave] = chain_controls();
    let schedule: [&[Rat]; 2] = [&first, &second_wave];
    let coordinates = all_coordinates(learner.constitution());
    let landing = learner
        .world_cycle_proposal(
            &coordinates,
            &source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            &schedule,
            &last,
        )
        .and_then(|proposal| {
            learner.land_world_descent_on(
                proposal,
                &source,
                &field.receivers()[0],
                &preparation,
                &[false, true],
                AdmittedFuture::Cycle(&schedule),
            )
        });
    match &landing {
        Err(refusal) => {
            println!("cycle trajectory ({name}): landing refused {refusal:?}");
        }
        Ok(WorldLanding::Unreached(refusal)) => {
            println!("cycle trajectory ({name}): landing unreached {refusal:?}");
        }
        Ok(WorldLanding::Read(reading)) => {
            println!(
                "cycle trajectory ({name}): landing {:?} at grain raise {:?} (orbit encounters {:?})",
                reading.decision,
                reading.grain_raise,
                reading.waves.iter().map(|w| w.decision).collect::<Vec<_>>()
            );
            for (k, wave) in reading.waves.iter().enumerate() {
                println!(
                    "cycle trajectory ({name}): orbit encounter {k}: contemporary code {:?} excess {}; candidate code {:?} excess {}",
                    wave.producing.code_length().unwrap(),
                    wave.producing.excess().unwrap(),
                    wave.proposed.code_length().unwrap(),
                    wave.proposed.excess().unwrap()
                );
            }
        }
    }
    for round in 0..14 {
        for (k, control) in schedule.iter().enumerate() {
            let (code, excess, _, _) = second_comparison(&mut learner, &field, &source, control);
            let (t_code, t_excess, _, _) = second_comparison(&mut twin, &field, &source, control);
            println!(
                "cycle trajectory ({name}): round {round}: encounter {k}: learner code {code:?} excess {excess}; twin code {t_code:?} excess {t_excess}"
            );
        }
    }
}

/// **One cycle landing, then the trajectory** (§7g, §7h), first fixture.
#[test]
fn the_cycle_landing_is_read_over_the_trajectory() {
    cycle_trajectory("first", false);
}

/// The same on the second fixture.
#[test]
fn the_cycle_landing_is_read_over_a_second_trajectory() {
    cycle_trajectory("second", true);
}
