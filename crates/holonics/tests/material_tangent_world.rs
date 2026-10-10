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
    WorldLanding, WorldModel,
};
use holonics::hnn::propagation::Operands;
use holonics::hnn::ring::ResonatorMaterial;
use holonics::hnn::word::action::PortPreparation;
use holonics::hnn::field::ConstitutionRead;
use holonics::hnn::word::continuation::{Admitted, MaterialDirection};
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
        .world_proposal(&coordinates, &tangents, &received)
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
            &control,
        )
        .unwrap();
    let reading = match landing {
        WorldLanding::Unreached(refusal) => {
            panic!("the measured landing reaches its lattice; it read: {refusal:?}")
        }
        WorldLanding::Read(reading) => reading,
    };
    println!(
        "world landing: producing code {:?} excess {}; proposed code {:?} excess {}; decision {:?}; deposition work {:?}",
        reading.producing.code_length().unwrap(),
        reading.producing.excess().unwrap(),
        reading.proposed.code_length().unwrap(),
        reading.proposed.excess().unwrap(),
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
        reading.proposed.code_length().unwrap(),
        "the located key's prospect is the actual next comparison"
    );
    assert_eq!(landed.1, reading.proposed.excess().unwrap());
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
    assert_eq!(unlanded.0, reading.producing.code_length().unwrap());
    assert_eq!(unlanded.1, reading.producing.excess().unwrap());
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
        .world_proposal(&coordinates, &tangents, &received)
        .unwrap();
    let landing = receiver
        .land_world_descent(
            proposal,
            source,
            &field.receivers()[0],
            &preparation,
            &[false, true],
            control,
        )
        .unwrap();
    let decision = match landing {
        WorldLanding::Unreached(refusal) => format!("unreached {refusal:?}"),
        WorldLanding::Read(reading) => format!("{:?}", reading.decision),
    };
    (code, excess, decision)
}

/// **The loop over several encounters, against its twin without landings.** Each round on the
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
    for round in 0..4 {
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
    let refused = receiver.world_proposal(&coordinates, &first_tangents, &received);
    assert!(
        matches!(refused, Err(HnnError::Unadmitted { .. })),
        "refused: {:?}",
        refused.as_ref().err()
    );
}
