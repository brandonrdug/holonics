//! The World model's exact fixed-key filter (Refs #73; the receiving-phase record §7, C1b-1).
//!
//! Unit controls on the declared mechanics fixture of `native_action_return.rs`, reused as it
//! stands: the actual World is one medium port Holon, and the model declares keys of the same native
//! kind without reading the World's coefficients. Every expected value is computed independently of
//! the incremental filter it checks: the actual World's own executed states, the batch preimage of
//! every absorbed return from the whole initial state space pushed forward, the closed-form charts
//! of a disconnected key, the closed-form singular midpoint commit of a non-passive key, and a
//! second, model-free receiver run in lockstep. They are unit controls, not learning evidence, and
//! they claim no identification beyond the declared keys.

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::HnnError;
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::phase_family::PhaseImage;
use holonics::hnn::physical::PhysicalReceiver;
use holonics::hnn::physical::action::{
    ActionCommunication, ActionReception, BoundJointWorld, CoupledChange, CoupledProspect,
    HeldReason, KeyState, ModelKey, PreparedPhysicalAction, StateFibre, WaveJointStep, WorldModel,
};
use holonics::hnn::ratio::Face;
use holonics::hnn::ring::ResonatorMaterial;
use holonics::hnn::word::action::{PortPreparation, ProspectiveControl};
use holonics::hnn::{
    Constitution, Current, Encoded, Field, FieldDeclaration, ReceivingRead, RingDeclaration,
    WordOpening,
};
use holonics::holarchy::terrain::KnownTruth;
use holonics::holon::element::{Pump, PumpSchedule};
use holonics::holon::law::{ReferenceHolon, Scheme};
use holonics::holon::{Holon, HolonState, PortHolon};
use holonics::navigator::Clock;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::SymmetricForm;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::face::GrainCell;
use holonics::receiver::receipt::{ReceiptLaw, RegionChart};
use holonics::receiver::reception::{JointLaw, ReceiverFace};
use num_bigint::BigInt;
use num_traits::{One, Zero};

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

/// `Q = diag(−2·I, I)`: with `Y = 2` and `h = 1` the midpoint commit `1 − ½(Ω − B Y⁻¹ Bᵀ) Q`
/// annihilates `e_0 − e_N` (checked in closed form below), so the Robin-coupled commit is singular.
fn singular_storage() -> Vec<Rat> {
    (0..2 * N)
        .map(|i| if i < N { integer(-2) } else { integer(1) })
        .collect()
}

/// The World's passive medium, pumped to the singular storage at every odd commit.
fn pumped(field: &Field) -> Holon {
    medium(&unit_storage(), source_input(true))
        .with_pump(Pump {
            schedule: PumpSchedule::new(vec![
                diagonal_form(&unit_storage()),
                diagonal_form(&singular_storage()),
            ])
            .unwrap(),
            clock: Clock::ring(field.step().clone(), 2).unwrap(),
        })
        .unwrap()
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

fn receiver<'f>(field: &'f Field, theta: Constitution) -> PhysicalReceiver<'f> {
    PhysicalReceiver::new(field, theta, Current::at_rest(field), WordOpening::Rest).unwrap()
}

/// One executed World step as the receipt reports it: `(a, b)` and the World's reached state.
struct Executed {
    incident: Vec<Rat>,
    reflected: Vec<Rat>,
    next: HolonState,
    /// The World's raw face after the step: the vector the encounter reads at its grain when the
    /// step's epoch is compared.
    face: Vec<Rat>,
}

fn executed(steps: &[WaveJointStep]) -> Vec<Executed> {
    steps
        .iter()
        .map(|step| Executed {
            incident: step.incident.clone(),
            reflected: step.reflected.clone(),
            next: step.joint.next_state(),
            face: step.joint.face().to_vec(),
        })
        .collect()
}

/// One actual encounter of the fixture's action (`native_action_return.rs`'s request).
fn encounter(
    receiver: &mut PhysicalReceiver<'_>,
    field: &Field,
    source: &Encoded,
) -> Result<ActionCommunication, HnnError> {
    let preparation = PortPreparation::new(field, 0, ExactRatMatrix::identity(N).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); N],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    receiver
        .prepare_action(
            source,
            &field.receivers()[0],
            &preparation,
            &request,
            &[false, true],
        )
        .unwrap()
        .encounter()
}

/// The executed steps of a completed or interrupted encounter; none for a held one.
fn steps_of(communication: &ActionCommunication) -> Vec<Executed> {
    match communication {
        ActionCommunication::Received(received) => executed(received.encounter.steps()),
        ActionCommunication::Interrupted(interrupted) => {
            executed(interrupted.encounter.partial.steps())
        }
        ActionCommunication::Held { .. } => Vec::new(),
    }
}

fn act(receiver: &mut PhysicalReceiver<'_>, field: &Field, source: &Encoded) -> Vec<Executed> {
    steps_of(&encounter(receiver, field, source).unwrap())
}

fn plus(left: &[Rat], right: &[Rat]) -> Vec<Rat> {
    left.iter().zip(right).map(|(a, b)| a + b).collect()
}

fn minus(left: &[Rat], right: &[Rat]) -> Vec<Rat> {
    left.iter().zip(right).map(|(a, b)| a - b).collect()
}

fn dot(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| sum + a * b)
}

fn from_columns(rows: usize, columns: &[Vec<Rat>]) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        rows,
        columns.len(),
        (0..rows)
            .map(|i| columns.iter().map(|column| column[i].clone()).collect())
            .collect(),
    )
    .unwrap()
}

/// Whether a state lies in an affine fibre.
fn contains(fibre: &StateFibre, state: &[Rat]) -> bool {
    from_columns(fibre.point.len(), &fibre.directions)
        .preimage_fibre(&minus(state, &fibre.point))
        .unwrap()
        .is_some()
}

/// Whether two affine fibres are one set: equal spans, and points that differ inside them.
fn same_fibre(left: &StateFibre, right: &StateFibre) -> bool {
    let sigma = left.point.len();
    let rank = |columns: &[Vec<Rat>]| from_columns(sigma, columns).rank().unwrap();
    let joint: Vec<Vec<Rat>> = left
        .directions
        .iter()
        .chain(&right.directions)
        .cloned()
        .collect();
    let span = rank(&left.directions);
    span == rank(&right.directions) && span == rank(&joint) && contains(left, &right.point)
}

/// **The batch fibre**: the complete preimage of every absorbed return from the whole initial state
/// space, solved at once on the stacked charts, then pushed forward to the reached crossing. It
/// shares the charts with the filter and nothing else.
fn batch_fibre(key: &ModelKey, founded: u64, steps: &[Executed]) -> StateFibre {
    let sigma = key.extent();
    let mut transport = ExactRatMatrix::identity(sigma).unwrap();
    let mut forced = vec![Rat::zero(); sigma];
    let mut rows: Vec<Vec<Rat>> = Vec::new();
    let mut target = Vec::new();
    for (t, step) in steps.iter().enumerate() {
        let charts = key.charts(founded + t as u64).unwrap();
        let observed = charts.p.multiply(&transport).unwrap();
        for i in 0..observed.rows() {
            rows.push(
                (0..sigma)
                    .map(|j| observed.get(i, j).unwrap().clone())
                    .collect(),
            );
        }
        let offset = plus(
            &charts.p.apply(&forced).unwrap(),
            &charts.q.apply(&step.incident).unwrap(),
        );
        target.extend(minus(&step.reflected, &offset));
        transport = charts.f.multiply(&transport).unwrap();
        forced = plus(
            &charts.f.apply(&forced).unwrap(),
            &charts.g.apply(&step.incident).unwrap(),
        );
    }
    let (initial, kernel) = ExactRatMatrix::shaped(rows.len(), sigma, rows)
        .unwrap()
        .preimage_fibre(&target)
        .unwrap()
        .expect("the World's own key reproduces its returns");
    StateFibre {
        point: plus(&transport.apply(&initial).unwrap(), &forced),
        directions: kernel
            .iter()
            .map(|direction| transport.apply(direction).unwrap())
            .collect(),
    }
}

/// The declared reading of the memory's bits, recomputed from its public states.
fn declared_bits(model: &WorldModel) -> u64 {
    let value = |x: &Rat| x.numer().bits() + x.denom().bits();
    let clock = |t: u64| u64::from(u64::BITS - t.leading_zeros());
    let fibre = |f: &StateFibre| {
        f.point
            .iter()
            .chain(f.directions.iter().flatten())
            .map(value)
            .sum::<u64>()
    };
    model
        .states()
        .iter()
        .map(|state| {
            2 + match state {
                KeyState::Live(f) => fibre(f),
                KeyState::Held {
                    fibre: f,
                    certified_tick,
                    ..
                } => fibre(f) + clock(*certified_tick) + 1,
                KeyState::Incompatible { tick, annihilator } => {
                    clock(*tick) + annihilator.iter().map(value).sum::<u64>()
                }
            }
        })
        .sum::<u64>()
        + clock(model.tick())
}

#[test]
fn the_world_key_reproduces_every_actual_step_and_its_fibre_is_the_batch_preimage() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    let actual = world(
        &field,
        source.part(0..0).unwrap(),
        medium(&unit_storage(), source_input(true)),
    );
    let founded = actual.state().clone();
    receiver.bind_world(actual).unwrap();
    let truth = key(&field, medium(&unit_storage(), source_input(true)));
    receiver
        .bind_world_model(WorldModel::found(vec![truth.clone()], founded.commit).unwrap())
        .unwrap();
    let mut steps = Vec::new();
    for _ in 0..3 {
        steps.extend(act(&mut receiver, &field, &source));
        // The memory's tick is the actual World's after every encounter.
        assert_eq!(
            receiver.world_model().unwrap().tick(),
            receiver.participating_world().unwrap().state().commit
        );
    }
    assert!(!steps.is_empty());
    let reached = receiver.participating_world().unwrap().state().clone();
    assert_eq!(reached.commit, founded.commit + steps.len() as u64);
    // The key's charts reproduce every actual transition and return of the World.
    let mut state = founded.configuration.clone();
    for (t, step) in steps.iter().enumerate() {
        let charts = truth.charts(founded.commit + t as u64).unwrap();
        assert_eq!(
            plus(
                &charts.p.apply(&state).unwrap(),
                &charts.q.apply(&step.incident).unwrap()
            ),
            step.reflected
        );
        state = plus(
            &charts.f.apply(&state).unwrap(),
            &charts.g.apply(&step.incident).unwrap(),
        );
        assert_eq!(state, step.next.configuration);
    }
    let model = receiver.world_model().unwrap();
    assert_eq!(receiver.resident().world_model(), Some(model));
    let KeyState::Live(fibre) = &model.states()[0] else {
        panic!("the World's own key stays live: {:?}", model.states()[0]);
    };
    assert!(contains(fibre, &reached.configuration));
    assert!(same_fibre(
        fibre,
        &batch_fibre(&truth, founded.commit, &steps)
    ));
    if fibre.directions.is_empty() {
        assert_eq!(fibre.point, reached.configuration);
    }
}

#[test]
fn a_disconnected_key_is_eliminated_only_by_its_exact_annihilator() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    let actual = world(
        &field,
        source.part(0..0).unwrap(),
        medium(&unit_storage(), source_input(true)),
    );
    let founded = actual.state().commit;
    receiver.bind_world(actual).unwrap();
    let disconnected = key(&field, medium(&unit_storage(), source_input(false)));
    // Its closed-form charts: no state reaches its ports and every wave returns whole.
    let charts = disconnected.charts(founded).unwrap();
    assert_eq!(charts.p, ExactRatMatrix::zero(N, 2 * N).unwrap());
    assert_eq!(charts.g, ExactRatMatrix::zero(2 * N, N).unwrap());
    assert_eq!(charts.q, ExactRatMatrix::identity(N).unwrap());
    receiver
        .bind_world_model(WorldModel::found(vec![disconnected], founded).unwrap())
        .unwrap();
    let mut steps = Vec::new();
    for _ in 0..2 {
        steps.extend(act(&mut receiver, &field, &source));
    }
    // The first actual step whose return is not its incident wave eliminates it, and none before.
    let first = steps
        .iter()
        .position(|step| step.reflected != step.incident)
        .expect("the actual World's ports carry flow");
    let model = receiver.world_model().unwrap();
    let KeyState::Incompatible { tick, annihilator } = &model.states()[0] else {
        panic!("eliminated by its annihilator: {:?}", model.states()[0]);
    };
    assert_eq!(*tick, founded + first as u64);
    // With P = 0 every covector annihilates P N; the witness pairs nonzero with b − Q a = b − a.
    assert_eq!(annihilator.len(), N);
    assert!(
        !dot(
            annihilator,
            &minus(&steps[first].reflected, &steps[first].incident)
        )
        .is_zero()
    );
    assert_eq!(model.tick(), founded + steps.len() as u64);
    assert!(model.predict(0, &[vec![Rat::zero(); N]]).is_err());
}

#[test]
fn a_non_passive_key_is_held_at_its_certified_cut_while_the_tick_advances() {
    let (field, theta, source) = fixture();
    // In closed form, independently of the owner: at h = 1 and Y = 2, 1 − ½(Ω − B Y⁻¹ Bᵀ) Q
    // annihilates e_0 − e_N for Q = diag(−2·I, I).
    assert_eq!(*field.step(), integer(1));
    let omega = gyrator();
    let storage = singular_storage();
    let commit = ExactRatMatrix::new(
        (0..2 * N)
            .map(|i| {
                (0..2 * N)
                    .map(|j| {
                        let wave = if i == j && i < N {
                            rat(1, 2)
                        } else {
                            Rat::zero()
                        };
                        let a = (omega.get(i, j).unwrap() - &wave) * &storage[j];
                        let identity = if i == j { Rat::one() } else { Rat::zero() };
                        identity - a / integer(2)
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let mut kernel = vec![Rat::zero(); 2 * N];
    kernel[0] = integer(1);
    kernel[N] = integer(-1);
    assert!(commit.apply(&kernel).unwrap().iter().all(Zero::is_zero));

    let mut receiver = receiver(&field, theta);
    let actual = world(
        &field,
        source.part(0..0).unwrap(),
        medium(&unit_storage(), source_input(true)),
    );
    let founded = actual.state().commit;
    receiver.bind_world(actual).unwrap();
    let non_passive = key(&field, medium(&singular_storage(), source_input(true)));
    assert!(non_passive.charts(founded).is_err());
    let truth = key(&field, medium(&unit_storage(), source_input(true)));
    receiver
        .bind_world_model(WorldModel::found(vec![non_passive, truth], founded).unwrap())
        .unwrap();
    let mut executed = 0;
    for _ in 0..2 {
        executed += act(&mut receiver, &field, &source).len();
    }
    assert!(executed > 0);
    let model = receiver.world_model().unwrap();
    assert_eq!(model.tick(), founded + executed as u64);
    assert_eq!(
        model.states()[0],
        KeyState::Held {
            fibre: StateFibre::whole(2 * N),
            certified_tick: founded,
            reason: HeldReason::Charts,
        }
    );
    assert!(matches!(model.states()[1], KeyState::Live(_)));
    // A held span is not a current-crossing alternative.
    assert!(model.predict(0, &[vec![Rat::zero(); N]]).is_err());
    assert!(model.predict(1, &[vec![Rat::zero(); N]]).is_ok());
}

#[test]
fn the_return_image_separates_the_free_and_forced_responses_and_holds_the_actual_returns() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    let actual = world(
        &field,
        source.part(0..0).unwrap(),
        medium(&unit_storage(), source_input(true)),
    );
    let founded = actual.state().commit;
    receiver.bind_world(actual).unwrap();
    let truth = key(&field, medium(&unit_storage(), source_input(true)));
    receiver
        .bind_world_model(WorldModel::found(vec![truth.clone()], founded).unwrap())
        .unwrap();
    act(&mut receiver, &field, &source);
    // The model before a later encounter of at least two steps, and the incident word that
    // encounter actually applied.
    let mut attempts = 0;
    let (before, steps) = loop {
        let before = receiver.world_model().unwrap().clone();
        let steps = act(&mut receiver, &field, &source);
        attempts += 1;
        if steps.len() >= 2 || attempts == 2 {
            break (before, steps);
        }
    };
    assert!(steps.len() >= 2);
    let word: Vec<Vec<Rat>> = steps.iter().map(|step| step.incident.clone()).collect();
    let image = before.predict(0, &word).unwrap();
    let KeyState::Live(fibre) = &before.states()[0] else {
        panic!("live before the encounter");
    };
    let t = before.tick();
    assert_eq!(image.tick, t);
    assert_eq!(
        (image.free.len(), image.forced.len()),
        (word.len(), word.len())
    );
    assert_eq!(image.directions.len(), fibre.directions.len());
    // The first two steps by hand: the first return is P_T c + Q_T a_T; the second carries
    // F_T and G_T a_T through P_(T+1).
    let (now, next) = (truth.charts(t).unwrap(), truth.charts(t + 1).unwrap());
    assert_eq!(image.free[0], now.p.apply(&fibre.point).unwrap());
    assert_eq!(image.forced[0], now.q.apply(&word[0]).unwrap());
    assert_eq!(
        image.free[1],
        next.p.apply(&now.f.apply(&fibre.point).unwrap()).unwrap()
    );
    assert_eq!(
        image.forced[1],
        plus(
            &next.p.apply(&now.g.apply(&word[0]).unwrap()).unwrap(),
            &next.q.apply(&word[1]).unwrap()
        )
    );
    for (r, direction) in fibre.directions.iter().enumerate() {
        assert_eq!(image.directions[r][0], now.p.apply(direction).unwrap());
    }
    // One k moves every step together, and some k reproduces every actual return.
    let mut rows = Vec::new();
    let mut target = Vec::new();
    for (j, step) in steps.iter().enumerate() {
        for i in 0..N {
            rows.push(
                image
                    .directions
                    .iter()
                    .map(|direction| direction[j][i].clone())
                    .collect::<Vec<Rat>>(),
            );
        }
        target.extend(minus(
            &step.reflected,
            &plus(&image.free[j], &image.forced[j]),
        ));
    }
    let stacked = ExactRatMatrix::shaped(rows.len(), fibre.directions.len(), rows).unwrap();
    assert!(stacked.preimage_fibre(&target).unwrap().is_some());
}

#[test]
fn the_resident_charges_the_models_current_bits_at_every_encounter() {
    let (field, theta, source) = fixture();
    let mut charged = receiver(&field, theta.clone());
    let mut bare = receiver(&field, theta);
    for receiver in [&mut charged, &mut bare] {
        receiver
            .bind_world(world(
                &field,
                source.part(0..0).unwrap(),
                medium(&unit_storage(), source_input(true)),
            ))
            .unwrap();
    }
    let keys = vec![
        key(&field, medium(&unit_storage(), source_input(true))),
        key(&field, medium(&unit_storage(), source_input(false))),
        key(&field, medium(&singular_storage(), source_input(true))),
    ];
    charged
        .bind_world_model(WorldModel::found(keys, 0).unwrap())
        .unwrap();
    let mut readings = Vec::new();
    for round in 0..=2 {
        if round > 0 {
            let with = act(&mut charged, &field, &source);
            let without = act(&mut bare, &field, &source);
            // The model reads the passage and never steers it.
            assert_eq!(with.len(), without.len());
            for (a, b) in with.iter().zip(&without) {
                assert_eq!((&a.incident, &a.reflected), (&b.incident, &b.reflected));
            }
        }
        let model = charged.world_model().unwrap();
        assert_eq!(model.current_bits(), declared_bits(model));
        assert_eq!(
            charged.resident().state_bits(),
            bare.resident().state_bits() + model.current_bits()
        );
        readings.push(model.current_bits());
    }
    // No fixed size: the founding memory is not what the absorbed passage leaves.
    assert_ne!(readings[0], readings[2]);
}

#[test]
fn an_interrupted_encounter_is_absorbed_through_its_executed_steps_without_rollback() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    let actual = world(&field, source.part(0..0).unwrap(), pumped(&field));
    let founded = actual.state().clone();
    receiver.bind_world(actual).unwrap();
    let truth = key(&field, pumped(&field));
    receiver
        .bind_world_model(WorldModel::found(vec![truth.clone()], founded.commit).unwrap())
        .unwrap();
    // The World's step at its first odd commit cannot be solved, so some encounter stops there.
    let mut steps = Vec::new();
    let mut stopped = false;
    for _ in 0..3 {
        let communication = encounter(&mut receiver, &field, &source);
        // Whatever the consumer returns after the World's refusal, the executed steps are
        // absorbed: the memory's tick is the actual World's, neither rewound.
        assert_eq!(
            receiver.world_model().unwrap().tick(),
            receiver.participating_world().unwrap().state().commit
        );
        match communication {
            Ok(ActionCommunication::Received(received)) => {
                steps.extend(executed(received.encounter.steps()));
            }
            Ok(ActionCommunication::Interrupted(interrupted)) => {
                steps.extend(executed(interrupted.encounter.partial.steps()));
                stopped = true;
                break;
            }
            Ok(ActionCommunication::Held { .. }) => {}
            Err(_) => {
                stopped = true;
                break;
            }
        }
    }
    assert!(stopped);
    let reached = receiver.participating_world().unwrap().state().clone();
    assert_eq!(reached.commit % 2, 1);
    let model = receiver.world_model().unwrap();
    assert_eq!(model.tick(), reached.commit);
    let KeyState::Live(fibre) = &model.states()[0] else {
        panic!("the World's own key stays live: {:?}", model.states()[0]);
    };
    assert!(contains(fibre, &reached.configuration));
    if steps.len() as u64 == reached.commit - founded.commit {
        assert_eq!(steps.last().map(|step| &step.next), Some(&reached));
        assert!(same_fibre(
            fibre,
            &batch_fibre(&truth, founded.commit, &steps)
        ));
    }
}

#[test]
fn binding_is_refused_without_a_world_off_its_tick_or_off_the_source_frame() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    let truth = || key(&field, medium(&unit_storage(), source_input(true)));
    // No World is bound yet.
    assert!(
        receiver
            .bind_world_model(WorldModel::found(vec![truth()], 0).unwrap())
            .is_err()
    );
    receiver
        .bind_world(world(
            &field,
            source.part(0..0).unwrap(),
            medium(&unit_storage(), source_input(true)),
        ))
        .unwrap();
    // A memory founded off the World's actual tick.
    assert!(
        receiver
            .bind_world_model(WorldModel::found(vec![truth()], 1).unwrap())
            .is_err()
    );
    // A key off the source's wave frame: another admittance, another step, another port count.
    let law = |step: Rat| {
        ReferenceHolon::new(
            medium(&unit_storage(), source_input(true)),
            step,
            Scheme::Midpoint,
        )
        .unwrap()
    };
    let other_admittance = ModelKey::declare(law(integer(1)), vec![integer(3); N]).unwrap();
    let other_step = ModelKey::declare(law(rat(1, 2)), admittance()).unwrap();
    let one_port = ModelKey::declare(
        ReferenceHolon::new(
            medium(
                &unit_storage(),
                ExactRatMatrix::new(
                    (0..2 * N)
                        .map(|i| vec![if i == 0 { integer(1) } else { Rat::zero() }])
                        .collect(),
                )
                .unwrap(),
            ),
            integer(1),
            Scheme::Midpoint,
        )
        .unwrap(),
        vec![integer(2)],
    )
    .unwrap();
    for off in [other_admittance, other_step, one_port] {
        assert!(
            receiver
                .bind_world_model(WorldModel::found(vec![truth(), off], 0).unwrap())
                .is_err()
        );
    }
    assert!(receiver.world_model().is_none());
    receiver
        .bind_world_model(WorldModel::found(vec![truth()], 0).unwrap())
        .unwrap();
    // One model only.
    assert!(
        receiver
            .bind_world_model(WorldModel::found(vec![truth()], 0).unwrap())
            .is_err()
    );
    assert_eq!(receiver.world_model().unwrap().keys(), &[truth()]);
}

/// The stacked system of one coupled prospect against an encounter: every actual `(a_t, b_t)`,
/// where given the actual receiving logits of one compared station, and where given the World's raw
/// face at one compared station. Columns are the fibre directions, the target is actual minus point;
/// `None` when the shapes do not meet.
fn stacked(
    prospect: &CoupledProspect,
    steps: &[Executed],
    station: Option<(usize, &[Rat])>,
    face: Option<(usize, &[Rat])>,
) -> Option<(ExactRatMatrix, Vec<Rat>)> {
    if prospect.point.waves.len() != steps.len() {
        return None;
    }
    let mut rows = Vec::new();
    let mut target = Vec::new();
    for (t, step) in steps.iter().enumerate() {
        let (incident, reflected) = &prospect.point.waves[t];
        for (i, actual) in step.incident.iter().enumerate() {
            rows.push(
                prospect
                    .directions
                    .iter()
                    .map(|direction| direction.waves[t].0[i].clone())
                    .collect::<Vec<Rat>>(),
            );
            target.push(actual - &incident[i]);
        }
        for (i, actual) in step.reflected.iter().enumerate() {
            rows.push(
                prospect
                    .directions
                    .iter()
                    .map(|direction| direction.waves[t].1[i].clone())
                    .collect::<Vec<Rat>>(),
            );
            target.push(actual - &reflected[i]);
        }
    }
    if let Some((compared, actual)) = station {
        let position = prospect
            .point
            .features
            .iter()
            .position(|(read, _, _)| *read == compared)?;
        let predicted = &prospect.point.features[position].2;
        if predicted.len() != actual.len() {
            return None;
        }
        for (i, value) in actual.iter().enumerate() {
            rows.push(
                prospect
                    .directions
                    .iter()
                    .map(|direction| direction.features[position].2[i].clone())
                    .collect::<Vec<Rat>>(),
            );
            target.push(value - &predicted[i]);
        }
    }
    if let Some((compared, actual)) = face {
        let position = prospect
            .faces
            .iter()
            .position(|(read, _)| *read == compared)?;
        let predicted = &prospect.faces[position].1;
        if predicted.len() != actual.len() {
            return None;
        }
        for (i, value) in actual.iter().enumerate() {
            rows.push(
                prospect
                    .directions
                    .iter()
                    .map(|direction| direction.faces[position].1[i].clone())
                    .collect::<Vec<Rat>>(),
            );
            target.push(value - &predicted[i]);
        }
    }
    Some((
        ExactRatMatrix::shaped(rows.len(), prospect.directions.len(), rows).unwrap(),
        target,
    ))
}

/// Whether one `k` carries a coupled prospect's point onto every given actual value at once.
fn holds(
    prospect: &CoupledProspect,
    steps: &[Executed],
    station: Option<(usize, &[Rat])>,
    face: Option<(usize, &[Rat])>,
) -> bool {
    stacked(prospect, steps, station, face)
        .is_some_and(|(matrix, target)| matrix.preimage_fibre(&target).unwrap().is_some())
}

/// The native-only prediction of a station's receiving logits under the unique control: the
/// baseline plus the response, which is how the control was solved (`ProspectiveControl`).
fn native_logits(control: &ProspectiveControl, station: usize, u: &[Rat]) -> Vec<Rat> {
    plus(
        &control.baseline()[station],
        &control.response().apply(u).unwrap(),
    )
}

#[test]
fn the_world_keys_coupled_prospect_holds_the_actual_encounter_before_it_runs() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    receiver
        .bind_world(world(
            &field,
            source.part(0..0).unwrap(),
            medium(&unit_storage(), source_input(true)),
        ))
        .unwrap();
    let keys = vec![
        key(&field, medium(&unit_storage(), source_input(true))),
        key(&field, medium(&unit_storage(), source_input(false))),
        key(&field, medium(&singular_storage(), source_input(true))),
    ];
    receiver
        .bind_world_model(WorldModel::found(keys, 0).unwrap())
        .unwrap();
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(N).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); N],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    let mut predicted = 0;
    let mut read_features = 0;
    for _ in 0..3 {
        let before = receiver.world_model().unwrap().clone();
        let prepared = receiver
            .prepare_action(
                &source,
                &field.receivers()[0],
                &preparation,
                &request,
                &[false, true],
            )
            .unwrap();
        let Some(control) = prepared.prospective().unique_control().map(<[Rat]>::to_vec) else {
            // A plural or obstructed control releases nothing, so nothing is predicted.
            assert!(prepared.world_prospect().is_err());
            assert!(matches!(
                prepared.encounter().unwrap(),
                ActionCommunication::Held { .. }
            ));
            continue;
        };
        let native = native_logits(prepared.prospective(), 1, &control);
        let prospects = prepared.world_prospect().unwrap();
        assert_eq!(prospects.len(), 3);
        // The prospect reads and writes nothing actual: the prepared Word still executes.
        let communication = prepared.encounter().unwrap();
        let steps = steps_of(&communication);
        // The encounter's own blind read of the compared station, under the producing frame: the
        // opening's receiving map and lift, which no reception publication moves.
        let actual_logits = match &communication {
            ActionCommunication::Received(received) => received
                .boundary
                .readings()
                .iter()
                .find(|read| read.station == 1)
                .map(|read| read.read.logits.clone()),
            _ => None,
        };
        assert!(!steps.is_empty());
        let after = receiver.world_model().unwrap();
        assert_eq!(after.tick(), before.tick() + steps.len() as u64);
        // The World's own key is live, and one k carries its prospect onto the actual waves.
        let truth = prospects[0].as_ref().unwrap();
        assert_eq!(truth.tick, before.tick());
        // One k carries the waves and the native readout together.
        let station = actual_logits.as_deref().map(|logits| (1, logits));
        assert!(holds(truth, &steps, station, None));
        if station.is_some() {
            read_features += 1;
        }
        if truth.directions.is_empty() {
            for (step, (incident, reflected)) in steps.iter().zip(&truth.point.waves) {
                assert_eq!((&step.incident, &step.reflected), (incident, reflected));
            }
            if let Some(logits) = &actual_logits {
                assert_eq!(&truth.point.features[0].2, logits);
            }
        }
        // The disconnected key, while live, returns every wave whole; its state reaches nothing,
        // so its directions change nothing, and its native readout is the native-only prediction.
        match &before.states()[1] {
            KeyState::Live(_) => {
                let disconnected = prospects[1].as_ref().unwrap();
                assert!(
                    disconnected
                        .point
                        .waves
                        .iter()
                        .all(|(incident, reflected)| incident == reflected)
                );
                assert!(disconnected.directions.iter().all(|direction| {
                    direction
                        .waves
                        .iter()
                        .flat_map(|(a, b)| a.iter().chain(b))
                        .chain(
                            direction
                                .features
                                .iter()
                                .flat_map(|(_, f, l)| f.iter().chain(l)),
                        )
                        .all(Zero::is_zero)
                }));
                let [(station, _, logits)] = &disconnected.point.features[..] else {
                    panic!("one compared station");
                };
                assert_eq!(*station, 1);
                assert_eq!(logits, &native);
            }
            _ => assert!(prospects[1].is_err()),
        }
        // The non-passive key's charts are refused before any image, live or held.
        assert!(prospects[2].is_err());
        predicted += 1;
    }
    assert!(predicted > 0);
    // The compared station's actual readout was measured against the true key's at least once.
    assert!(read_features > 0);
}

/// The fixture's action prepared on a receiver, before its encounter.
fn prepare<'r, 'f>(
    receiver: &'r mut PhysicalReceiver<'f>,
    field: &Field,
    source: &Encoded,
    preparation: &PortPreparation,
    request: &[Vec<Rat>],
) -> PreparedPhysicalAction<'r, 'f> {
    receiver
        .prepare_action(
            source,
            &field.receivers()[0],
            preparation,
            request,
            &[false, true],
        )
        .unwrap()
}

#[test]
fn a_prospect_is_refused_without_a_world_model_and_moves_no_participant() {
    let (field, theta, source) = fixture();
    let mut read = receiver(&field, theta.clone());
    let mut unread = receiver(&field, theta);
    for receiver in [&mut read, &mut unread] {
        receiver
            .bind_world(world(
                &field,
                source.part(0..0).unwrap(),
                medium(&unit_storage(), source_input(true)),
            ))
            .unwrap();
    }
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(N).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); N],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    // Without a bound model the read refuses as a whole, and the action still executes.
    {
        let prepared = prepare(&mut read, &field, &source, &preparation, &request);
        assert!(prepared.world_prospect().is_err());
        steps_of(&prepared.encounter().unwrap());
    }
    steps_of(
        &prepare(&mut unread, &field, &source, &preparation, &request)
            .encounter()
            .unwrap(),
    );
    let tick = read.participating_world().unwrap().state().commit;
    assert_eq!(unread.participating_world().unwrap().state().commit, tick);
    for receiver in [&mut read, &mut unread] {
        receiver
            .bind_world_model(
                WorldModel::found(
                    vec![key(&field, medium(&unit_storage(), source_input(true)))],
                    tick,
                )
                .unwrap(),
            )
            .unwrap();
    }
    // With the model, two reads before the encounter return one exact prospect, and the
    // encounter and the memory then equal those of a receiver that never read it.
    for _ in 0..2 {
        let prepared = prepare(&mut read, &field, &source, &preparation, &request);
        if prepared.prospective().unique_control().is_some() {
            let first = prepared.world_prospect().unwrap();
            let second = prepared.world_prospect().unwrap();
            assert_eq!(first[0].as_ref().unwrap(), second[0].as_ref().unwrap());
        }
        let with = steps_of(&prepared.encounter().unwrap());
        let without = steps_of(
            &prepare(&mut unread, &field, &source, &preparation, &request)
                .encounter()
                .unwrap(),
        );
        assert_eq!(with.len(), without.len());
        for (a, b) in with.iter().zip(&without) {
            assert_eq!(
                (&a.incident, &a.reflected, &a.next),
                (&b.incident, &b.reflected, &b.next)
            );
        }
        assert_eq!(read.world_model().unwrap(), unread.world_model().unwrap());
    }
}

#[test]
fn a_key_with_the_worlds_face_covers_its_observed_face_and_a_wrong_face_does_not() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    receiver
        .bind_world(world(
            &field,
            source.part(0..0).unwrap(),
            medium(&unit_storage(), source_input(true)),
        ))
        .unwrap();
    let law = || key(&field, medium(&unit_storage(), source_input(true)));
    // The World's own face reads the receiver's coordinates; the wrong one adds the offset e_0.
    let mut offset = vec![Rat::zero(); N];
    offset[0] = integer(1);
    let wrong = ReceiverFace::new(
        ExactRatMatrix::zero(N, N).unwrap(),
        ExactRatMatrix::identity(N).unwrap(),
        offset,
        vec![Rat::zero(); N],
    )
    .unwrap();
    let keys = vec![
        law()
            .with_face(ReceiverFace::receiver_state(N, N).unwrap(), N)
            .unwrap(),
        law().with_face(wrong, N).unwrap(),
        law(),
    ];
    // A face with a chart rate, or split outside the storage, is refused.
    assert!(
        law()
            .with_face(
                ReceiverFace::new(
                    ExactRatMatrix::zero(N, N).unwrap(),
                    ExactRatMatrix::identity(N).unwrap(),
                    vec![Rat::zero(); N],
                    vec![integer(1); N],
                )
                .unwrap(),
                N,
            )
            .is_err()
    );
    assert!(
        law()
            .with_face(ReceiverFace::receiver_state(N, N).unwrap(), 3 * N)
            .is_err()
    );
    receiver
        .bind_world_model(WorldModel::found(keys, 0).unwrap())
        .unwrap();
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(N).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); N],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    let (mut covered, mut separated, mut read_natively) = (0, 0, 0);
    for _ in 0..3 {
        let prepared = prepare(&mut receiver, &field, &source, &preparation, &request);
        if prepared.prospective().unique_control().is_none() {
            assert!(matches!(
                prepared.encounter().unwrap(),
                ActionCommunication::Held { .. }
            ));
            continue;
        }
        let epoch = prepared.receiving_phases().epochs().nth(1).unwrap();
        let prospects = prepared.world_prospect().unwrap();
        let communication = prepared.encounter().unwrap();
        let steps = steps_of(&communication);
        let actual = &steps[epoch - 1].face;
        // The encounter's own blind read of the compared station, in the producing frame.
        let native = match &communication {
            ActionCommunication::Received(received) => received
                .boundary
                .readings()
                .iter()
                .find(|read| read.station == 1)
                .map(|read| read.read.logits.clone()),
            _ => None,
        };
        let station = native.as_deref().map(|logits| (1, logits));
        if station.is_some() {
            read_natively += 1;
        }
        let truth = prospects[0].as_ref().unwrap();
        let faced = prospects[1].as_ref().unwrap();
        let faceless = prospects[2].as_ref().unwrap();
        // Only declared faces are predicted, at the compared station only.
        assert_eq!(truth.faces.len(), 1);
        assert_eq!(faced.faces.len(), 1);
        assert!(faceless.faces.is_empty());
        // The wrong face is the true one shifted by its offset, with the same directions.
        let mut shifted = truth.faces[0].1.clone();
        shifted[0] += integer(1);
        assert_eq!(faced.faces[0].1, shifted);
        // One k carries the World's own face key onto all three actual values together: the
        // waves, the native receiving logits and the observed raw face.
        let face = Some((1, actual.as_slice()));
        assert!(holds(truth, &steps, station, face));
        covered += 1;
        // Where the waves alone fix k, the true port law with the wrong face fails the same
        // combined check: no k that the waves admit can also absorb the face's offset.
        let (matrix, _) = stacked(truth, &steps, None, None).unwrap();
        if matrix.rank().unwrap() == truth.directions.len() {
            assert!(!holds(faced, &steps, station, face));
            separated += 1;
        }
        // An undeclared face is neutral: the faceless key carries no face rows in any direction,
        // predicts the same waves and native readout as the same law with a face, and holds the
        // actual waves and native readout with no face row at all.
        assert!(
            faceless
                .directions
                .iter()
                .all(|direction| direction.faces.is_empty())
        );
        assert_eq!(faceless.point, truth.point);
        for (bare, faced_direction) in faceless.directions.iter().zip(&truth.directions) {
            assert_eq!(
                (&bare.waves, &bare.features),
                (&faced_direction.waves, &faced_direction.features)
            );
        }
        assert!(holds(faceless, &steps, station, None));
    }
    assert!(covered > 0);
    assert!(separated > 0);
    // The combined check read the actual native readout at least once, so it is never vacuous.
    assert!(read_natively > 0);
}

/// C2's declared observable of realified receiving logits at the receiver's grain `L`: per class after
/// the first, its real row's grain index relative to the first class's, `⌊L Re f_c⌋ − ⌊L Re f_0⌋`,
/// read as `carry · L + phase class` from the cells; and per class the block `⌊L φ_c⌋` of its lifted
/// phase `φ_c = Im f_c / 2`. Every cell's unresolved fibre is not part of it. The relative indices
/// remove only a common offset of whole cells: a common raw shift that crosses a cell boundary can
/// still move them.
fn admitted(cells: &[GrainCell], phases: &[Rat], grain: u64) -> (Vec<BigInt>, Vec<BigInt>) {
    let index = |cell: &GrainCell| &cell.carry * BigInt::from(grain) + BigInt::from(cell.phase);
    let first = index(&cells[0]);
    (
        cells[1..].iter().map(|cell| index(cell) - &first).collect(),
        PhaseImage::block_of(phases, grain),
    )
}

/// The declared observable of realified logits, read by the receiver's own reader.
fn admitted_of(logits: &[Rat], grain: u64) -> (Vec<BigInt>, Vec<BigInt>) {
    let read = ReceivingRead::of_logits(logits.to_vec(), grain);
    admitted(&read.cells, &read.phases, grain)
}

/// A member of a station's image along one change of it: `point` moved until one relative real row has
/// moved by `2/L` or, where no relative real row moves, one lifted phase by `1/L`. Either crosses a cell
/// of the declared observable, which the caller reads; `None` when the change moves no relative real
/// row and no phase: a change common to every real row, which this witness never uses.
fn crossing(point: &[Rat], change: &[Rat], grain: u64) -> Option<Vec<Rat>> {
    let scale = Rat::from_integer(BigInt::from(grain));
    let classes = point.len() / 2;
    let relative = (1..classes)
        .map(|class| &change[2 * class] - &change[0])
        .find(|moved| !moved.is_zero())
        .map(|moved| integer(2) / (&scale * moved));
    let phase = (0..classes)
        .map(|class| change[2 * class + 1].clone())
        .find(|moved| !moved.is_zero())
        .map(|moved| integer(2) / (&scale * moved));
    let step = relative.or(phase)?;
    Some(
        point
            .iter()
            .zip(change)
            .map(|(value, moved)| value + &step * moved)
            .collect(),
    )
}

/// Every value of a coupled passage in one order: each step's `(a, b)`, each compared station's
/// feature and logits, then each declared face.
fn passage_values(
    waves: &[(Vec<Rat>, Vec<Rat>)],
    features: &[(usize, Vec<Rat>, Vec<Rat>)],
    faces: &[(usize, Vec<Rat>)],
) -> Vec<Rat> {
    waves
        .iter()
        .flat_map(|(a, b)| a.iter().chain(b))
        .chain(features.iter().flat_map(|(_, f, l)| f.iter().chain(l)))
        .chain(faces.iter().flat_map(|(_, f)| f.iter()))
        .cloned()
        .collect()
}

/// Whether one coupled prospect lies in another of the same passage's shape: its point in the other's
/// affine image and every direction of it in the other's span, by exact preimages.
fn prospect_within(inner: &CoupledProspect, outer: &CoupledProspect) -> bool {
    let point = |p: &CoupledProspect| passage_values(&p.point.waves, &p.point.features, &p.faces);
    let change = |d: &CoupledChange| passage_values(&d.waves, &d.features, &d.faces);
    let base = point(outer);
    let span: Vec<Vec<Rat>> = outer.directions.iter().map(change).collect();
    let lies = |value: &[Rat]| {
        from_columns(value.len(), &span)
            .preimage_fibre(value)
            .unwrap()
            .is_some()
    };
    let at = point(inner);
    at.len() == base.len()
        && lies(&minus(&at, &base))
        && inner.directions.iter().all(|d| lies(&change(d)))
}

/// Whether one affine fibre of states lies in another: its point in the other and its directions in
/// the other's span.
fn fibre_within(inner: &StateFibre, outer: &StateFibre) -> bool {
    let span = from_columns(outer.point.len(), &outer.directions);
    contains(outer, &inner.point)
        && inner
            .directions
            .iter()
            .all(|direction| span.preimage_fibre(direction).unwrap().is_some())
}

/// **The whole state space carried through an incident word, solved at once** from the charts alone:
/// the forced state from zero and the transported span, with no restriction.
fn carried_whole(key: &ModelKey, founded: u64, incident: &[Vec<Rat>]) -> StateFibre {
    let sigma = key.extent();
    let mut transport = ExactRatMatrix::identity(sigma).unwrap();
    let mut forced = vec![Rat::zero(); sigma];
    for (t, wave) in incident.iter().enumerate() {
        let charts = key.charts(founded + t as u64).unwrap();
        transport = charts.f.multiply(&transport).unwrap();
        forced = plus(
            &charts.f.apply(&forced).unwrap(),
            &charts.g.apply(wave).unwrap(),
        );
    }
    StateFibre {
        point: forced,
        directions: (0..sigma)
            .map(|j| {
                (0..sigma)
                    .map(|i| transport.get(i, j).unwrap().clone())
                    .collect()
            })
            .collect(),
    }
}

/// The encounter's own blind read of the compared station 1, in the producing frame.
fn station_logits(received: &ActionReception) -> Vec<Rat> {
    received
        .boundary
        .readings()
        .iter()
        .find(|read| read.station == 1)
        .map(|read| read.read.logits.clone())
        .expect("the compared station is read")
}

/// **C2: retained actual World history fixes the next encounter's reading** (the receiving-phase
/// record §7, C2; Refs #73). Two actual encounters on one receiver and one World. Before the first,
/// the World model's prospect is read over its whole fibre, and one `k` of the World's key carries
/// the actual passage. At the continuing crossing one prepared second action is read from the bound
/// memory and from its state-only matched control: the memory from before the first encounter
/// carried through that encounter's actual incident waves with no restriction by its reflected waves
/// (`WorldModel::carried`). Everything actual is shared: the receiver's carry, material and opening,
/// the one World and its clock, the keys and their charts.
///
/// The bound prospect lies in the control's. No retained direction moves the compared station's
/// logits, while a control direction does, and two exact control members differ in the declared
/// observable (`admitted`), so retained history fixed one reading that the control leaves open. The
/// second encounter then reads exactly that. The family also carries the World's law with a false
/// face, which the port filter never rules out.
///
/// Not witnessed: a selection (both plans read the same declared control), the Ask over keys, face
/// conditioning by observed faces, the grain readings of a plural raw image, material learning, or
/// anything beyond this declared World. If the station reading is not fixed after one encounter, that
/// is a measured negative of this declared future, not a fixture to repair.
#[test]
fn retained_world_history_fixes_the_next_reading_that_its_state_only_control_leaves_open() {
    let (field, theta, source) = fixture();
    let mut receiver = receiver(&field, theta);
    receiver
        .bind_world(world(
            &field,
            source.part(0..0).unwrap(),
            medium(&unit_storage(), source_input(true)),
        ))
        .unwrap();
    let law = || key(&field, medium(&unit_storage(), source_input(true)));
    let mut offset = vec![Rat::zero(); N];
    offset[0] = integer(1);
    let false_face = ReceiverFace::new(
        ExactRatMatrix::zero(N, N).unwrap(),
        ExactRatMatrix::identity(N).unwrap(),
        offset,
        vec![Rat::zero(); N],
    )
    .unwrap();
    // The declared family: the World's law with its own face, the same law with a false face, and a
    // disconnected law. The World's membership is this fixture's hypothesis, never a claim.
    let keys = vec![
        law()
            .with_face(ReceiverFace::receiver_state(N, N).unwrap(), N)
            .unwrap(),
        law().with_face(false_face, N).unwrap(),
        key(&field, medium(&unit_storage(), source_input(false))),
    ];
    receiver
        .bind_world_model(WorldModel::found(keys.clone(), 0).unwrap())
        .unwrap();
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(N).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); N],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];

    // The first encounter, its prospect over the whole fibre read before it runs.
    let founded = receiver.world_model().unwrap().clone();
    let first = prepare(&mut receiver, &field, &source, &preparation, &request);
    assert!(first.prospective().unique_control().is_some());
    let foreseen = first.world_prospect().unwrap();
    let ActionCommunication::Received(received) = first.encounter().unwrap() else {
        panic!("the first encounter completes");
    };
    assert!(received.closes());
    let steps = executed(received.encounter.steps());
    let logits = station_logits(&received);
    assert!(holds(
        foreseen[0].as_ref().unwrap(),
        &steps,
        Some((1, logits.as_slice())),
        None
    ));
    let incident: Vec<Vec<Rat>> = steps.iter().map(|step| step.incident.clone()).collect();

    // The state-only matched control, checked against the charts alone.
    let updated = receiver.world_model().unwrap().clone();
    let control = founded.carried(&incident).unwrap();
    assert_eq!(control.keys(), updated.keys());
    assert_eq!(control.tick(), updated.tick());
    for (key, state) in keys.iter().zip(control.states()) {
        let KeyState::Live(fibre) = state else {
            panic!("every declared key is passive, so the control carries it live: {state:?}");
        };
        assert!(same_fibre(
            fibre,
            &carried_whole(key, founded.tick(), &incident)
        ));
    }
    // The restriction is the only difference: every retained fibre lies in its control fibre, and a
    // key the actual reflected waves eliminated is live in the control.
    for (retained, carried) in updated.states().iter().zip(control.states()) {
        let KeyState::Live(carried) = carried else {
            unreachable!("checked above");
        };
        match retained {
            KeyState::Live(retained) => assert!(fibre_within(retained, carried)),
            KeyState::Incompatible { .. } => {}
            KeyState::Held { .. } => panic!("no declared key is held: {retained:?}"),
        }
    }
    // The disconnected law returns every wave whole, so an actual step that does not eliminates it.
    if steps.iter().any(|step| step.reflected != step.incident) {
        assert!(matches!(updated.states()[2], KeyState::Incompatible { .. }));
    }
    // The port filter does not rule out the false face: both faced laws stay live.
    assert!(matches!(updated.states()[0], KeyState::Live(_)));
    assert!(matches!(updated.states()[1], KeyState::Live(_)));

    // The continuing crossing: one prepared second action, read from both memories.
    let second = prepare(&mut receiver, &field, &source, &preparation, &request);
    assert!(second.prospective().unique_control().is_some());
    // A memory off the bound crossing is refused.
    assert!(second.world_prospect_of(&founded).is_err());
    let retained = second.world_prospect().unwrap();
    let matched = second.world_prospect_of(&control).unwrap();
    let grain = second.receiving_phases().grain();
    // Per key, typed: a live retained key's prospect lies in its control's; an eliminated key has no
    // retained image, while its control still reads one.
    for (index, state) in updated.states().iter().enumerate() {
        match state {
            KeyState::Live(_) => assert!(prospect_within(
                retained[index].as_ref().unwrap(),
                matched[index].as_ref().unwrap()
            )),
            _ => {
                assert!(retained[index].is_err());
                assert!(matched[index].is_ok());
            }
        }
    }
    let truth = retained[0].as_ref().unwrap();
    let open = matched[0].as_ref().unwrap();
    let position = truth
        .point
        .features
        .iter()
        .position(|(read, _, _)| *read == 1)
        .unwrap();
    let fixed = truth.point.features[position].2.clone();
    // No retained direction moves the compared station's logits: the retained plan reads one value.
    assert!(
        truth
            .directions
            .iter()
            .all(|direction| direction.features[position].2.iter().all(Zero::is_zero))
    );
    // A control direction moves them, and two exact members of the control's image, the retained
    // point and the point moved along it, differ in the declared observable.
    let member = open
        .directions
        .iter()
        .find_map(|direction| crossing(&fixed, &direction.features[position].2, grain))
        .expect("a direction the retained history removed moves the station's reading");
    assert_ne!(admitted_of(&member, grain), admitted_of(&fixed, grain));

    // The second encounter reads what the retained history fixed.
    let ActionCommunication::Received(received) = second.encounter().unwrap() else {
        panic!("the second encounter completes");
    };
    assert!(received.closes());
    assert_eq!(
        received.word.boundary,
        -received
            .encounter
            .steps()
            .iter()
            .map(|step| &step.port_work)
            .sum::<Rat>()
    );
    let steps = executed(received.encounter.steps());
    let logits = station_logits(&received);
    assert_eq!(logits, fixed);
    assert_eq!(admitted_of(&logits, grain), admitted_of(&fixed, grain));
    // One k carries the actual waves and the station's logits together; where no retained direction
    // moves the waves, they are the retained point's.
    assert!(holds(truth, &steps, Some((1, logits.as_slice())), None));
    let waves_fixed = truth.directions.iter().all(|direction| {
        direction
            .waves
            .iter()
            .all(|(a, b)| a.iter().chain(b).all(Zero::is_zero))
    });
    if waves_fixed {
        for (step, (incident, reflected)) in steps.iter().zip(&truth.point.waves) {
            assert_eq!((&step.incident, &step.reflected), (incident, reflected));
        }
    }
    // Where no retained direction moves a key's face, its reading is the encounter's own reader on the
    // predicted raw face; the World's face is observed only at the compared epoch.
    let observed = received.encounter.observed()[1]
        .as_ref()
        .expect("the compared epoch is observed");
    let faced = |prospect: &CoupledProspect| {
        let at = prospect
            .faces
            .iter()
            .position(|(read, _)| *read == 1)
            .unwrap();
        prospect
            .directions
            .iter()
            .all(|direction| direction.faces[at].1.iter().all(Zero::is_zero))
            .then(|| {
                Face::of_read(
                    &ReceivingRead::of_logits(prospect.faces[at].1.clone(), grain),
                    grain,
                )
                .unwrap()
            })
    };
    if let Some(face) = faced(truth) {
        assert_eq!(&face, observed);
    }
    // The false face is read beside it and never counted as eliminated: it stays live, and where its
    // face is fixed its declared reading differs from the observed one.
    let after = receiver.world_model().unwrap();
    assert!(matches!(after.states()[1], KeyState::Live(_)));
    if let Some(face) = faced(retained[1].as_ref().unwrap()) {
        assert_ne!(
            admitted(face.cells(), face.phases(), grain),
            admitted(observed.cells(), observed.phases(), grain)
        );
    }
    // Both participants continue: the memory's tick is the World's commit, and the World's native tick
    // is the receiver's carry.
    assert_eq!(
        after.tick(),
        receiver.participating_world().unwrap().state().commit
    );
    assert_eq!(after.tick(), updated.tick() + steps.len() as u64);
    assert_eq!(
        receiver
            .participating_world()
            .unwrap()
            .native_tick()
            .unwrap(),
        receiver.resident().carried().unwrap().ticks
    );
}
