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
use holonics::hnn::physical::PhysicalReceiver;
use holonics::hnn::physical::action::{
    ActionCommunication, BoundJointWorld, CoupledProspect, HeldReason, KeyState, ModelKey,
    PreparedPhysicalAction, StateFibre, WaveJointStep, WorldModel,
};
use holonics::hnn::ring::ResonatorMaterial;
use holonics::hnn::word::action::{PortPreparation, ProspectiveControl};
use holonics::hnn::{
    Constitution, Current, Encoded, Field, FieldDeclaration, RingDeclaration, WordOpening,
};
use holonics::holarchy::terrain::KnownTruth;
use holonics::holon::element::{Pump, PumpSchedule};
use holonics::holon::law::{ReferenceHolon, Scheme};
use holonics::holon::{Holon, HolonState, PortHolon};
use holonics::navigator::Clock;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::SymmetricForm;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::receipt::{ReceiptLaw, RegionChart};
use holonics::receiver::reception::{JointLaw, ReceiverFace};
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
    let mut theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ports(1, None, None, Some(ExactRatMatrix::identity(4).unwrap()))
        .unwrap();
    // The source is terminated by the actual World; only the receiving ring is loaded.
    for g in [1] {
        theta = theta
            .with_ring_resonator(
                &field,
                g,
                ResonatorMaterial::new(
                    ExactRatMatrix::identity(4).unwrap(),
                    ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
                    ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 16)),
                    None,
                )
                .unwrap(),
            )
            .unwrap();
    }
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
}

fn executed(steps: &[WaveJointStep]) -> Vec<Executed> {
    steps
        .iter()
        .map(|step| Executed {
            incident: step.incident.clone(),
            reflected: step.reflected.clone(),
            next: step.joint.next_state(),
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

/// Whether one `k` carries a coupled prospect's point onto every actual `(a_t, b_t)` of an
/// encounter: the stacked change of every step against the stacked directions.
fn holds(prospect: &CoupledProspect, steps: &[Executed]) -> bool {
    if prospect.point.waves.len() != steps.len() {
        return false;
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
    ExactRatMatrix::shaped(rows.len(), prospect.directions.len(), rows)
        .unwrap()
        .preimage_fibre(&target)
        .unwrap()
        .is_some()
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
        let steps = steps_of(&prepared.encounter().unwrap());
        assert!(!steps.is_empty());
        let after = receiver.world_model().unwrap();
        assert_eq!(after.tick(), before.tick() + steps.len() as u64);
        // The World's own key is live, and one k carries its prospect onto the actual waves.
        let truth = prospects[0].as_ref().unwrap();
        assert_eq!(truth.tick, before.tick());
        assert!(holds(truth, &steps));
        if truth.directions.is_empty() {
            for (step, (incident, reflected)) in steps.iter().zip(&truth.point.waves) {
                assert_eq!((&step.incident, &step.reflected), (incident, reflected));
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
