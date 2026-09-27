//! Campaign 3's first construction (Lean `HNN/ModeQuotient`): a loaded ring's modes descend to
//! their future quotient. The two-receiver, later-phase witness with its exact ranks and separators,
//! the period lift read against the owner's tick, the squares at the consumer, the storage-null
//! release, the pumped dormant pair one chart cannot release, and the loaded word comparison.

use num_traits::{One, Zero};

use super::learning::{chain, generic, moment, phases};
use super::support::Draw;
use crate::hnn::modes::{LoadedRing, ModeQuotient, Separator, Silence, StateReceiver};
use crate::hnn::ring::{
    PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands, ResonatorRemainders,
};
use crate::hnn::word::Word;
use crate::holon::parametron::Carrier;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, is_zero, matrix, zeros};
use crate::ratio::{Rat, integer, rat};

// -------------------------------------------------------------------------------------------
// fixtures

fn diagonal(entries: &[Rat]) -> ExactRatMatrix {
    ExactRatMatrix::from_diagonal(entries.to_vec()).unwrap()
}

/// The realified form of a closed cycle of `nodes` nodes, weight `w` on every branch:
/// `Σ_b w (e_b − e_(b+1))(e_b − e_(b+1))ᵀ` on the real and on the imaginary coordinate.
fn cycle_form(nodes: usize, weight: &Rat) -> ExactRatMatrix {
    let mut form = vec![vec![Rat::zero(); nodes]; nodes];
    for branch in 0..nodes {
        let (i, j) = (branch, (branch + 1) % nodes);
        form[i][i] += weight;
        form[j][j] += weight;
        form[i][j] -= weight;
        form[j][i] -= weight;
    }
    matrix(2 * nodes, 2 * nodes, |r, c| {
        if r % 2 == c % 2 {
            form[r / 2][c / 2].clone()
        } else {
            Rat::zero()
        }
    })
    .unwrap()
}

/// A half-turn pump of strength `p` on the axis `1`: `K_0 = K − 2p diag(1, −1)`,
/// `K_1 = K + 2p diag(1, −1)` on every node.
fn half_pump(strength: Rat) -> PumpDeclaration {
    PumpDeclaration::new(
        strength,
        Carrier::new(Rat::one(), Rat::zero()).unwrap(),
        PumpStep::Half,
    )
    .unwrap()
}

/// The loaded ring at `h = 1`, `Y = 1`, under the exact law.
fn operands(material: &ResonatorMaterial) -> ResonatorOperands {
    ResonatorOperands::at_cut(0, material, &Rat::one(), &Rat::one(), None).unwrap()
}

/// **The pumped phase pair**: two nodes, `C = diag(1, 0, 1, 0)`, `K = ½`, no dissipation, a
/// half-turn pump of strength `¼`: `K_0 = diag(0, 1, 0, 1)`, `K_1 = diag(1, 0, 1, 0)`. The state is
/// `(u_0x, u_0y, u_1x, u_1y, w_0x, w_0y, w_1x, w_1y)`.
fn pumped_pair() -> ResonatorMaterial {
    let one = Rat::one();
    let zero = Rat::zero();
    ResonatorMaterial::new(
        diagonal(&[one.clone(), zero.clone(), one, zero]),
        ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 2)),
        ExactRatMatrix::zero(4, 4).unwrap(),
        Some(half_pump(rat(1, 4))),
    )
    .unwrap()
}

/// **The non-diagonal base**: the two-node cycle's forms `C = 2L̃`, `K = 4L̃`, `D = ⅛`, unpumped.
fn cycle_base() -> ResonatorMaterial {
    ResonatorMaterial::new(
        cycle_form(2, &Rat::one()),
        cycle_form(2, &integer(2)),
        ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
        None,
    )
    .unwrap()
}

/// **The pumped dormant pair**: one node, `C = 1`, `K = 0`, no dissipation, a half-turn pump of
/// strength `¼`: `K_0 = diag(−½, ½)`, `K_1 = diag(½, −½)`.
fn pumped_dormant() -> ResonatorMaterial {
    ResonatorMaterial::new(
        ExactRatMatrix::identity(2).unwrap(),
        ExactRatMatrix::zero(2, 2).unwrap(),
        ExactRatMatrix::zero(2, 2).unwrap(),
        Some(half_pump(rat(1, 4))),
    )
    .unwrap()
}

fn unit(extent: usize, index: usize) -> Vec<Rat> {
    let mut vector = zeros(extent);
    vector[index] = Rat::one();
    vector
}

fn row(extent: usize, index: usize) -> ExactRatMatrix {
    ExactRatMatrix::shaped(1, extent, vec![unit(extent, index)]).unwrap()
}

/// Whether two families of vectors span the same subspace.
fn same_span(left: &[Vec<Rat>], right: &[Vec<Rat>], extent: usize) -> bool {
    let rank = |rows: Vec<Vec<Rat>>| {
        if rows.is_empty() {
            0
        } else {
            ExactRatMatrix::shaped(rows.len(), extent, rows)
                .unwrap()
                .rank()
                .unwrap()
        }
    };
    let both = [left, right].concat();
    rank(left.to_vec()) == rank(both.clone()) && rank(right.to_vec()) == rank(both)
}

/// The owner's exact tick over a drive sequence from a state: the returned waves and the states.
fn owner_run(
    operands: &ResonatorOperands,
    state: &[Rat],
    drives: &[Vec<Rat>],
) -> (Vec<Vec<Rat>>, Vec<Vec<Rat>>) {
    let n = operands.width();
    let mut current = state.to_vec();
    let (mut waves, mut states) = (Vec::new(), vec![current.clone()]);
    for (tick, drive) in drives.iter().enumerate() {
        let stepped = operands
            .step(
                tick,
                drive,
                [&current[..n], &current[n..]],
                &ResonatorRemainders::default(),
                None,
            )
            .unwrap();
        waves.push(stepped.output);
        current = [stepped.state[0].clone(), stepped.state[1].clone()].concat();
        states.push(current.clone());
    }
    (waves, states)
}

fn drives(seed: u64, width: usize, ticks: usize) -> Vec<Vec<Rat>> {
    let mut draw = Draw::new(seed);
    (0..ticks).map(|_| draw.half_vector(width)).collect()
}

fn heard(silence: &Silence) -> Option<&Separator> {
    match silence {
        Silence::Heard(separator) => Some(separator),
        _ => None,
    }
}

// -------------------------------------------------------------------------------------------
// the witness

/// **The two-receiver, later-phase witness.** On the pumped phase pair the present receiver (the
/// port at phase `0`) is silent on four directions: `u_0x`, `u_1x` (in `ker K_0`) and `w_0y`,
/// `w_1y` (in `ker C`). The admitted future (the pump's cycle) reads `u_0x` and `u_1x` at tick `1`,
/// where `K_1` stiffens them: each is retained with the separator (port, phase `1`, word `[0]`).
/// The massless velocities never move the rate, so the port never hears them: released. Exact
/// ranks: retained `6 = 2·3`, released `2`, present-silent `4 = 2²`. Admitting a cycle receiver that
/// reads `w_0y` at phase `1` retains it with its separator (receiver `1`, phase `1`, word `[0]`):
/// retained `7`, released `1`, and the larger family's release lies in the smaller's.
#[test]
fn a_later_phase_reading_retains_what_the_present_does_not_hear() {
    let material = pumped_pair();
    let ring = LoadedRing::at_cut(&operands(&material)).unwrap();
    assert_eq!(ring.phases().len(), 2);
    let port = ModeQuotient::of(&ring, &[]).unwrap();
    let extent = 8;
    let (u0x, u1x, w0y, w1y) = (0, 2, 5, 7);
    assert!(same_span(
        port.present_silent(),
        &[
            unit(extent, u0x),
            unit(extent, u1x),
            unit(extent, w0y),
            unit(extent, w1y)
        ],
        extent,
    ));
    assert_eq!((port.retained_rank(), port.released_rank()), (6, 2));
    assert!(same_span(
        &port.released().unwrap(),
        &[unit(extent, w0y), unit(extent, w1y)],
        extent,
    ));
    assert!(same_span(
        &port.admitted().kernel().unwrap(),
        &port.released().unwrap(),
        extent,
    ));
    let later = Separator {
        receiver: 0,
        phase: 1,
        word: vec![0],
    };
    assert_eq!(port.silent().len(), 4);
    assert_eq!(port.silent().iter().filter(|c| c.released()).count(), 2);
    for coordinate in port.silent().iter().filter(|c| !c.released()) {
        assert_eq!(heard(&coordinate.silence), Some(&later));
        assert!(same_span(
            std::slice::from_ref(&coordinate.direction),
            &[unit(
                extent,
                if coordinate.direction[u0x].is_zero() {
                    u1x
                } else {
                    u0x
                }
            )],
            extent,
        ));
    }

    // The two-receiver family: a cycle receiver reads `w_0y` once per cycle, at phase 1.
    let cycle = StateReceiver::new(row(extent, w0y), vec![1]);
    let both = ModeQuotient::of(&ring, &[cycle]).unwrap();
    assert_eq!((both.retained_rank(), both.released_rank()), (7, 1));
    assert!(same_span(
        &both.released().unwrap(),
        &[unit(extent, w1y)],
        extent
    ));
    let read_by_cycle = both
        .silent()
        .iter()
        .find(|c| !c.direction[w0y].is_zero())
        .unwrap();
    assert_eq!(
        heard(&read_by_cycle.silence),
        Some(&Separator {
            receiver: 1,
            phase: 1,
            word: vec![0],
        })
    );
    // The larger family's release lies in the smaller's (`admitted_nonincreasing`'s direction).
    for direction in both.released().unwrap() {
        assert!(same_span(
            &port.released().unwrap(),
            &[port.released().unwrap(), vec![direction]].concat(),
            extent,
        ));
    }
}

/// **The non-diagonal base.** The two-node cycle's forms `C = 2L̃`, `K = 4L̃` (unpumped, `P = 1`):
/// the port at the cut is silent on `L̃(w − u) = 0`, dimension `6 = 2·3`. The harmonic displacement
/// `ker K` and the massless velocity `ker C` (the rotor's common translation, each of dimension 2)
/// are never heard: released, `4 = 2²`. The two further silent directions `(u, u)`, `u` off
/// `ker L̃`, have no rate now, tick to `(u, −u)`, and are heard at tick `1`. A cycle receiver that
/// reads the harmonic displacement `u_0x + u_1x` retains it: released `3`.
#[test]
fn the_cycle_base_releases_its_harmonic_and_massless_modes() {
    let ring = LoadedRing::at_cut(&operands(&cycle_base())).unwrap();
    let quotient = ModeQuotient::of(&ring, &[]).unwrap();
    let extent = 8;
    assert_eq!(quotient.present_silent().len(), 6);
    assert_eq!((quotient.retained_rank(), quotient.released_rank()), (4, 4));
    let translation = |offset: usize, axis: usize| {
        let mut v = zeros(extent);
        v[offset + axis] = Rat::one();
        v[offset + 2 + axis] = Rat::one();
        v
    };
    assert!(same_span(
        &quotient.released().unwrap(),
        &[
            translation(0, 0),
            translation(0, 1),
            translation(4, 0),
            translation(4, 1)
        ],
        extent,
    ));
    let tick_one = Separator {
        receiver: 0,
        phase: 0,
        word: vec![0],
    };
    let heard_now: Vec<_> = quotient
        .silent()
        .iter()
        .filter_map(|c| heard(&c.silence))
        .collect();
    assert_eq!(heard_now, vec![&tick_one, &tick_one]);

    let mut winding = zeros(extent);
    winding[0] = Rat::one();
    winding[2] = Rat::one();
    let cycle = StateReceiver::new(
        ExactRatMatrix::shaped(1, extent, vec![winding]).unwrap(),
        vec![0],
    );
    let read = ModeQuotient::of(&ring, &[cycle]).unwrap();
    assert_eq!((read.retained_rank(), read.released_rank()), (5, 3));
    assert!(!same_span(
        &read.released().unwrap(),
        &[read.released().unwrap(), vec![translation(0, 0)]].concat(),
        extent,
    ));
}

/// **The pumped dormant pair: one chart cannot release it.** With `C = 1`, `K = 0` and a half-turn
/// pump, the pairs `(u, ½K_0 u)` have no rate at phase `0`, tick to `(u, −½K_0 u)` and have none at
/// phase `1` either: the whole admitted future is silent on them (`K_adm` of dimension 2, all of
/// `ker F_now`). A chart shared by both phases fails its square there: the lift's chart is not
/// carried by `T_0`, the phase-`1` port would hear each pair itself, a reading a shared chart must
/// factor (separator: receiver `0`, phase `1`, empty word), and nothing is released (retained
/// `4 = 2²`). They store energy: `E_0` of
/// `(1, 0, −¼, 0)` is `1/32 − 1/4 = −7/32`, which a release would drop.
#[test]
fn a_pumped_dormant_pair_is_silent_but_one_chart_cannot_release_it() {
    let material = pumped_dormant();
    let loaded = operands(&material);
    let ring = LoadedRing::at_cut(&loaded).unwrap();
    let quotient = ModeQuotient::of(&ring, &[]).unwrap();
    let extent = 4;
    let pair = vec![Rat::one(), Rat::zero(), rat(-1, 4), Rat::zero()];
    let other = vec![Rat::zero(), Rat::one(), Rat::zero(), rat(1, 4)];
    assert!(same_span(
        quotient.present_silent(),
        &[pair.clone(), other.clone()],
        extent
    ));
    let admitted = quotient.admitted().kernel().unwrap();
    assert!(same_span(&admitted, &[pair.clone(), other], extent));
    assert_eq!((quotient.retained_rank(), quotient.released_rank()), (4, 0));
    let fails = Separator {
        receiver: 0,
        phase: 1,
        word: Vec::new(),
    };
    assert_eq!(quotient.silent().len(), 2);
    for coordinate in quotient.silent() {
        assert_eq!(coordinate.silence, Silence::SquareFails(fails.clone()));
    }
    // The lift's chart: its kernel is not carried by the phase-0 tick, so `V T_0 = T̄ V` has no
    // solution `T̄` with that `V`.
    let carried = ring.phases()[0].transport.apply(&pair).unwrap();
    assert!(!same_span(
        &admitted,
        &[admitted.clone(), vec![carried.clone()]].concat(),
        extent
    ));
    assert_eq!(
        carried,
        vec![Rat::one(), Rat::zero(), rat(1, 4), Rat::zero()]
    );
    // The admitted future never hears it: silent over four periods of the owner's tick.
    let (waves, _) = owner_run(&loaded, &pair, &vec![zeros(2); 8]);
    assert!(waves.iter().all(|wave| is_zero(wave)));
    assert_eq!(
        material.energy(0, &pair[..2], &pair[2..]).unwrap(),
        rat(-7, 32)
    );
}

// -------------------------------------------------------------------------------------------
// the laws at the consumer

fn fixtures() -> Vec<(ResonatorMaterial, Vec<StateReceiver>)> {
    vec![
        (pumped_pair(), Vec::new()),
        (pumped_pair(), vec![StateReceiver::new(row(8, 5), vec![1])]),
        (cycle_base(), Vec::new()),
        (pumped_dormant(), Vec::new()),
    ]
}

/// **The period lift is exact** (Lean `periodic_lift_exact`, `cycle_mul_add`): the owner's tick
/// over `t` ticks is `Φ(t) = Φ(t mod P) T_P^(t div P)`, and the kernel of every admitted reading
/// `ρ_(r, t mod P) Φ(t)` over `t < P·2n` ticks is the lift's kernel.
#[test]
fn the_period_lift_reads_exactly_the_pump_cycle() {
    for (material, receivers) in fixtures() {
        let loaded = operands(&material);
        let ring = LoadedRing::at_cut(&loaded).unwrap();
        let quotient = ModeQuotient::of(&ring, &receivers).unwrap();
        let (period, extent) = (ring.phases().len(), ring.extent());
        let lift = ring.period().unwrap();
        let mut power = ExactRatMatrix::identity(extent).unwrap();
        let mut rows = Vec::new();
        for t in 0..period * extent {
            if t > 0 && t % period == 0 {
                power = lift.multiply(&power).unwrap();
            }
            let cycle = ring.cycle(t).unwrap();
            assert_eq!(
                cycle,
                ring.cycle(t % period).unwrap().multiply(&power).unwrap()
            );
            for column in 0..extent {
                let (_, states) = owner_run(
                    &loaded,
                    &unit(extent, column),
                    &vec![zeros(ring.width()); t],
                );
                let direct = cycle.apply(&unit(extent, column)).unwrap();
                assert_eq!(states[t], direct);
            }
            for &(receiver, phase) in quotient.requests() {
                if phase == t % period {
                    let map = if receiver == 0 {
                        ring.phases()[phase].reading.clone()
                    } else {
                        receivers[receiver - 1].reading().clone()
                    };
                    rows.extend(map.multiply(&cycle).unwrap().to_rows());
                }
            }
        }
        let silent = ExactRatMatrix::shaped(rows.len(), extent, rows)
            .unwrap()
            .kernel_basis()
            .unwrap();
        assert!(same_span(
            &silent,
            &quotient.admitted().kernel().unwrap(),
            extent
        ));
    }
}

/// **The squares at the consumer**: `V T_t = T̄_t V`, `V B_t = B̄_t` and `ρ_(r,t) = ρ̄_(r,t) V` at
/// every phase, and the consequence `ρ̄ T̄_w V x = ρ T_w x` over the admitted cycle's words, read
/// against the owner's tick.
#[test]
fn every_phase_square_closes_and_the_admitted_readings_descend() {
    for (seed, (material, receivers)) in fixtures().into_iter().enumerate() {
        let loaded = operands(&material);
        let ring = LoadedRing::at_cut(&loaded).unwrap();
        let quotient = ModeQuotient::of(&ring, &receivers).unwrap();
        let v = quotient.retain();
        for (phase, operators) in ring.phases().iter().enumerate() {
            let descended = quotient.transport(phase).unwrap();
            assert_eq!(
                v.multiply(&operators.transport).unwrap(),
                descended.multiply(v).unwrap()
            );
            assert_eq!(
                &v.multiply(&operators.source).unwrap(),
                quotient.source(phase).unwrap()
            );
            assert_eq!(quotient.feedthrough(phase).unwrap(), &operators.feedthrough);
        }
        for &(receiver, phase) in quotient.requests() {
            let map = if receiver == 0 {
                ring.phases()[phase].reading.clone()
            } else {
                receivers[receiver - 1].reading().clone()
            };
            let reading = quotient.reading(receiver, phase).unwrap();
            assert_eq!(map, reading.multiply(v).unwrap());
        }
        // The consequence over admitted words, against the owner's tick at zero drive.
        let state = Draw::new(401 + seed as u64).half_vector(ring.extent());
        let ticks = 2 * ring.phases().len() * ring.extent();
        let (_, states) = owner_run(&loaded, &state, &vec![zeros(ring.width()); ticks]);
        let mut retained = quotient.retained(&state).unwrap();
        for (t, full) in states.iter().enumerate() {
            let phase = t % ring.phases().len();
            for &(receiver, at) in quotient.requests() {
                if at == phase {
                    let map = if receiver == 0 {
                        ring.phases()[phase].reading.clone()
                    } else {
                        receivers[receiver - 1].reading().clone()
                    };
                    assert_eq!(
                        quotient
                            .reading(receiver, phase)
                            .unwrap()
                            .apply(&retained)
                            .unwrap(),
                        map.apply(full).unwrap()
                    );
                }
            }
            retained = quotient.transport(phase).unwrap().apply(&retained).unwrap();
        }
    }
}

/// **The released part changes no admitted reading, and stores nothing** (Lean
/// `released_pair_storage_null`): for every released `k` and every phase, `C k_w = 0` and
/// `K_t k_u = 0`, so `E_t(x + k) = E_t(x)` (the split is `Q_t`-orthogonal, hence `C`-orthogonal,
/// for every complement); and the owner's tick from `x` and from `x + k`, on the same drives,
/// returns the same wave at every tick.
#[test]
fn the_released_part_is_never_heard_and_stores_nothing() {
    let mut released_total = 0;
    for (seed, (material, receivers)) in fixtures().into_iter().enumerate() {
        let loaded = operands(&material);
        let ring = LoadedRing::at_cut(&loaded).unwrap();
        let quotient = ModeQuotient::of(&ring, &receivers).unwrap();
        let n = ring.width();
        let mut draw = Draw::new(501 + seed as u64);
        let state = draw.half_vector(ring.extent());
        let drive = drives(601 + seed as u64, n, 3 * ring.extent());
        let (waves, states) = owner_run(&loaded, &state, &drive);
        let (capacity, _, _) = material.forms();
        for direction in quotient.released().unwrap() {
            released_total += 1;
            let (u, w) = direction.split_at(n);
            assert!(is_zero(&capacity.apply(w).unwrap()));
            for phase in 0..ring.phases().len() {
                assert!(is_zero(&loaded.stiffness(phase).apply(u).unwrap()));
                let moved = add(&state, &direction);
                assert_eq!(
                    material.energy(phase, &moved[..n], &moved[n..]).unwrap(),
                    material.energy(phase, &state[..n], &state[n..]).unwrap()
                );
            }
            let (shifted, shifted_states) = owner_run(&loaded, &add(&state, &direction), &drive);
            assert_eq!(shifted, waves);
            for (t, (full, moved)) in states.iter().zip(&shifted_states).enumerate() {
                let phase = t % ring.phases().len();
                for (index, receiver) in receivers.iter().enumerate() {
                    if receiver.phases().contains(&phase) {
                        assert_eq!(
                            receiver.reading().apply(full).unwrap(),
                            receiver.reading().apply(moved).unwrap(),
                            "receiver {}",
                            index + 1
                        );
                    }
                }
            }
        }
    }
    assert_eq!(released_total, 2 + 1 + 4);
}

/// **The descended ring returns the same wave** (Lean `descended_run_reads`): from `V x`, on
/// drawn drives, the descended run's waves equal the owner's tick from `x`, tick for tick.
#[test]
fn the_descended_ring_returns_the_full_rings_wave() {
    for (seed, (material, receivers)) in fixtures().into_iter().enumerate() {
        let loaded = operands(&material);
        let ring = LoadedRing::at_cut(&loaded).unwrap();
        let quotient = ModeQuotient::of(&ring, &receivers).unwrap();
        let state = Draw::new(701 + seed as u64).half_vector(ring.extent());
        let drive = drives(801 + seed as u64, ring.width(), 3 * ring.extent());
        let (waves, _) = owner_run(&loaded, &state, &drive);
        let descended = quotient
            .run(&quotient.retained(&state).unwrap(), &drive)
            .unwrap();
        assert_eq!(descended, waves);
    }
}

/// A lattice chart's executed solve is not the law: the mode quotient refuses it.
#[test]
fn a_charted_solve_is_refused() {
    let field = chain();
    let lattice = field.word_lattice().copied().unwrap();
    let charted =
        ResonatorOperands::at_cut(0, &pumped_pair(), &Rat::one(), &Rat::one(), Some(&lattice))
            .unwrap();
    assert!(LoadedRing::at_cut(&charted).is_err());
}

// -------------------------------------------------------------------------------------------
// the loaded word comparison

/// **The loaded word comparison**: the chain control on the exact law, ring 0 loaded with the
/// two-node cycle's forms, `D = ⅛` and a half-turn pump of strength `1/16`. The word runs; the
/// descended ring, driven by the word's own element outputs from the retained zero, returns the
/// resonator's waves exactly at each of the word's three ticks. The pump leaves no stiffness
/// kernel, so only the massless velocities are released: retained `6 = 2·3`, released `2`; the
/// port at the cut is silent on `4 = 2²` directions, and the other two are heard at tick `1`.
#[test]
fn the_descended_ring_reproduces_the_loaded_word() {
    let field = chain().with_exact_word();
    let width = field.ring(0).width();
    assert_eq!(width, 4);
    let pump = PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
    let material = ResonatorMaterial::new(
        cycle_form(2, &Rat::one()),
        cycle_form(2, &integer(2)),
        ExactRatMatrix::identity(width).unwrap().scaled(&rat(1, 8)),
        Some(pump),
    )
    .unwrap();
    let theta = generic(&field, 311)
        .with_ring_resonator(&field, 0, material)
        .unwrap();
    let (current, open) = moment(&field, 312, 12);
    let admitted = phases(&field, &theta, &current);
    let mut word = Word::open(&field, &theta, &current, &open).unwrap();
    word.forward(&admitted).unwrap();
    let steps = &word.resonances()[0].as_ref().unwrap().steps;
    assert!(steps.len() >= 2);
    assert!(steps.iter().any(|step| !is_zero(&step.output)));

    let loaded = ResonatorOperands::at_cut(
        0,
        theta.resonator(0).unwrap(),
        field.ring(0).admittance(),
        field.step(),
        None,
    )
    .unwrap();
    let ring = LoadedRing::at_cut(&loaded).unwrap();
    let quotient = ModeQuotient::of(&ring, &[]).unwrap();
    assert_eq!((quotient.retained_rank(), quotient.released_rank()), (6, 2));
    // The port at the cut is silent on four directions: the two massless velocities, released,
    // and two more that the pump's phase 1 hears at tick 1.
    assert_eq!(quotient.present_silent().len(), 4);
    assert!(same_span(
        &quotient.admitted().kernel().unwrap(),
        &quotient.released().unwrap(),
        2 * width,
    ));
    let later = Separator {
        receiver: 0,
        phase: 1,
        word: vec![0],
    };
    let heard_later: Vec<_> = quotient
        .silent()
        .iter()
        .filter_map(|c| heard(&c.silence))
        .collect();
    assert_eq!(heard_later, vec![&later, &later]);
    assert_eq!(steps.len(), 3);
    for (tick, step) in steps.iter().enumerate() {
        assert_eq!(step.phase, tick % 2);
    }
    let drive: Vec<Vec<Rat>> = steps.iter().map(|step| step.drive.clone()).collect();
    let descended = quotient
        .run(&quotient.retained(&zeros(2 * width)).unwrap(), &drive)
        .unwrap();
    for (step, wave) in steps.iter().zip(&descended) {
        assert_eq!(&step.output, wave);
    }
}
