//! The locking pump on the live listener (the revised plan, step 1a): the receiving ring's
//! saturated resonator, founded by [`super::mounted`] with its two sheets certified on the period
//! the live word executes, read here through the live word itself. The authored values below are
//! test probes (injected storage waves, perturbations, covectors); none enters the founding.
use super::mounted;
use crate::octets::BUDGET;
use holonics::hnn::Floquet;
use holonics::hnn::chart::Charts;
use holonics::hnn::constitution::{Constitution, DepositReading, Lattice, Locus, RingReading};
use holonics::hnn::field::{ConstitutionRead, Current, Field};
use holonics::hnn::paired::PairedCarrier;
use holonics::hnn::propagation::Operands;
use holonics::hnn::reference::observed::ObservedCrib;
use holonics::hnn::reference::{Reference, Resident};
use holonics::hnn::ring::{
    PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands, ResonatorRemainders,
    ReverseSplit, TubeCentre,
};
use holonics::hnn::word::{EndChange, Word};
use holonics::holon::parametron::{Carrier, LockedPair};
use holonics::ratio::{Rat, integer, rat};
use num_traits::{One, Zero};

/// The founded listener, its receiving ring and the live word's lattice and certified lock.
struct Live {
    resident: Resident,
    ring: usize,
    transient: Lattice,
    pair: LockedPair,
}

fn live() -> Live {
    let port = Reference::new(4, BUDGET);
    let (resident, _) = mounted(&port, 65536).unwrap();
    let ring = resident.field().receivers()[0].ring;
    let operands = operands(&resident, resident.constitution());
    let transient = operands.lattice().unwrap().transient();
    let pair = operands.resonators()[ring]
        .as_ref()
        .unwrap()
        .executed_lock(Some(&transient))
        .unwrap();
    Live {
        resident,
        ring,
        transient,
        pair,
    }
}

/// The operands the live word opens on: the resident's field and current, cold charts.
fn operands(resident: &Resident, constitution: &Constitution) -> Operands {
    Operands::at_cut_charted(
        resident.field(),
        constitution,
        resident.current(),
        &mut Charts::new(),
    )
    .unwrap()
}

/// A live word at rest except ring `ring`'s resonator state and an injected storage wave on it.
fn word<'c>(
    field: &'c Field,
    operands: Operands,
    ring: usize,
    state: Option<[Vec<Rat>; 2]>,
    storage: Vec<Rat>,
) -> Word<'c> {
    let mut change = EndChange::rest(field, &operands);
    if let Some(state) = state {
        change.resonators[ring] = Some(state);
    }
    let injection: Vec<Vec<Rat>> = field
        .rings()
        .iter()
        .enumerate()
        .map(|(g, declared)| {
            if g == ring {
                storage.clone()
            } else {
                vec![Rat::zero(); declared.width()]
            }
        })
        .collect();
    Word::continuing(field, operands, &change, &injection, 0).unwrap()
}

/// The resonator's state `[u, w]` read as the domain's `(u, w)` coordinates.
fn state_of(word: &Word<'_>, ring: usize) -> Vec<Rat> {
    let resonance = word.resonances()[ring].as_ref().unwrap();
    [resonance.state[0].clone(), resonance.state[1].clone()].concat()
}

/// A test's reading of the pair at a closing boundary: closed-ball membership in one of its two
/// certified balls (`PeriodicLock::contains`), or in neither. The lock event that reads it in the
/// library joins with the event clock that consumes it (the revised plan, step 1b).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LockSample {
    Sheet(i8),
    Unlocked,
}

/// The state entered a ball other than the one it last lay in (`from`, `None` before any ball).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LockEvent {
    from: Option<i8>,
    to: i8,
    at: u64,
}

fn sample(pair: &LockedPair, state: &[Rat]) -> LockSample {
    if pair.positive().contains(state).unwrap() {
        LockSample::Sheet(1)
    } else if pair.negative().contains(state).unwrap() {
        LockSample::Sheet(-1)
    } else {
        LockSample::Unlocked
    }
}

fn observe(
    pair: &LockedPair,
    last: Option<i8>,
    state: &[Rat],
    at: u64,
) -> (LockSample, Option<LockEvent>) {
    let sampled = sample(pair, state);
    let event = match sampled {
        LockSample::Sheet(to) if last != Some(to) => Some(LockEvent { from: last, to, at }),
        _ => None,
    };
    (sampled, event)
}

/// The live word's samples and events over `ticks` ticks, and the ticks whose drive the lying
/// sheet's margin held or did not hold.
struct Sampled {
    samples: Vec<LockSample>,
    events: Vec<LockEvent>,
    held: usize,
    exceeded: usize,
}

/// Tick the live word `ticks` times, sampling the lock at every closing boundary (a standing
/// pump's period is one tick) and checking every tick's balances. Wherever the state lay in a
/// sheet's ball and the tick's drive is held by that sheet's margin, the certificate's claim is
/// read on the live path: the next sample lies in the same ball.
fn sampled(word: &mut Word<'_>, ring: usize, pair: &LockedPair, ticks: usize) -> Sampled {
    let mut lying = sample(pair, &state_of(word, ring));
    let (mut samples, mut events, mut last) = (Vec::new(), Vec::new(), None);
    let (mut held, mut exceeded) = (0, 0);
    for at in 0..ticks {
        let balance = word.tick().unwrap();
        assert!(balance.closes(), "tick {at}'s executed balance closes");
        let drive = &word.resonances()[ring]
            .as_ref()
            .unwrap()
            .steps
            .last()
            .unwrap()
            .drive;
        let margin = match lying {
            LockSample::Sheet(1) => Some(pair.positive()),
            LockSample::Sheet(_) => Some(pair.negative()),
            LockSample::Unlocked => None,
        }
        .map(|lock| lock.domain().step(0).unwrap().holds(drive).unwrap());
        let (now, event) = observe(pair, last, &state_of(word, ring), at as u64);
        match margin {
            Some(true) => {
                held += 1;
                assert_eq!(now, lying, "tick {at}: a held drive keeps its ball");
            }
            Some(false) => exceeded += 1,
            None => {}
        }
        if let LockSample::Sheet(sheet) = now {
            last = Some(sheet);
        }
        lying = now;
        samples.push(now);
        events.extend(event);
    }
    for (at, field) in word.field_balances().iter().enumerate() {
        assert!(field.closes(), "tick {at}'s field balance closes");
    }
    Sampled {
        samples,
        events,
        held,
        exceeded,
    }
}

/// A storage wave of amplitude `z` at carrier `(re, im)` on every node.
fn wave(field: &Field, ring: usize, z: &Rat, re: i64, im: i64) -> Vec<Rat> {
    (0..field.ring(ring).width())
        .map(|i| z * integer(if i % 2 == 0 { re } else { im }))
        .collect()
}

#[test]
fn the_founding_certifies_both_sheets_on_the_live_words_rounded_period() {
    let live = live();
    let field = live.resident.field();
    let material = live
        .resident
        .constitution()
        .ring_resonator(live.ring)
        .unwrap();
    assert_eq!(material.pump().unwrap().step(), PumpStep::Stand);
    assert!(material.saturation().is_some());
    // The live word's own operands, its lattice the field's word lattice.
    let opened = word(
        field,
        operands(&live.resident, live.resident.constitution()),
        live.ring,
        None,
        vec![Rat::zero(); field.ring(live.ring).width()],
    );
    let resonator = opened.operands().resonators()[live.ring].as_ref().unwrap();
    let transient = opened.operands().lattice().unwrap().transient();
    assert_eq!(transient.unit(), live.transient.unit());
    assert!(
        resonator.chart_words(0).is_some(),
        "the live word charts its solve"
    );
    let pair = resonator.executed_lock(Some(&transient)).unwrap();
    assert_eq!(pair, live.pair);
    let (positive, negative) = (
        pair.positive().domain().step(0).unwrap(),
        pair.negative().domain().step(0).unwrap(),
    );
    // Two opposite cyclic domains, each with a positive drive margin under its rounding floor.
    assert_eq!(pair.positive().sheet(), 1);
    assert_eq!(pair.negative().sheet(), -1);
    assert_eq!(
        positive.proposal().centre[0],
        -negative.proposal().centre[0].clone()
    );
    for step in [positive, negative] {
        assert!(step.margin() > &Rat::zero());
        assert!(step.rounding_floor() > &Rat::zero());
        let rounding = &step.proposal().rounding;
        assert!(rounding * rounding >= *step.rounding_floor());
    }
    eprintln!(
        "lock amplitude={} unit={} rounding={} margin={} contraction={}",
        resonator.sheet_amplitude().unwrap(),
        transient.unit(),
        positive.proposal().rounding,
        positive.margin(),
        pair.positive().domain().contraction()
    );
    // The smooth law alone does not certify the charted solve the word executes.
    assert!(resonator.executed_lock(None).is_err());
    // A saturated period is not a Floquet multiplier problem.
    assert!(Floquet::of(resonator).is_err());
}

#[test]
fn the_live_resonator_started_in_its_sheet_stays_in_its_ball() {
    let live = live();
    let field = live.resident.field();
    let width = field.ring(live.ring).width();
    let centre = live
        .pair
        .positive()
        .domain()
        .step(0)
        .unwrap()
        .proposal()
        .centre
        .clone();
    let unit = live.transient.unit();
    for offset in [Rat::zero(), integer(64) * &unit] {
        let mut start = centre.clone();
        start[0] += &offset;
        let mut opened = word(
            field,
            operands(&live.resident, live.resident.constitution()),
            live.ring,
            Some([start[..width].to_vec(), start[width..].to_vec()]),
            vec![Rat::zero(); width],
        );
        assert_eq!(
            sample(&live.pair, &start),
            LockSample::Sheet(1),
            "the start lies in the positive ball"
        );
        let read = sampled(&mut opened, live.ring, &live.pair, 16);
        assert!(
            read.samples.iter().all(|s| *s == LockSample::Sheet(1)),
            "offset {offset}: {:?}",
            read.samples
        );
        assert_eq!(
            read.events,
            vec![LockEvent {
                from: None,
                to: 1,
                at: 0
            }]
        );
        eprintln!(
            "offset={offset} ticks=16 drive_held_by_margin={} exceeded={}",
            read.held, read.exceeded
        );
        if offset.is_zero() {
            assert_eq!(read.held, 16, "the fixed point drives nothing");
            assert_eq!(
                state_of(&opened, live.ring),
                centre,
                "the sheet is a fixed point"
            );
        }
    }
}

#[test]
fn a_drive_below_the_margin_holds_the_sheet_and_one_above_flips_it_once() {
    let live = live();
    let field = live.resident.field();
    let width = field.ring(live.ring).width();
    let opened = operands(&live.resident, live.resident.constitution());
    let resonator = opened.resonators()[live.ring].as_ref().unwrap();
    let step = live.pair.positive().domain().step(0).unwrap();
    let centre = &step.proposal().centre;
    let unit = live.transient.unit();
    // The largest dyadic in-phase drive on every node that the margin holds: the margin is the
    // certified room left in the next ball, `|D̂(e − e₀)|_G ≤ m`.
    let uniform = |scale: &Rat| -> Vec<Rat> {
        (0..width)
            .map(|i| {
                if i % 2 == 0 {
                    scale.clone()
                } else {
                    Rat::zero()
                }
            })
            .collect()
    };
    let mut scale = Rat::one();
    while !step.holds(&uniform(&scale)).unwrap() {
        scale /= integer(2);
    }
    assert!(!step.holds(&uniform(&(integer(2) * &scale))).unwrap());
    let rest = ResonatorRemainders::default();
    let held = resonator
        .step(
            0,
            &uniform(&scale),
            [&centre[..width], &centre[width..]],
            &rest,
            Some(&live.transient),
        )
        .unwrap();
    let next = [held.state[0].clone(), held.state[1].clone()].concat();
    assert_eq!(sample(&live.pair, &next), LockSample::Sheet(1));
    eprintln!("margin holds an in-phase drive of {scale} on every node (unit {unit})");
    // Storage waves against the sheet, through the live word. Amplitude 6 leaves the ball and the
    // field returns it to the same sheet: unlocked samples, no event. Amplitude 8 flips it with
    // one event. Amplitude 16 flips it and rings at the far ball's boundary: one event, however
    // often the samples leave and re-enter that ball.
    for (z, end, change) in [(6, 1, None), (8, -1, Some(99)), (16, -1, Some(118))] {
        let mut flipped = word(
            field,
            operands(&live.resident, live.resident.constitution()),
            live.ring,
            Some([centre[..width].to_vec(), centre[width..].to_vec()]),
            wave(field, live.ring, &integer(z), -1, 0),
        );
        let read = sampled(&mut flipped, live.ring, &live.pair, 192);
        let unlocked = read
            .samples
            .iter()
            .filter(|s| **s == LockSample::Unlocked)
            .count();
        eprintln!(
            "against {z}: events={:?} unlocked={unlocked} held={} exceeded={}",
            read.events, read.held, read.exceeded
        );
        assert_eq!(*read.samples.last().unwrap(), LockSample::Sheet(end));
        let mut expected = vec![LockEvent {
            from: None,
            to: 1,
            at: 0,
        }];
        expected.extend(change.map(|at| LockEvent {
            from: Some(1),
            to: -1,
            at,
        }));
        assert_eq!(read.events, expected, "one event per change of ball");
        assert!(unlocked > 0 && read.exceeded > 0);
    }
}

/// The founded material with its pump removed: strength zero, the saturation kept.
fn unpumped(live: &Live) -> Constitution {
    bare(
        live.resident.constitution(),
        live.resident.field(),
        live.ring,
        Some(removed()),
    )
}

/// The removed pump: a standing pump of strength zero.
fn removed() -> PumpDeclaration {
    PumpDeclaration::new(Rat::zero(), Carrier::at(&Rat::zero()), PumpStep::Stand).unwrap()
}

/// `constitution` with ring `ring`'s pump replaced by `pump`, its dissipation and saturation kept.
fn bare(
    constitution: &Constitution,
    field: &Field,
    ring: usize,
    pump: Option<PumpDeclaration>,
) -> Constitution {
    let material = constitution.ring_resonator(ring).unwrap();
    let (_, _, dissipation) = material.forms();
    let d = dissipation.get(0, 0).unwrap().clone();
    let bare = ResonatorMaterial::of_parametron(field.ring(ring).parametron(), &d, pump)
        .unwrap()
        .with_symmetric_saturation(material.saturation().unwrap().coefficient().clone())
        .unwrap();
    constitution
        .clone()
        .with_ring_resonator(field, ring, bare)
        .unwrap()
}

#[test]
fn the_sheet_reads_the_arrivals_relative_phase_and_vanishes_without_the_pump() {
    let live = live();
    let field = live.resident.field();
    let z = rat(1, 8);
    let quarters = [(1, 0), (0, 1), (-1, 0), (0, -1)];
    let read = |constitution: &Constitution| -> Vec<LockSample> {
        quarters
            .iter()
            .map(|&(re, im)| {
                let mut opened = word(
                    field,
                    operands(&live.resident, constitution),
                    live.ring,
                    None,
                    wave(field, live.ring, &z, re, im),
                );
                *sampled(&mut opened, live.ring, &live.pair, 192)
                    .samples
                    .last()
                    .unwrap()
            })
            .collect()
    };
    let pumped = read(live.resident.constitution());
    eprintln!("pumped sheets by quarter turn={pumped:?}");
    // A half turn of the arrival reflects the sheet; the quarter turns lock through the field's
    // own transport of the arrival onto the pump's axis.
    use LockSample::Sheet;
    assert_eq!(pumped, vec![Sheet(1), Sheet(1), Sheet(-1), Sheet(-1)]);
    let bare = unpumped(&live);
    let unlocked = read(&bare);
    eprintln!("unpumped samples by quarter turn={unlocked:?}");
    assert!(unlocked.iter().all(|s| *s == LockSample::Unlocked));
}

/// `F(x+v) − F(x−v)` and its double, combined so that a cubic's derivative is exact.
fn exact_derivative(f: &dyn Fn(&[Rat]) -> Vec<Rat>, x: &[Rat], v: &[Rat]) -> Vec<Rat> {
    let at = |t: i64| -> Vec<Rat> {
        f(&x.iter()
            .zip(v)
            .map(|(a, b)| a + integer(t) * b)
            .collect::<Vec<_>>())
    };
    let (p1, m1, p2, m2) = (at(1), at(-1), at(2), at(-2));
    (0..p1.len())
        .map(|i| {
            let d1 = (&p1[i] - &m1[i]) / integer(2);
            let d2 = (&p2[i] - &m2[i]) / integer(4);
            (integer(4) * d1 - d2) / integer(3)
        })
        .collect()
}

fn pairing(a: &[Rat], b: &[Rat]) -> Rat {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

#[test]
fn the_adjoint_versioned_per_tick_matches_the_exact_difference_across_a_pumped_tick() {
    let live = live();
    let field = live.resident.field();
    let width = field.ring(live.ring).width();
    // A live trajectory leaving rest under an arrival: generic producing states.
    let mut opened = word(
        field,
        operands(&live.resident, live.resident.constitution()),
        live.ring,
        None,
        wave(field, live.ring, &rat(1, 8), 1, 0),
    );
    sampled(&mut opened, live.ring, &live.pair, 6);
    let resonator: &ResonatorOperands = opened.operands().resonators()[live.ring].as_ref().unwrap();
    let steps = &opened.resonances()[live.ring].as_ref().unwrap().steps;
    let (tick, earlier) = (&steps[5], &steps[2]);
    assert_ne!(tick.input[0], earlier.input[0]);
    // The unsplit executed tick (the live chart, no splits): (u, w, e) ↦ (u′, w′, s′).
    let rest = ResonatorRemainders::default();
    let map = |x: &[Rat]| -> Vec<Rat> {
        let executed = resonator
            .step(
                5,
                &x[2 * width..],
                [&x[..width], &x[width..2 * width]],
                &rest,
                None,
            )
            .unwrap();
        [
            executed.state[0].clone(),
            executed.state[1].clone(),
            executed.output.clone(),
        ]
        .concat()
    };
    let x = [
        tick.input[0].clone(),
        tick.input[1].clone(),
        tick.drive.clone(),
    ]
    .concat();
    let probe = |seed: i64| -> Vec<Rat> {
        (0..3 * width)
            .map(|i| rat(((i as i64 * seed) % 7) - 3, 64))
            .collect()
    };
    let (v, lambda) = (probe(3), probe(5));
    let forward = pairing(&lambda, &exact_derivative(&map, &x, &v));
    // The unsplit reverse: every split keeps its whole image.
    let reversed = |step: &holonics::hnn::ring::ResonatorStep| -> Rat {
        let back = resonator
            .reverse(
                step,
                [&lambda[..width], &lambda[width..2 * width]],
                &lambda[2 * width..],
                &mut |_: ReverseSplit, image: Vec<Rat>| image,
            )
            .unwrap();
        pairing(&back.state[0], &v[..width])
            + pairing(&back.state[1], &v[width..2 * width])
            + pairing(&back.drive, &v[2 * width..])
    };
    assert_eq!(
        reversed(tick),
        forward,
        "the tick's own Hessian pairs exactly"
    );
    // The same reverse read at another tick's displacement is a different, wrong transpose.
    let mut stale = tick.clone();
    stale.input[0] = earlier.input[0].clone();
    assert_ne!(reversed(&stale), forward, "a stale Hessian does not pair");
    assert!(tick.pump.is_zero() && !tick.port.is_zero());
}

/// The receiving face along the live word after an arrival: at each tick, the receiving ring's
/// anchor `v_R` (the face the receiving map reads), the logits `Z = R v_R`, and the resonator's
/// state `(u, w)` the lock samples.
struct Face {
    anchors: Vec<Vec<Rat>>,
    logits: Vec<Vec<Rat>>,
    states: Vec<Vec<Rat>>,
}

fn face(
    resident: &Resident,
    constitution: &Constitution,
    ring: usize,
    arrival: Vec<Rat>,
    ticks: usize,
) -> Face {
    let field = resident.field();
    let mut opened = word(field, operands(resident, constitution), ring, None, arrival);
    let map = constitution.receiving_map(ring).unwrap().clone();
    let (mut anchors, mut logits, mut states) = (Vec::new(), Vec::new(), Vec::new());
    for at in 0..ticks {
        let balance = opened.tick().unwrap();
        assert!(balance.closes(), "tick {at}'s executed balance closes");
        let anchor = opened.anchor(at, ring).unwrap().to_vec();
        logits.push(map.apply(&anchor).unwrap());
        anchors.push(anchor);
        states.push(state_of(&opened, ring));
    }
    Face {
        anchors,
        logits,
        states,
    }
}

/// Whether two faces point to one side within an eighth of a turn: `⟨a, b⟩ > 0` and
/// `2⟨a, b⟩² ≥ |a|²|b|²`.
fn aligned(a: &[Rat], b: &[Rat]) -> bool {
    let ab = pairing(a, b);
    ab > Rat::zero() && integer(2) * &ab * &ab >= pairing(a, a) * pairing(b, b)
}

/// Whether the arrivals' faces separate by `sheets`: one side within a sheet, opposite sides across
/// sheets (a half turn reflecting the face).
fn separates(faces: &[&Vec<Rat>], sheets: &[i8]) -> bool {
    (0..faces.len()).all(|p| {
        (p + 1..faces.len()).all(|q| {
            if sheets[p] == sheets[q] {
                aligned(faces[p], faces[q])
            } else {
                let opposite: Vec<Rat> = faces[q].iter().map(|x| -x.clone()).collect();
                aligned(faces[p], &opposite)
            }
        })
    })
}

/// `⟨a, b⟩²/(|a|²|b|²)` with the sign of `⟨a, b⟩`, for the receipt: its exact enclosure between
/// the neighbouring multiples of `2^(−grain)` (the word's transient unit).
fn cosine(a: &[Rat], b: &[Rat], grain: u32) -> String {
    let ab = pairing(a, b);
    let norms = pairing(a, a) * pairing(b, b);
    if norms.is_zero() {
        return "a zero face".to_string();
    }
    let square = &ab * &ab / norms;
    let unit = holonics::holon::deposition::dyadic(-i64::from(grain));
    let low = (&square / &unit).floor() * &unit;
    let high = (&square / &unit).ceil() * &unit;
    let sign = if ab < Rat::zero() { "-" } else { "+" };
    format!("{sign}[{low}, {high}]")
}

/// The receiving ring's pump in a learned run.
#[derive(Clone, Copy, Debug)]
enum Pump {
    /// As [`super::mounted`] founds it.
    Founded,
    /// Removed: a standing pump of strength zero, the saturation kept.
    Removed,
    /// Not declared, the saturation kept.
    Undeclared,
}

/// The listener as [`super::mounted`] founds it, or with ring 2's pump replaced (`pump`) before the
/// pairing places its ports (a learned law is never founded again), after `cells` delivered cells
/// (classes `0, 1, 2, 3, 0, …`) through the listener's observed deposit, with each deposit's
/// reading.
fn learned(pump: Pump, cells: usize) -> (Resident, Vec<DepositReading>) {
    let port = Reference::new(4, BUDGET);
    let (mut resident, pairing) = mounted(&port, 65536).unwrap();
    let replaced = match pump {
        Pump::Founded => None,
        Pump::Removed => Some(Some(removed())),
        Pump::Undeclared => Some(None),
    };
    if let Some(replaced) = replaced {
        let field = resident.field().clone();
        let ring = field.receivers()[0].ring;
        let founded = Constitution::initial(&field, BUDGET)
            .unwrap()
            .with_locking_pump(&field, ring)
            .unwrap();
        let material =
            PairedCarrier::found(&field, bare(&founded, &field, ring, replaced), 0, &pairing)
                .unwrap()
                .0;
        resident = port
            .mount_with(&field, &Current::at_rest(&field), material)
            .unwrap();
    }
    let mut crib = ObservedCrib::new(0);
    let readings = (0..cells)
        .map(|cell| {
            port.observe_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                cell % 4,
                None,
                |_, _, _, _, reading| reading.clone(),
            )
            .unwrap()
            .view
        })
        .collect();
    (resident, readings)
}

/// The acceptance at the listener's face (the design review's item (c)). Four arrivals of `1/8` at
/// the quarter-turn carriers, from rest, through the live word on the material the listener learned
/// over four cells, its receiving map nonzero. With the pump, every arrival locks and at the station
/// after the last lock event the receiving face (`v_R` and `Z = R v_R`) separates by sheet: the two
/// arrivals of one sheet point to one side, a half turn reflects it. With the pump removed (strength
/// zero, the saturation kept, learned over the same cells) nothing locks and the same station's face
/// does not separate.
#[test]
fn the_receiving_face_separates_by_sheet_and_not_without_the_pump() {
    let z = rat(1, 8);
    let quarters = [(1, 0), (0, 1), (-1, 0), (0, -1)];
    let ticks = 192;
    let read = |unpumped: bool| -> (Vec<Face>, Option<LockedPair>, u32) {
        let (resident, _) = learned(
            if unpumped {
                Pump::Removed
            } else {
                Pump::Founded
            },
            4,
        );
        let field = resident.field();
        let ring = field.receivers()[0].ring;
        let constitution = resident.constitution();
        let map = constitution.receiving_map(ring).unwrap();
        assert!(
            (0..map.rows()).any(|i| (0..map.columns()).any(|j| !map.get(i, j).unwrap().is_zero())),
            "the learned receiving map reads the face"
        );
        let opened = operands(&resident, constitution);
        let transient = opened.lattice().unwrap().transient();
        let pair = (!unpumped).then(|| {
            opened.resonators()[ring]
                .as_ref()
                .unwrap()
                .executed_lock(Some(&transient))
                .unwrap()
        });
        let faces = quarters
            .iter()
            .map(|&(re, im)| {
                face(
                    &resident,
                    constitution,
                    ring,
                    wave(field, ring, &z, re, im),
                    ticks,
                )
            })
            .collect();
        (faces, pair, transient.exponent())
    };
    let (pumped, pair, grain) = read(false);
    let pair = pair.unwrap();
    // Each arrival's lock events; the station is the tick after the last of them.
    let mut sheets = Vec::new();
    let mut last_event = 0;
    for (q, face) in pumped.iter().enumerate() {
        let mut last = None;
        for (at, state) in face.states.iter().enumerate() {
            let (now, event) = observe(&pair, last, state, at as u64);
            if let LockSample::Sheet(sheet) = now {
                last = Some(sheet);
            }
            if event.is_some() {
                last_event = last_event.max(at);
            }
        }
        let LockSample::Sheet(sheet) = sample(&pair, face.states.last().unwrap()) else {
            panic!("arrival {q} locks with the pump");
        };
        sheets.push(sheet);
    }
    assert_eq!(sheets, vec![1, 1, -1, -1]);
    let station = last_event + 1;
    assert!(station < ticks, "the station follows the last lock event");
    let (bare, _, _) = read(true);
    for (name, faces) in [("pumped", &pumped), ("unpumped", &bare)] {
        for t in [12, 24, 48, 96, station, ticks - 1] {
            let anchors: Vec<String> = (1..4)
                .map(|q| cosine(&faces[q].anchors[t], &faces[0].anchors[t], grain))
                .collect();
            let logits: Vec<String> = (1..4)
                .map(|q| cosine(&faces[q].logits[t], &faces[0].logits[t], grain))
                .collect();
            eprintln!("{name} t={t}: signed cos² to arrival 0: v_R={anchors:?} Z={logits:?}");
        }
    }
    let at = |faces: &[Face], logits: bool| -> Vec<Vec<Rat>> {
        faces
            .iter()
            .map(|face| {
                if logits {
                    face.logits[station].clone()
                } else {
                    face.anchors[station].clone()
                }
            })
            .collect()
    };
    for logits in [false, true] {
        let pumped_face = at(&pumped, logits);
        let bare_face = at(&bare, logits);
        assert!(
            separates(&pumped_face.iter().collect::<Vec<_>>(), &sheets),
            "with the pump the face (logits: {logits}) separates by sheet at tick {station}"
        );
        assert!(
            !separates(&bare_face.iter().collect::<Vec<_>>(), &sheets),
            "without the pump the face (logits: {logits}) does not separate at tick {station}"
        );
    }
}

/// Whether a deposit stepped a source port at a positive step.
fn source_stepped(reading: &DepositReading) -> bool {
    reading
        .steps
        .iter()
        .any(|(locus, step)| matches!(locus, Locus::SourcePort(_)) && step.step.step > Rat::zero())
}

#[test]
fn the_deposit_reads_the_pumped_ring_on_its_tube_and_steps_the_source_through_it() {
    let ring = live().ring;
    let (_, readings) = learned(Pump::Founded, 6);
    let mut read = 0;
    for (cell, reading) in readings.iter().enumerate() {
        let Some(pumped) = reading.pumped.as_ref() else {
            eprintln!("cell {cell}: nothing stepped, no reach read");
            continue;
        };
        read += 1;
        let reached = pumped
            .rings
            .iter()
            .find(|reached| reached.ring == ring)
            .expect("the receiving ring's reach is read");
        let RingReading::Tube(tube) = &reached.reading else {
            panic!("cell {cell}: the saturated ring is read on its tube");
        };
        assert!(tube.radius > tube.distance);
        let closure = pumped
            .closures
            .iter()
            .find(|closure| closure.ring == ring)
            .expect("the tube's closure is read");
        assert!(
            closure.holds(),
            "cell {cell}: the stepped passage stays in the tube"
        );
        eprintln!(
            "cell {cell}: tube centre={:?} distance={} radius={} variation={} tangent={} sigma={} \
             young={:?} low={} high={} span={} reach={} factor={} rung={} deviation={} slack={} \
             source_stepped={} held={:?}",
            tube.centre,
            tube.distance,
            tube.radius,
            tube.variation,
            tube.tangent,
            tube.bound.growth,
            tube.young,
            tube.bound.low,
            tube.bound.high,
            pumped.span,
            reached.reach.last().unwrap(),
            pumped.factor,
            closure.rung,
            closure.deviation,
            closure.slack,
            source_stepped(reading),
            pumped.held,
        );
    }
    assert!(read > 0, "some cell steps through the pumped ring");
    assert!(
        readings.iter().any(source_stepped),
        "the source port's certified step is nonzero through the pumped ring"
    );
}

/// With the pump removed (strength zero) the saturated ring's period has one rest point, the
/// origin, and its tube's tangent is the unpumped tick's: every deposit reads as it does on the ring
/// declared with no pump at all, the same saturation and dissipation, over the same cells.
#[test]
fn with_the_pump_removed_the_reading_reverts_to_the_unpumped_one() {
    let (resident, removed) = learned(Pump::Removed, 6);
    let (_, undeclared) = learned(Pump::Undeclared, 6);
    let ring = resident.field().receivers()[0].ring;
    let mut read = 0;
    for (cell, (removed, undeclared)) in removed.iter().zip(&undeclared).enumerate() {
        assert_eq!(removed.steps, undeclared.steps, "cell {cell}: the steps");
        assert_eq!(
            removed.joint, undeclared.joint,
            "cell {cell}: the joint step"
        );
        assert_eq!(removed.pumped, undeclared.pumped, "cell {cell}: the reach");
        let Some(reached) = removed
            .pumped
            .as_ref()
            .and_then(|pumped| pumped.rings.iter().find(|reached| reached.ring == ring))
        else {
            eprintln!("cell {cell}: the unpumped ring's reach is not read");
            continue;
        };
        let RingReading::Tube(tube) = &reached.reading else {
            panic!("cell {cell}: the saturated ring is read on its tube");
        };
        assert_eq!(
            tube.centre,
            TubeCentre::Origin,
            "cell {cell}: the only rest point"
        );
        read += 1;
        eprintln!(
            "cell {cell}: unpumped tube distance={} radius={} variation={} tangent={} sigma={} \
             young={:?} reach={} source_stepped={}",
            tube.distance,
            tube.radius,
            tube.variation,
            tube.tangent,
            tube.bound.growth,
            tube.young,
            reached.reach.last().unwrap(),
            source_stepped(removed),
        );
    }
    assert!(read > 0, "some cell reads the unpumped ring on its tube");
    assert!(removed.iter().any(source_stepped));
}

#[test]
fn inside_a_lock_ball_the_tube_contracts_and_across_the_saddle_it_amplifies() {
    let live = live();
    let opened = operands(&live.resident, live.resident.constitution());
    let resonator = opened.resonators()[live.ring].as_ref().unwrap();
    let grain = 15;
    let step = live.pair.positive().domain().step(0).unwrap();
    let proposal = step.proposal();
    // A passage that stays at the sheet's centre, on the ball's own radius.
    let width = resonator.width();
    let centre = proposal.centre[..width].to_vec();
    let passage = resonator.passage([centre.as_slice()]).unwrap();
    assert_eq!(passage.nearest().0, TubeCentre::Sheet(1));
    let inside = resonator
        .tube_reach(&passage, &proposal.euclidean_radius, grain)
        .unwrap();
    eprintln!(
        "lock ball: sigma={} tangent={} variation={} young={:?} lambda={}",
        inside.bound.growth, inside.tangent, inside.variation, inside.young, proposal.lipschitz
    );
    assert!(
        inside.bound.growth <= proposal.lipschitz,
        "σ ≤ λ inside the ball"
    );
    assert!(inside.bound.growth < Rat::one());
    // A passage that stays at rest, on the saddle's tube of the same radius.
    let rest = vec![Rat::zero(); width];
    let saddle = resonator.passage([rest.as_slice()]).unwrap();
    assert_eq!(saddle.nearest().0, TubeCentre::Origin);
    let across = resonator
        .tube_reach(&saddle, &proposal.euclidean_radius, grain)
        .unwrap();
    eprintln!(
        "saddle: sigma={} tangent={} variation={}",
        across.bound.growth, across.tangent, across.variation
    );
    assert!(across.bound.growth > Rat::one(), "σ > 1 across the saddle");
}
