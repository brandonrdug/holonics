//! The locking pump on the live listener (the revised plan, step 1a): the receiving ring's
//! saturated resonator, founded by [`super::mounted`] with its two sheets certified on the period
//! the live word executes, read here through the live word itself. The authored values below are
//! test probes (injected storage waves, perturbations, covectors); none enters the founding.
use super::mounted;
use crate::octets::BUDGET;
use holonics::hnn::Floquet;
use holonics::hnn::chart::Charts;
use holonics::hnn::constitution::{Constitution, Lattice};
use holonics::hnn::field::{ConstitutionRead, Field};
use holonics::hnn::propagation::Operands;
use holonics::hnn::reference::{Reference, Resident};
use holonics::hnn::ring::{
    PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands, ResonatorRemainders,
    ReverseSplit,
};
use holonics::hnn::word::{EndChange, Word};
use holonics::holon::parametron::{Carrier, LockEvent, LockSample, LockedPair};
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
    let mut lying = pair.sample(&state_of(word, ring)).unwrap();
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
        let (sample, event) = pair
            .observe(last, &state_of(word, ring), at as u64)
            .unwrap();
        match margin {
            Some(true) => {
                held += 1;
                assert_eq!(sample, lying, "tick {at}: a held drive keeps its ball");
            }
            Some(false) => exceeded += 1,
            None => {}
        }
        if let LockSample::Sheet(sheet) = sample {
            last = Some(sheet);
        }
        lying = sample;
        samples.push(sample);
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
            live.pair.sample(&start).unwrap(),
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
    assert_eq!(live.pair.sample(&next).unwrap(), LockSample::Sheet(1));
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
    let field = live.resident.field();
    let material = live
        .resident
        .constitution()
        .ring_resonator(live.ring)
        .unwrap();
    let (_, _, dissipation) = material.forms();
    let d = dissipation.get(0, 0).unwrap().clone();
    let bare = ResonatorMaterial::of_parametron(
        field.ring(live.ring).parametron(),
        &d,
        Some(
            PumpDeclaration::new(Rat::zero(), Carrier::at(&Rat::zero()), PumpStep::Stand).unwrap(),
        ),
    )
    .unwrap()
    .with_symmetric_saturation(material.saturation().unwrap().coefficient().clone())
    .unwrap();
    live.resident
        .constitution()
        .clone()
        .with_ring_resonator(field, live.ring, bare)
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
