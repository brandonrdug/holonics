//! The Holon ratio at the receiver's face and the carried power: the covector's two parts, the
//! target's phase and its winding, a common rechart, exact normalization in `ℚ(θ)`, the face's
//! constancy on its fibre, the code tolerance of the grain, and the uniform first face.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use super::learning::chain;
use super::support::Draw;
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, Steps};
use crate::hnn::field::{Current, Field, FieldDeclaration};
use crate::hnn::moment::SourceMoment;
use crate::hnn::port::ExecutionPort;
use crate::hnn::ratio::{
    Face, Faces, HolonRatio, TargetPhases, code_face, code_margin, interval_difference,
    log2_of_enclosure, power_of_two_enclosure, target_phases,
};
use crate::hnn::receiving::{GrainCell, ReceivingPhases, ReceivingRead};
use crate::hnn::reference::{Reference, one_hot};
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::exponentiated::{CarriedPower, PhaseField, power_of_two};
use crate::ratio::{Rat, integer, rat};

/// A receiving read of realified logits `[Re, Im, …]` at a grain.
fn read(logits: Vec<Rat>, grain: u64) -> ReceivingRead {
    ReceivingRead {
        cells: logits
            .chunks(2)
            .map(|pair| GrainCell::of(&pair[0], grain))
            .collect(),
        phases: logits.chunks(2).map(|pair| &pair[1] / integer(2)).collect(),
        logits,
    }
}

fn logits(values: &[(Rat, Rat)]) -> Vec<Rat> {
    values
        .iter()
        .flat_map(|(re, im)| [re.clone(), im.clone()])
        .collect()
}

/// Target phases read in a cut's frame whose winding is `branch`.
fn window(branch: i64, phases: Vec<Rat>) -> TargetPhases {
    TargetPhases {
        branch: BigInt::from(branch),
        phases,
    }
}

fn below(a: &ExactInterval, bound: &Rat) -> bool {
    &a.upper < bound && &-a.lower.clone() < bound
}

/// Lean `HNN/Ratio.odometer_covector_descends`, `odometer_eq_face_at_integer_cells`: the real
/// covector is `p̃ − q` in the declared odometer chart, `p̃_c ∝ 2^(n_c)(L + k_c)`; it sums to zero, it
/// is a strict descent direction of the scored code length (`⟨p̂ − q, p̃ − q⟩ > 0`, read here on
/// the real chart's enclosure of `p̂`), and at `L = 1` the odometer chart and the exact face agree.
#[test]
fn the_real_covector_is_the_face_minus_the_target_at_the_cell_representative() {
    let values = [
        (rat(3, 2), rat(1, 3)),
        (rat(-1, 3), integer(0)),
        (rat(5, 16) + rat(1, 64), rat(-2, 5)),
        (integer(0), integer(1)),
    ];
    let faces = Faces::of_reads(&[read(logits(&values), 16)], 16).unwrap();
    let ratio = HolonRatio::compare(faces, &[2], &window(0, vec![rat(1, 3)])).unwrap();
    let covector = ratio.covector().unwrap();
    let weights: Vec<Rat> = values
        .iter()
        .map(|(re, _)| {
            let cell = GrainCell::of(re, 16);
            power_of_two(&cell.carry).unwrap() * Rat::from_integer(BigInt::from(16 + cell.phase))
        })
        .collect();
    let total: Rat = weights.iter().sum();
    for (class, weight) in weights.iter().enumerate() {
        let target = if class == 2 { Rat::one() } else { Rat::zero() };
        assert_eq!(covector.logits()[0][2 * class], weight / &total - target);
    }
    let sum: Rat = covector.logits()[0].iter().step_by(2).sum();
    assert!(sum.is_zero());
    // ⟨p̂ − q, p̃ − q⟩ > 0, with p̂ read from its enclosure: the lower bound of the pairing.
    let face = &ratio.faces().faces[0];
    let mut pairing = Rat::zero();
    for (class, entry) in covector.logits()[0].iter().step_by(2).enumerate() {
        let mass = face.mass(class).unwrap().enclosure().unwrap();
        let target = if class == 2 { Rat::one() } else { Rat::zero() };
        let (low, high) = (&mass.lower - &target, &mass.upper - &target);
        pairing += if entry.is_negative() {
            entry * high
        } else {
            entry * low
        };
    }
    assert!(pairing.is_positive(), "{pairing}");
    // At L = 1 the two charts agree: the exact face is rational and equals the odometer masses.
    let coarse = Face::of_read(&read(logits(&values), 1), 1).unwrap();
    for (class, mass) in coarse.odometer_masses().unwrap().iter().enumerate() {
        assert_eq!(coarse.mass(class).unwrap().as_rational(), Some(mass));
    }
}

/// Lean `HNN/Ratio.alignCost_turns`, `receivingPhase_phase_pullback`: the phase covector is
/// `−½ q_c Δ_c` on `Im f_c` (`−q_c Δ_c` on the phase in turns), zero off the target class, with
/// `Δ` the windowed gap; the cut's winding is the log's branch and never enters the covector or
/// the excess `½ Δ²`.
#[test]
fn the_phase_covector_is_minus_the_windowed_gap_and_the_winding_its_branch() {
    let values = [(integer(0), integer(3)), (integer(1), rat(1, 2))];
    let faces = Faces::of_reads(&[read(logits(&values), 16)], 16).unwrap();
    let target_phase = rat(1, 3);
    let ratio = HolonRatio::compare(faces, &[1], &window(7, vec![target_phase.clone()])).unwrap();
    let gap = &target_phase - rat(1, 4);
    let phase = &ratio.phases()[0];
    assert_eq!(phase.gap.windings(), &BigInt::zero());
    assert_eq!(phase.gap.phase(), &rat(1, 12));
    assert_eq!(phase.winding(), BigInt::from(7));
    assert_eq!(phase.excess, &gap * &gap / integer(2));
    let covector = ratio.covector().unwrap();
    assert_eq!(covector.logits()[0][3], -&gap / integer(2));
    assert!(covector.logits()[0][1].is_zero());
    let lift = ratio.log_ratio(0).unwrap();
    assert_eq!(lift.winding, 7);
    // The same window at another cut's winding: the covector and the excess do not move.
    let faces = Faces::of_reads(&[read(logits(&values), 16)], 16).unwrap();
    let far = HolonRatio::compare(faces, &[1], &window(521, vec![target_phase])).unwrap();
    assert_eq!(far.covector().unwrap(), covector);
    assert_eq!(far.phases()[0].excess, phase.excess);
    assert_eq!(far.log_ratio(0).unwrap().winding, 521);
}

/// Review C1: over a long stream the receiving ring's clock winds without bound (`τ_R/d_R` passes
/// hundreds of turns), but every window's target phase, read in its cut's frame, stays in
/// `[0, 1 + 2A/d_R)`, and its branch is the cut's winding; so the phase covector against a produced
/// phase of zero stays below one, the scale of the magnitude part (on the chain control, whose
/// receiving ring of period 2 steps only by carry).
#[test]
fn the_windowed_gap_stays_bounded_over_a_long_stream() {
    let field = &chain();
    let (ring, aperture, alphabet) = (2usize, 2usize, field.alphabet());
    let period = BigInt::from(field.ring(ring).period());
    let bound = integer(1) + Rat::new(BigInt::from(2 * aperture), period.clone());
    let mut draw = Draw::new(97);
    let stream: Vec<usize> = (0..6_000).map(|_| draw.below(alphabet)).collect();
    let mut current = Current::at_rest(field);
    let mut widest = Rat::zero();
    let zeros = read(vec![Rat::zero(); 2 * alphabet], 16);
    for (start, cells) in stream.chunks(aperture).enumerate() {
        if cells.len() == aperture && start % 29 == 0 {
            let window = target_phases(field, current.lift(), ring, cells).unwrap();
            assert_eq!(window.branch, current.winding(field, ring).unwrap());
            for phase in &window.phases {
                assert!(!phase.is_negative() && phase < &bound, "{phase}");
                widest = widest.max(phase.clone());
            }
            let faces = Faces::of_reads(&[zeros.clone(), zeros.clone()], 16).unwrap();
            let ratio = HolonRatio::compare(faces, cells, &window).unwrap();
            let covector = ratio.covector().unwrap();
            for (phase, target) in covector.logits().iter().zip(cells) {
                let entry = &phase[2 * target + 1];
                assert!(entry.abs() < Rat::one(), "{entry}");
            }
        }
        for &code in cells {
            current.step(field, code).unwrap();
        }
    }
    let turns = Rat::new(current.lift()[ring].clone(), period);
    assert!(turns > integer(100), "the stream winds: {turns}");
    assert!(widest < bound);
}

/// A target's phase is `(τ_R(j) − d_R w)/d_R` from selective stepping over the targets, read in
/// the cut's frame with the cut's winding `w` the branch; ingesting those targets afterwards
/// reaches the same `λ_R`.
#[test]
fn a_targets_phase_is_its_clock_and_ingesting_the_targets_reaches_it() {
    let field = &chain();
    let period = BigInt::from(field.ring(2).period());
    let mut draw = Draw::new(5);
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    let history: Vec<usize> = (0..300).map(|_| draw.below(4)).collect();
    let mut fed = 0;
    while fed < history.len() {
        fed += moment
            .ingest(field, &mut current, &history[fed..])
            .unwrap()
            .cells;
    }
    let targets = [0usize, 3, 2, 0, 3, 1];
    let window = target_phases(field, current.lift(), 2, &targets).unwrap();
    assert_eq!(window.branch, current.winding(field, 2).unwrap());
    let floor = &window.branch * &period;
    let mut fed = 0;
    while fed < targets.len() {
        fed += moment
            .ingest(field, &mut current, &targets[fed..])
            .unwrap()
            .cells;
    }
    let last = window.phases.last().unwrap();
    assert_eq!(*last, Rat::new(&current.lift()[2] - &floor, period));
    assert_eq!(
        &window.branch + last.floor().to_integer(),
        current.winding(field, 2).unwrap()
    );
}

/// Lean `HNN/Ratio.receivingPhase_ratio`: a common rechart (an integer shift of every magnitude
/// logit, and one phase shift of the produced and target phases together) leaves the code length
/// and the gap; a one-sided rechart of the produced phase moves the gap
/// (`produced_rechart_moves_the_ratio`).
#[test]
fn a_common_rechart_leaves_the_ratio() {
    let mut draw = Draw::new(8);
    let values: Vec<(Rat, Rat)> = (0..5).map(|_| (draw.rational(), draw.rational())).collect();
    let shift = rat(5, 7);
    let moved: Vec<(Rat, Rat)> = values
        .iter()
        .map(|(re, im)| (re + integer(3), im + integer(2) * &shift))
        .collect();
    let target = rat(9, 4);
    let at = |values: &[(Rat, Rat)], phase: Rat| {
        HolonRatio::compare(
            Faces::of_reads(&[read(logits(values), 16)], 16).unwrap(),
            &[3],
            &window(4, vec![phase]),
        )
        .unwrap()
    };
    let before = at(&values, target.clone());
    let after = at(&moved, &target + &shift);
    assert_eq!(
        before.phases()[0].code_length,
        after.phases()[0].code_length
    );
    assert_eq!(before.phases()[0].gap, after.phases()[0].gap);
    let one_sided = at(&moved, target.clone());
    assert_eq!(
        one_sided.phases()[0].gap.turns(),
        before.phases()[0].gap.turns() - &shift
    );
}

/// Lean `Objects/Ratio/CarriedPower.carriedPower_exact`, `HNN/Ratio.face_constant_on_fibre`:
/// `2^n θ^k` carries by multiplication by 2, `θ^L = 2`, the face normalizes exactly in `ℚ(θ)`,
/// and two logits in one grain cell read one face.
#[test]
fn the_carried_power_normalizes_exactly_and_the_face_is_constant_on_its_fibre() {
    let grain = 16;
    let a = CarriedPower::new(BigInt::from(1), 12, grain).unwrap();
    let b = CarriedPower::new(BigInt::from(0), 7, grain).unwrap();
    assert_eq!(
        a.times(&b).unwrap(),
        CarriedPower::new(BigInt::from(2), 3, grain).unwrap()
    );
    let root = CarriedPower::new(BigInt::zero(), 8, grain).unwrap();
    assert_eq!(
        root.times(&root).unwrap().value().unwrap(),
        PhaseField::rational(integer(2), grain)
    );
    let mut draw = Draw::new(21);
    let values: Vec<(Rat, Rat)> = (0..6).map(|_| (draw.rational(), draw.rational())).collect();
    let face = Face::of_read(&read(logits(&values), grain), grain).unwrap();
    let mut total = PhaseField::zero(grain);
    for class in 0..values.len() {
        total = total.plus(&face.mass(class).unwrap()).unwrap();
    }
    assert_eq!(total, PhaseField::rational(Rat::one(), grain));
    // Move every logit within its cell: the cells, masses and code lengths stay.
    let nudged: Vec<(Rat, Rat)> = values
        .iter()
        .map(|(re, im)| {
            let cell = GrainCell::of(re, grain);
            (cell.representative(grain) + rat(1, 64), im.clone())
        })
        .collect();
    let other = Face::of_read(&read(logits(&nudged), grain), grain).unwrap();
    for class in 0..values.len() {
        assert_eq!(face.mass(class).unwrap(), other.mass(class).unwrap());
        assert_eq!(
            face.code_length(class).unwrap(),
            other.code_length(class).unwrap()
        );
    }
}

/// Lean `HNN/Ratio.face_code_length_within_grain`, `reading_beyond_the_grain_moves_the_code`:
/// reading every exponent down within its cell moves each code length by less than `1/L_R` bits;
/// read at a coarser grain than the tolerance, it moves by more.
#[test]
fn reading_every_exponent_down_moves_each_code_length_by_less_than_the_grain() {
    let exact = |values: &[Rat], class: usize| -> ExactInterval {
        let mut lower = Rat::zero();
        let mut upper = Rat::zero();
        for value in values {
            let power = power_of_two_enclosure(&(value - &values[class])).unwrap();
            lower += power.lower;
            upper += power.upper;
        }
        log2_of_enclosure(&ExactInterval::new(lower, upper).unwrap()).unwrap()
    };
    let mut draw = Draw::new(34);
    for _ in 0..2 {
        let values: Vec<Rat> = (0..3).map(|_| draw.rational() + rat(1, 5)).collect();
        let face = Face::of_read(
            &read(
                values
                    .iter()
                    .flat_map(|v| [v.clone(), Rat::zero()])
                    .collect(),
                16,
            ),
            16,
        )
        .unwrap();
        for class in 0..values.len() {
            let moved =
                interval_difference(&face.code_length(class).unwrap(), &exact(&values, class))
                    .unwrap();
            assert!(below(&moved, &rat(1, 16)), "class {class}: {moved:?}");
        }
    }
    let beyond = [integer(0), rat(15, 16)];
    let coarse = Face::of_read(
        &read(
            logits(&[
                (beyond[0].clone(), Rat::zero()),
                (beyond[1].clone(), Rat::zero()),
            ]),
            1,
        ),
        1,
    )
    .unwrap();
    let moved = interval_difference(&coarse.code_length(1).unwrap(), &exact(&beyond, 1)).unwrap();
    assert!(moved.lower > rat(1, 16));
}

/// `ℚ(θ)` is a field: every nonzero value has an exact inverse.
#[test]
fn the_phase_field_inverts_exactly() {
    let mut draw = Draw::new(55);
    for grain in [2u64, 5, 16] {
        let field_value = PhaseField::rational(Rat::one(), grain)
            .shifted(1)
            .scaled(&draw.rational())
            .plus(&PhaseField::rational(integer(3), grain))
            .unwrap()
            .plus(&PhaseField::rational(draw.rational(), grain).shifted(grain - 1))
            .unwrap();
        let product = field_value.times(&field_value.inverse().unwrap()).unwrap();
        assert_eq!(product, PhaseField::rational(Rat::one(), grain));
    }
}

/// The declared initial constitution reads uniform faces: `E_0 = 0` makes every logit zero, so
/// every class of every refined face costs exactly `log₂|A|` bits, a point (`log₂ 4 = 2` on the
/// chain control; campaign 1's bytes cost 8).
#[test]
fn the_initial_faces_are_uniform_at_the_log_of_the_alphabet() {
    let field = &chain();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(field, &Current::at_rest(field)).unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[3, 1, 1, 2, 0]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (_, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let faces = refined.forward.into_present().unwrap();
    assert_eq!(faces.faces.len(), phases.aperture());
    for face in &faces.faces {
        for class in 0..field.alphabet() {
            assert_eq!(
                face.code_length(class).unwrap(),
                ExactInterval::point(integer(2))
            );
        }
    }
}

/// Decision 26, the target's code face: the receiver's margin is the least integer `m` whose face
/// `χ_R(T) = m·e_t` codes its own target within one grain, `(2^m + |A| − 1)^(L_R) ≤ 2^(m·L_R + 1)`,
/// read in exact integers: 13 at campaign 1's `|A| = 2^8`, `L_R = 2^4` (12 does not hold), 7 on the
/// chain's `|A| = 4`; the fields declare it by rule and the receiving phases carry it; the face's
/// code length of its target is at most `1/L_R` at `m` and more at `m − 1`.
#[test]
fn the_margin_is_the_least_code_face_within_one_grain() {
    let holds = |m: u64, alphabet: usize, grain: u64| {
        let face = (BigUint::one() << m as usize) + BigUint::from(alphabet - 1);
        face.pow(grain as u32) <= BigUint::one() << (m * grain + 1) as usize
    };
    for (alphabet, grain) in [
        (256usize, 16u64),
        (4, 16),
        (2, 1),
        (1, 16),
        (256, 1),
        (3, 5),
    ] {
        let m = code_margin(alphabet, grain);
        assert!(holds(m, alphabet, grain), "{alphabet} {grain}");
        assert!(
            m == 0 || !holds(m - 1, alphabet, grain),
            "{alphabet} {grain}"
        );
    }
    assert_eq!(code_margin(256, 16), 13);
    assert_eq!(code_margin(4, 16), 7);
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    assert_eq!(campaign.margins(), &[13]);
    let chain = chain();
    assert_eq!(chain.margins(), &[7]);
    let theta = Constitution::initial(&chain, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET).unwrap();
    let phases = ReceivingPhases::declare(
        &chain,
        &theta,
        &Current::at_rest(&chain),
        &chain.receivers()[0],
    )
    .unwrap();
    assert_eq!(phases.margin(), 7);
    let face = code_face(13, 5, 256).unwrap();
    assert_eq!(face.len(), 512);
    assert_eq!(face[10], integer(13));
    assert!(
        face.iter()
            .enumerate()
            .all(|(entry, value)| entry == 10 || value.is_zero())
    );
    let grain = rat(1, 16);
    let within = Face::of_read(&read(face, 16), 16).unwrap();
    assert!(within.code_length(5).unwrap().upper <= grain);
    let below = Face::of_read(&read(code_face(12, 5, 256).unwrap(), 16), 16).unwrap();
    assert!(below.code_length(5).unwrap().lower > grain);
    assert!(code_face(13, 256, 256).is_err());
}
