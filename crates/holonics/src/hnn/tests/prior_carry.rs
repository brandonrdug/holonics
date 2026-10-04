//! The receiving prior carried beside its Gram and moved to the code's cell (the
//! [prior carry's design](../../../../../research/records/2026-10-04_THE_RECEIVING_PRIOR_IS_CARRIED_BESIDE_ITS_GRAM_AND_MOVES_TO_THE_CODES_CELL.md)
//! §6; Lean `HNN/PriorCarry`): the window's terms read through the map before its deposit, the
//! pair carried with no tape, the move to the Newton point's cell with its Gram, map, chart and
//! rebased pair, a sign inside `ln 2`'s enclosure holding `k`, the floor at `2^0`, a held prior
//! unchanged, and a saved state restoring across a move.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::{chain_declaration, chain_reach};
use crate::hnn::HnnError;
use crate::hnn::constitution::{
    BudgetedCarry, ChartRule, Constitution, ContinuingState, Lattice, LinearLocus, LinearStep,
    LocatedPrior, Locus, NormalLaw, PriorHeld, Sample, prequential_terms,
};
use crate::hnn::field::{Field, ReceivingPrior};
use crate::hnn::port::Deposit;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

/// The chain control with its receiver's prior declared `prior`.
fn chain_at(prior: ReceivingPrior) -> Field {
    let mut declared = chain_declaration(1 << 16);
    declared.receivers[0].receiving_prior = prior;
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// A receiving reading: weight one, feature `z`, and the descent covector `q − p̃` of the masses
/// `p̃` against the target class `target` on the class entries, its phase entries `phase`.
fn reading(feature: &[Rat], masses: &[Rat], target: usize, phase: &Rat) -> Sample {
    let covector = masses
        .iter()
        .enumerate()
        .flat_map(|(c, p)| {
            let q = if c == target { Rat::one() } else { Rat::zero() };
            [q - p, phase.clone()]
        })
        .collect();
    Sample {
        weight: Rat::one(),
        feature: feature.to_vec(),
        covector,
    }
}

/// The window `t`'s receiving readings on a map of width `n` over `a` classes: dyadic features and
/// masses that turn with `t`.
fn window(t: usize, n: usize, a: usize) -> Vec<Sample> {
    (0..3)
        .map(|s| {
            let feature: Vec<Rat> = (0..n)
                .map(|j| rat(((t + 2 * s + 3 * j) % 5) as i64 - 2, 4))
                .collect();
            let lead = (t + s) % a;
            let masses: Vec<Rat> = (0..a)
                .map(|c| if c == lead { rat(5, 8) } else { rat(3, 8 * (a as i64 - 1)) })
                .collect();
            reading(&feature, &masses, (lead + 1 + s) % a, &rat(1, 16))
        })
        .collect()
}

/// One hand-built deposit of window `t` at the receiving map of ring `g` alone.
fn receiving_deposit(theta: &Constitution, g: usize, t: usize) -> Deposit {
    let map = theta.receiving_law(g).unwrap().map();
    let (rows, n) = (map.rows(), map.columns());
    Deposit::new(
        theta.commit(),
        vec![LinearStep {
            locus: LinearLocus::Receiving(g),
            samples: window(t, n, rows / 2),
        }],
        Vec::new(),
        vec![Locus::ReceivingMap(g)],
    )
    .with_reach(chain_reach())
}

/// `2^e` for a signed `e`.
fn power(e: i64) -> Rat {
    let p = BigInt::one() << e.unsigned_abs() as usize;
    if e >= 0 { Rat::from_integer(p) } else { Rat::new(BigInt::one(), p) }
}

/// A located run of `windows` hand-built receiving deposits on the chain from `2^from I`, with
/// each window's law before, its terms read independently at that law's map, and its prior read.
fn located_run(from: u32, windows: usize) -> Vec<(NormalLaw, (Rat, Rat), NormalLaw, crate::hnn::constitution::PriorMove)> {
    let field = chain_at(ReceivingPrior::Located { from });
    let mut theta = Constitution::initial(&field, 1 << 40).unwrap();
    (0..windows)
        .map(|t| {
            let deposit = receiving_deposit(&theta, 2, t);
            let before = theta.receiving_law(2).unwrap().clone();
            let terms = prequential_terms(&deposit.linear()[0].samples, before.map()).unwrap();
            let (next, reading) = theta.deposited(&deposit).unwrap();
            let [(locus, chart)] = reading.charts.as_slice() else {
                panic!("one chart reading, at the receiving map");
            };
            assert_eq!(*locus, Locus::ReceivingMap(2));
            let read = chart.prior.clone().expect("a located prior is read at every deposit");
            theta = next;
            (before, terms, theta.receiving_law(2).unwrap().clone(), read)
        })
        .collect()
}

/// **The terms are read before the deposit, and the pair keeps no tape** (§6, tests 1 and 2):
/// the first window reads the founding map `W₀ = 0`, so its terms are `(0, 0)` and nothing locates;
/// every later window's terms are read at the map before its deposit, computed independently here;
/// the pair after each window is the pair before it plus that window's terms, rebased by the move's
/// `x` where the prior moved (Lean `HNN/PriorCarry.{carried_append, carried_eq_sum}`,
/// `rebaseAt`), and between moves it is the sum of the windows' terms.
#[test]
fn the_pair_reads_each_window_through_the_map_before_its_deposit_and_keeps_no_tape() {
    let run = located_run(6, 8);
    assert_eq!(run[0].1, (Rat::zero(), Rat::zero()));
    assert_eq!(run[0].3.held, Some(PriorHeld::NoCurvature));
    let mut carried = LocatedPrior::from_parts(6, Rat::zero(), Rat::zero(), Rat::zero());
    let (mut moves, mut since) = (0, (Rat::zero(), Rat::zero()));
    for (before, terms, after, read) in &run {
        assert_eq!(read.from, before.chart().scale());
        assert_eq!(read.to, after.chart().scale());
        let mut expected = before.located().unwrap().clone();
        expected.read(terms);
        carried.read(terms);
        since = (&since.0 + &terms.0, &since.1 + &terms.1);
        if read.to != read.from {
            let x = power(i64::from(read.from) - i64::from(read.to));
            expected = expected.rebased(&x);
            carried = carried.rebased(&x);
            since = (Rat::zero(), Rat::zero());
            moves += 1;
        } else if moves == 0 {
            let (from, a0, a1, s) = after.located().unwrap().parts();
            assert_eq!((from, a0, a1, s), (6, &since.0, &Rat::zero(), &since.1));
        }
        assert_eq!(after.located(), Some(&expected));
        assert_eq!(after.located(), Some(&carried));
    }
    assert!(moves >= 1, "the run moves its prior");
    // Moves compose (Lean `rebaseAt_mul`).
    let pair = LocatedPrior::from_parts(0, rat(3, 7), rat(-2, 5), rat(9, 4));
    assert_eq!(
        pair.rebased(&rat(1, 2)).rebased(&integer(8)),
        pair.rebased(&integer(4))
    );
}

/// **A held prior is unchanged** (§6, test 4): its law carries no pair and its deposits read no
/// prior. While the located run has located nothing (its first window, on the zero map), the two
/// runs' laws and readings agree but for the pair and its read.
#[test]
fn a_held_prior_carries_no_pair_and_agrees_with_the_located_run_until_it_moves() {
    let run = |prior: ReceivingPrior| {
        let field = chain_at(prior);
        let theta = Constitution::initial(&field, 1 << 40).unwrap();
        let (next, reading) = theta.deposited(&receiving_deposit(&theta, 2, 0)).unwrap();
        (next.receiving_law(2).unwrap().clone(), reading)
    };
    let (held, held_reading) = run(ReceivingPrior::Held(1));
    let (located, mut located_reading) = run(ReceivingPrior::Located { from: 1 });
    assert!(held.located().is_none());
    assert!(held_reading.charts.iter().all(|(_, chart)| chart.prior.is_none()));
    assert_eq!(held, located.clone().with_located(None));
    for (_, chart) in &mut located_reading.charts {
        chart.prior = None;
    }
    assert_eq!(held_reading, located_reading);
}

/// A receiving law founded at `2^from I` on a 4 × 2 map, after one deposit (so its Gram has a
/// support), with the given pair, its chart rule and a budgeted carry for the move.
fn moving_law(from: u32, pair: (Rat, Rat, Rat)) -> (NormalLaw, ChartRule, BudgetedCarry) {
    let lattice = Lattice::new(12);
    let rule = ChartRule::new(lattice, 16);
    let map = ExactRatMatrix::shaped(
        4,
        2,
        vec![
            vec![rat(1, 2), rat(-1, 4)],
            vec![rat(1, 8), Rat::zero()],
            vec![rat(-3, 4), rat(1, 2)],
            vec![Rat::zero(), rat(1, 16)],
        ],
    )
    .unwrap();
    let law = NormalLaw::with_receiving_prior(map, ReceivingPrior::Located { from });
    let samples = window(1, 2, 2);
    let mut at = BudgetedCarry::new(lattice, 1);
    let (law, _) = law.deposited(&samples, &rat(1, 4), &rule, &mut at).unwrap();
    let (a0, a1, s) = pair;
    let law = law.with_located(Some(LocatedPrior::from_parts(from, a0, a1, s)));
    (law, rule, BudgetedCarry::new(lattice, 2))
}

/// The move's successor read against its law: the Gram's diagonal moved by exactly
/// `2^(k′) − 2^k` and nothing else, `W′ = x W` up to the map's carry (`W′ + r′ = x W + r`), the
/// chart at scale `k′` certified to its rule's target, and the pair rebased by `x`.
fn assert_moved(law: &NormalLaw, moved: &NormalLaw, to: u32, rule: &ChartRule) {
    let k = law.chart().scale();
    let x = power(i64::from(k) - i64::from(to));
    let shift = power(i64::from(to)) - power(i64::from(k));
    let (gram, moved_gram) = (law.gram(), moved.gram());
    for i in 0..gram.rows() {
        for j in 0..gram.columns() {
            let expected = if i == j {
                gram.get(i, j).unwrap() + &shift
            } else {
                gram.get(i, j).unwrap().clone()
            };
            assert_eq!(moved_gram.get(i, j).unwrap(), &expected);
        }
    }
    let (map, remainder) = (law.map(), law.map_remainder());
    let (moved_map, moved_remainder) = (moved.map(), moved.map_remainder());
    for i in 0..map.rows() {
        for j in 0..map.columns() {
            assert_eq!(
                moved_map.get(i, j).unwrap() + moved_remainder.get(i, j).unwrap(),
                &x * map.get(i, j).unwrap() + remainder.get(i, j).unwrap()
            );
        }
    }
    assert_eq!(moved.chart().scale(), to);
    assert!(moved.chart().certificate() <= &rule.target());
    assert_eq!(
        moved.located(),
        Some(&law.located().unwrap().rebased(&x))
    );
}

/// **The move** (§6, test 3): a pair whose Newton point `1 + a/V = 2` lies in the cell of
/// `x = 2` moves `k = 2` to `k′ = 1`, its Gram, map, chart and pair moved together, and the rebased
/// pair's Newton point lies in the unit's cell, so an immediate re-read holds (Lean
/// `HNN/PriorCarry.{newton_rebaseAt, rebase_into_cell}`). A pair whose code falls toward the zero
/// map (`V + a ≤ 0`) moves one member the other way, `k ↦ k + 1`, halving the map through its carry.
#[test]
fn the_prior_moves_to_the_newton_points_cell_with_its_gram_map_chart_and_pair() {
    let s = rat(5, 3);
    let (law, rule, mut at) = moving_law(2, (Rat::zero(), s.clone(), s));
    let (moved, read) = law.moved_prior(&rule, &mut at).unwrap().unwrap();
    assert_eq!((read.from, read.to, read.held), (2, 1, None));
    assert_eq!(read.certificate.as_ref(), Some(moved.chart().certificate()));
    assert_moved(&law, &moved, 1, &rule);
    assert_eq!(moved.located().unwrap().member(1).unwrap(), (0, None));
    let (law, rule, mut at) = moving_law(2, (integer(-10), Rat::zero(), Rat::one()));
    let (moved, read) = law.moved_prior(&rule, &mut at).unwrap().unwrap();
    assert_eq!((read.from, read.to, read.held), (2, 3, None));
    assert_moved(&law, &moved, 3, &rule);
}

/// **A sign inside the enclosure holds `k`; no curvature holds `k`** (§6, test 5): with
/// `V + a = A₀ + ln 2` and `A₀` minus the midpoint of `ln 2`'s enclosure, the sign of `V + a` lies
/// inside it, so the law stands unmoved and its read says so, never rounded.
#[test]
fn a_sign_inside_ln_twos_enclosure_holds_the_prior() {
    let ln2 = crate::hnn::executed::ln_two().unwrap();
    let middle = (&ln2.lower + &ln2.upper) / integer(2);
    let (law, rule, mut at) = moving_law(2, (-middle, Rat::zero(), Rat::one()));
    let (moved, read) = law.moved_prior(&rule, &mut at).unwrap().unwrap();
    assert_eq!((read.from, read.to, read.held), (2, 2, Some(PriorHeld::Undecided)));
    assert_eq!(moved, law);
    let (law, rule, mut at) = moving_law(2, (integer(3), integer(1), Rat::zero()));
    let (moved, read) = law.moved_prior(&rule, &mut at).unwrap().unwrap();
    assert_eq!(read.held, Some(PriorHeld::NoCurvature));
    assert_eq!(moved, law);
}

/// **The floor** (§6, test 6): a Newton point `1 + a/V = 100` locates the member `x = 2^6`,
/// below `2^0` from `k = 1`, so the prior moves to `k′ = 0` and the read says it was floored; at
/// `k = 0` it holds there.
#[test]
fn a_cell_below_the_unit_prior_moves_to_it() {
    let s = rat(7, 2);
    let (law, rule, mut at) = moving_law(1, (Rat::zero(), integer(99) * &s, s.clone()));
    let (moved, read) = law.moved_prior(&rule, &mut at).unwrap().unwrap();
    assert_eq!((read.from, read.to, read.held), (1, 0, Some(PriorHeld::Floor)));
    assert_moved(&law, &moved, 0, &rule);
    let (law, rule, mut at) = moving_law(0, (Rat::zero(), integer(99) * &s, s));
    let (moved, read) = law.moved_prior(&rule, &mut at).unwrap().unwrap();
    assert_eq!((read.from, read.to, read.held), (0, 0, Some(PriorHeld::Floor)));
    assert_eq!(moved, law);
}

/// **A saved state restores across a move** (§6, test 7; §4): the continuing state carries the
/// receiving law whole (its moved Gram, its chart at its scale, its remainders and its pair) and its
/// clock inside the check, its text reads back equal, the declared opening continued from it is the
/// moved constitution, and the next deposit from either is the same. A state of the located field
/// is refused on the held field's opening, whose material differs only in the declared prior.
#[test]
fn a_saved_state_restores_across_a_move() {
    let field = chain_at(ReceivingPrior::Located { from: 6 });
    let opening = Constitution::initial(&field, 1 << 40).unwrap();
    let mut theta = opening.clone();
    let mut moved = false;
    for t in 0..2 {
        let (next, reading) = theta.deposited(&receiving_deposit(&theta, 2, t)).unwrap();
        moved |= reading
            .charts
            .iter()
            .any(|(_, chart)| chart.prior.as_ref().is_some_and(|read| read.to != read.from));
        theta = next;
    }
    assert!(moved, "the second window moves the prior");
    assert_ne!(theta.receiving_law(2).unwrap().chart().scale(), 6);
    let state = theta.continuing_state(0).unwrap();
    let text = state.to_text();
    assert!(text.contains("\nlocated 6 "));
    let read = ContinuingState::from_text(&text).unwrap();
    assert_eq!(read, state);
    let restored = opening.clone().continued(&read).unwrap();
    assert_eq!(restored, theta);
    let (a, ra) = theta.deposited(&receiving_deposit(&theta, 2, 2)).unwrap();
    let (b, rb) = restored.deposited(&receiving_deposit(&restored, 2, 2)).unwrap();
    assert_eq!((a, ra), (b, rb));
    let held = Constitution::initial(&chain_at(ReceivingPrior::Held(6)), 1 << 40).unwrap();
    assert!(matches!(
        held.continued(&read),
        Err(HnnError::ContinuingState { what }) if what.contains("another opening")
    ));
    // A chart's scale whose prior is not the Gram off its support is refused, even with its check
    // re-stamped over the changed bytes: the unmoved source law's Gram is `I`, so its scale is `0`.
    let line = text.find("\nchart ").unwrap() + 1;
    let end = line + text[line..].find('\n').unwrap();
    let mut words: Vec<&str> = text[line..end].split(' ').collect();
    let scale = format!("{}", words[3].parse::<u32>().unwrap() + 1);
    words[3] = &scale;
    let changed = format!("{}{}{}", &text[..line], words.join(" "), &text[end..]);
    let stamped = ContinuingState::stamped(&changed, &opening).unwrap();
    assert!(matches!(
        ContinuingState::from_text(&stamped),
        Err(HnnError::ContinuingState { what }) if what.contains("scale")
    ));
}

/// **The located prior on the port** (§6, the exposure): the chain at its capacity with its
/// receiver's prior located from `2^6`, exposed window by window through the reference port. Every
/// deposit whose covector reached the receiving map reads the pair once there (a deposit that
/// stepped only the source port, or nothing, reads none: its terms never reached the map), and the
/// exposure moves `k` off its founding; the last receiving law still says where its prior was
/// founded. The card's lockstep (`holonics_cuda::hnn::port_tests`) runs the same chain against this
/// reference.
#[test]
fn an_exposed_located_chain_reads_its_pair_where_the_map_is_stepped_and_moves_its_prior() {
    use super::support::Draw;
    use crate::hnn::field::Current;
    use crate::hnn::port::{ExecutionPort, Handle};
    use crate::hnn::reference::{Reference, one_hot};

    let located = ReceivingPrior::Located { from: 6 };
    let declared = |population: u64| {
        let mut declaration = chain_declaration(population);
        declaration.receivers[0].receiving_prior = located;
        Field::declare(declaration.by_lattice_rule()).unwrap()
    };
    let field = declared(declared(1 << 20).capacity().n_star() as u64);
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let mut draw = Draw::new(7);
    let cells: Vec<usize> = (0..field.population()).map(|_| draw.below(4)).collect();
    let phases = resident.admitted()[0].clone();
    let family = resident.admitted().to_vec();
    let (moment, _) = reference.ingest(&mut resident, None, &[]).unwrap();
    let (mut deposits, mut reads, mut moves) = (0u64, 0u64, Vec::new());
    for span in cells.chunks(phases.aperture()) {
        if span.len() == phases.aperture() {
            let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
            let (staged, _) = reference
                .compare(&mut resident, pending, &one_hot(span))
                .unwrap();
            if resident.stopped().is_some() {
                reference
                    .discard(&mut resident, Handle::Staged(staged))
                    .unwrap();
            } else {
                let returned = reference.deposit(&mut resident, staged).unwrap();
                let reading = returned.deposit.into_present().expect("a published deposit");
                deposits += 1;
                for (locus, chart) in &reading.charts {
                    let Some(prior) = &chart.prior else {
                        assert_ne!(*locus, Locus::ReceivingMap(2), "a stepped map reads its pair");
                        continue;
                    };
                    assert_eq!(*locus, Locus::ReceivingMap(2));
                    reads += 1;
                    if prior.to != prior.from {
                        moves.push(prior.clone());
                    }
                }
            }
        }
        let mut fed = 0;
        while fed < span.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &one_hot(&span[fed..]))
                .unwrap();
            let ingested = ingested.forward.into_present().expect("the ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                reference.close_aeon(&mut resident, &family).unwrap();
            }
        }
    }
    println!("{deposits} deposits, {reads} pair reads, moves {moves:?}");
    assert!(reads > 0 && reads <= deposits);
    assert!(!moves.is_empty(), "the exposure moves the located prior");
    let last = resident.constitution().receiving_law(2).unwrap();
    assert_eq!(last.receiving_prior(), located);
    assert_eq!(last.chart().scale(), moves.last().unwrap().to);
}
