//! Current-window receiving proposals retain their immutable founding declaration, select at
//! their predeposit map, conserve carried map/Gram values under a rebase, and restore exactly.
//! The [prior-carry record](../../../../../research/records/2026-10-04_THE_RECEIVING_PRIOR_IS_CARRIED_BESIDE_ITS_GRAM_AND_MOVES_TO_THE_CODES_CELL.md)
//! is superseded in part by D2: fixed-ray scalar evidence is retired; these current-window,
//! phase-statistics, immutable-founding and cold-continuation controls remain.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{chain_declaration, chain_reach};
use crate::hnn::HnnError;
use crate::hnn::constitution::{
    Constitution, ContinuingState, Lattice, LinearLocus, LinearStep, Locus, NormalLaw, PriorHeld,
    Sample, prequential_terms,
};
use crate::hnn::field::Field;
use crate::hnn::port::Deposit;
use crate::hnn::tests::support::encoded;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

/// The chain control with its receiver's prior declared `prior`.
fn chain_at(from: u32) -> Field {
    let mut declared = chain_declaration(1 << 16);
    declared.receivers[0].receiving_prior = from;
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
        masses: None,
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
                .map(|c| {
                    if c == lead {
                        rat(5, 8)
                    } else {
                        rat(3, 8 * (a as i64 - 1))
                    }
                })
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

fn located_run(
    from: u32,
    windows: usize,
) -> Vec<(
    NormalLaw,
    (Rat, Rat),
    NormalLaw,
    crate::hnn::constitution::PriorMove,
)> {
    let field = chain_at(from);
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
            let read = chart
                .prior
                .clone()
                .expect("a located prior is read at every deposit");
            theta = next;
            (before, terms, theta.receiving_law(2).unwrap().clone(), read)
        })
        .collect()
}

/// Each receiving proposal belongs to its predeposit map; the current window alone selects
/// the metric, while its founding declaration remains unchanged.
#[test]
fn each_receiving_window_selects_at_its_old_map_without_transporting_scalar_history() {
    use crate::hnn::constitution::receiving_window::ReceivingWindowRay;
    let run = located_run(6, 8);
    assert_eq!(run[0].1, (Rat::zero(), Rat::zero()));
    assert_eq!(run[0].3.held, Some(PriorHeld::NoCurvature));
    let mut moves = 0;
    for (t, (before, _terms, after, read)) in run.iter().enumerate() {
        assert_eq!(read.from, before.chart().scale());
        assert_eq!(read.to, after.chart().scale());
        let samples = window(t, before.map().columns(), before.map().rows() / 2);
        let ray = ReceivingWindowRay::read(&samples, before.map()).unwrap();
        let (j, _) = ray.member().unwrap();
        let j = j.min(i64::from(read.from));
        assert_eq!(i64::from(read.to), i64::from(read.from) - j);
        assert_eq!(after.receiving_prior(), Some(6));
        moves += usize::from(read.to != read.from);
    }
    assert!(moves >= 1, "current evidence still permits a prior move");
}

#[test]
fn the_founding_declaration_and_mount_move_nothing() {
    for from in [0, 1, 6] {
        let theta = Constitution::initial(&chain_at(from), 1 << 40).unwrap();
        let law = theta.receiving_law(2).unwrap();
        assert_eq!(law.receiving_prior(), Some(from));
        assert_eq!(law.chart().scale(), from);
        assert_eq!(law.chart().certificate(), &Rat::zero());
        let unit = Rat::from_integer(BigInt::one() << from as usize);
        let gram = law.gram();
        let n = gram.rows();
        assert_eq!(gram, ExactRatMatrix::identity(n).unwrap().scaled(&unit));
        let (_, reading) = theta.deposited(&receiving_deposit(&theta, 2, 0)).unwrap();
        let [(_, chart)] = reading.charts.as_slice() else {
            panic!("one chart reading, at the receiving map");
        };
        let read = chart.prior.clone().unwrap();
        assert_eq!(
            (read.from, read.to, read.held),
            (from, from, Some(PriorHeld::NoCurvature))
        );
    }
}

#[test]
fn a_saved_state_restores_across_a_move() {
    let field = chain_at(6);
    let opening = Constitution::initial(&field, 1 << 40).unwrap();
    let mut theta = opening.clone();
    let mut moved = false;
    for t in 0..2 {
        let (next, reading) = theta.deposited(&receiving_deposit(&theta, 2, t)).unwrap();
        moved |= reading.charts.iter().any(|(_, chart)| {
            chart
                .prior
                .as_ref()
                .is_some_and(|read| read.to != read.from)
        });
        theta = next;
    }
    assert!(moved, "the second window moves the prior");
    assert_ne!(theta.receiving_law(2).unwrap().chart().scale(), 6);
    let state = theta.continuing_state(0).unwrap();
    let text = state.to_text();
    assert!(text.contains("\nreceiving_prior 6\n"));
    assert!(!text.lines().any(|line| line.starts_with("located ")));
    let read = ContinuingState::from_text(&text, opening.budget()).unwrap();
    assert_eq!(read, state);
    let restored = opening.clone().continued(&read).unwrap();
    assert_eq!(restored, theta);
    let (a, ra) = theta.deposited(&receiving_deposit(&theta, 2, 2)).unwrap();
    let (b, rb) = restored
        .deposited(&receiving_deposit(&restored, 2, 2))
        .unwrap();
    assert_eq!((a, ra), (b, rb));
    let other = Constitution::initial(&chain_at(5), 1 << 40).unwrap();
    assert!(matches!(
        other.continued(&read),
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
        ContinuingState::from_text(&stamped, opening.budget()),
        Err(HnnError::ContinuingState { what }) if what.contains("scale")
    ));
}

fn exposed(
    field: &Field,
    cells: &[usize],
    reception: crate::hnn::reference::Reception,
) -> (u64, Vec<crate::hnn::constitution::PriorMove>, NormalLaw) {
    use crate::hnn::field::Current;
    use crate::hnn::port::{ExecutionPort, Handle};
    use crate::hnn::reference::Reference;

    let reference = Reference::campaign_one().with_reception(reception);
    let mut resident = reference.mount(field, &Current::at_rest(field)).unwrap();
    let phases = resident.admitted()[0].clone();
    let family = resident.admitted().to_vec();
    let (moment, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &[]))
        .unwrap();
    let (mut deposits, mut reads) = (0u64, Vec::new());
    for span in cells.chunks(phases.aperture()) {
        if span.len() == phases.aperture() {
            let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
            let (staged, _) = reference
                .compare(&mut resident, pending, &encoded(&field, span))
                .unwrap();
            if resident.stopped().is_some() {
                reference
                    .discard(&mut resident, Handle::Staged(staged))
                    .unwrap();
            } else {
                let returned = reference.deposit(&mut resident, staged).unwrap();
                let reading = returned
                    .deposit
                    .into_present()
                    .expect("a published deposit");
                deposits += 1;
                for (locus, chart) in &reading.charts {
                    let Some(prior) = &chart.prior else {
                        assert_ne!(
                            *locus,
                            Locus::ReceivingMap(2),
                            "a stepped map reads its pair"
                        );
                        continue;
                    };
                    assert_eq!(*locus, Locus::ReceivingMap(2));
                    reads.push(prior.clone());
                }
            }
        }
        let mut fed = 0;
        while fed < span.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &encoded(&field, &span[fed..]))
                .unwrap();
            let ingested = ingested.forward.into_present().expect("the ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                reference.close_aeon(&mut resident, &family).unwrap();
            }
        }
    }
    let law = resident.constitution().receiving_law(2).unwrap().clone();
    (deposits, reads, law)
}

fn located_chain(place: impl Fn(&mut crate::hnn::field::RingDeclaration)) -> Field {
    let declared = |population: u64| {
        let mut declaration = super::learning::chain_two_declaration(population);
        declaration.receivers[0].receiving_prior = 6;
        declaration.rings.iter_mut().for_each(&place);
        Field::declare(declaration.by_lattice_rule()).unwrap()
    };
    declared(declared(1 << 20).capacity().n_star() as u64)
}

#[test]
fn an_exposed_located_chain_reads_its_pair_where_the_map_is_stepped_and_moves_its_prior() {
    use super::support::Draw;

    let field = located_chain(|_| {});
    let mut draw = Draw::new(7);
    let cells: Vec<usize> = (0..field.population()).map(|_| draw.below(2)).collect();
    let reception = crate::hnn::reference::Reference::campaign_one().reception();
    let (deposits, reads, last) = exposed(&field, &cells, reception);
    let moves: Vec<_> = reads.iter().filter(|read| read.to != read.from).collect();
    println!(
        "{deposits} deposits, {} pair reads, moves {moves:?}",
        reads.len()
    );
    assert!(!reads.is_empty() && reads.len() as u64 <= deposits);
    assert!(!moves.is_empty(), "the exposure moves the located prior");
    assert_eq!(last.receiving_prior(), Some(6));
    assert_eq!(last.chart().scale(), moves.last().unwrap().to);
}

#[test]
fn at_rest_a_map_that_never_leaves_zero_holds_its_prior() {
    use super::support::Draw;
    use crate::hnn::field::FieldDeclaration;
    use crate::hnn::reference::Reception;

    let field = located_chain(|ring| {
        let period = ring.period;
        ring.placements = (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect();
    });
    let mut draw = Draw::new(3);
    let cells: Vec<usize> = (0..field.population() as usize)
        .map(|k| {
            if draw.below(8) == 0 {
                draw.below(2)
            } else {
                [0, 1, 2, 1][k % 4] % 2
            }
        })
        .collect();
    let (_, at_rest, rest_law) = exposed(&field, &cells, Reception::Rest);
    assert!(!at_rest.is_empty());
    assert!(
        at_rest
            .iter()
            .all(|read| (read.from, read.to, read.held) == (6, 6, Some(PriorHeld::NoCurvature)))
    );
    assert!(rest_law.map().entries().iter().all(Zero::is_zero));
}

#[test]
fn zero_prequential_window_does_not_suppress_ordinary_receiving_learning() {
    let run = located_run(1, 1);
    let (before, terms, after, prior) = &run[0];
    assert_eq!(terms, &(Rat::zero(), Rat::zero()));
    assert_eq!(prior.held, Some(PriorHeld::NoCurvature));
    assert_ne!(before.gram(), after.gram());
    assert_ne!(before.map(), after.map());
    assert_ne!(before.phase_statistics(), after.phase_statistics());
}

#[test]
fn receiving_rebase_conserves_map_gram_carries_and_recertifies_without_an_observation() {
    use std::collections::BTreeSet;
    let field = chain_at(1);
    let initial = Constitution::initial(&field, 1 << 40).unwrap();
    let (theta, _) = initial
        .deposited(&receiving_deposit(&initial, 2, 0))
        .unwrap();
    let locus = Locus::ReceivingMap(2);
    let retained = BTreeSet::from([locus]);
    assert_eq!(theta.rebased(locus, 0, &retained).unwrap(), theta);
    let old = theta.receiving_law(2).unwrap();
    let exponent = theta.lattice(locus).unwrap().exponent();
    let remainder = old.map_remainder();
    assert!(remainder.entries().iter().any(|x| !x.is_zero()));
    let mut levels = 1;
    while remainder
        .entries()
        .iter()
        .all(|x| Lattice::new(exponent + levels).div_rem(x).0.is_zero())
    {
        levels += 1;
    }
    let stale = receiving_deposit(&theta, 2, 1);
    let next = theta.rebased(locus, levels, &retained).unwrap();
    let new = next.receiving_law(2).unwrap();
    assert_eq!(next.clock(locus), theta.clock(locus));
    assert_eq!(next.commit(), theta.commit() + 1);
    assert_eq!(
        next.lattice(locus).unwrap().exponent(),
        theta.lattice(locus).unwrap().exponent() + levels
    );
    assert_eq!(old.prior_scale(), new.prior_scale());
    assert_eq!(old.receiving_prior(), new.receiving_prior());
    assert_eq!(old.phase_statistics(), new.phase_statistics());
    for ((a, b), (ar, br)) in old.map().entries().iter().zip(new.map().entries()).zip(
        old.map_remainder()
            .entries()
            .iter()
            .zip(new.map_remainder().entries()),
    ) {
        assert_eq!(a + ar, b + br);
    }
    for ((a, b), (ar, br)) in old.gram().entries().iter().zip(new.gram().entries()).zip(
        old.gram_remainder()
            .entries()
            .iter()
            .zip(new.gram_remainder().entries()),
    ) {
        assert_eq!(a + ar, b + br);
    }
    assert!(new.chart().certificate() <= &next.chart_rule(locus).unwrap().target());
    assert!(next.on_lattice());
    assert_ne!(
        old.map(),
        new.map(),
        "the retained remainder actually becomes executed material"
    );
    assert!(matches!(
        next.deposited(&stale),
        Err(HnnError::StaleDeposit { .. })
    ));
    let (continued, _) = next.deposited(&receiving_deposit(&next, 2, 1)).unwrap();
    assert_eq!(continued.clock(locus), next.clock(locus) + 1);
    assert_eq!(
        continued.lattice(locus).unwrap(),
        next.lattice(locus).unwrap()
    );
    let changed = old
        .map()
        .entries()
        .iter()
        .zip(new.map().entries())
        .position(|(a, b)| a != b)
        .unwrap();
    let column = changed % old.map().columns();
    let mut basis = vec![Rat::zero(); old.map().columns()];
    basis[column] = Rat::one();
    let feature = field.ring(2).rotate(&basis, &BigInt::from(-3));
    let rotated = field.ring(2).rotate(&feature, &BigInt::from(3));
    assert_eq!(rotated, basis);
    assert_ne!(
        old.map().apply(&rotated).unwrap(),
        new.map().apply(&rotated).unwrap()
    );
    // Exact output change and its row-sum bound on an actual test feature; not a claim that
    // publishing the carry leaves the formerly quantized receiver output unchanged.
    let feature = vec![rat(3, 7); old.map().columns()];
    for row in 0..old.map().rows() {
        let delta: Vec<Rat> = old
            .map()
            .row(row)
            .unwrap()
            .iter()
            .zip(new.map().row(row).unwrap())
            .map(|(a, b)| b - a)
            .collect();
        let effect: Rat = delta.iter().zip(&feature).map(|(d, z)| d * z).sum();
        let bound: Rat = delta
            .iter()
            .map(|d| if d < &Rat::zero() { -d } else { d.clone() })
            .sum::<Rat>()
            * rat(3, 7);
        assert!(effect >= -&bound && effect <= bound);
    }
}

#[test]
fn arrival_context_receiving_deposit_is_dyadically_covariant_and_restores() {
    use crate::hnn::constitution::ReceivingLayout;
    use crate::hnn::field::ConstitutionRead;
    let field = chain_at(1);
    let mut opening = Constitution::initial(&field, 1 << 40).unwrap();
    let width = opening.receiving_map(2).unwrap().columns();
    opening.bind_arrival_context_receiving(2).unwrap();
    assert_eq!(
        opening.receiving_layout(2),
        Some(ReceivingLayout::ArrivalContext {
            source_width: width
        })
    );
    assert!(opening.receiving_law(2).is_none());
    let classes = opening.receiving_map(2).unwrap().rows() / 2;
    let masses = vec![rat(1, classes as i64); classes];
    let sample = |source_scale: Rat, context_scale: Rat| {
        let feature = (0..2 * width)
            .map(|j| {
                if j < width {
                    &source_scale * rat((j % 3 + 1) as i64, 16)
                } else {
                    &context_scale * rat((j % 2 + 1) as i64, 64)
                }
            })
            .collect::<Vec<_>>();
        let mut sample = reading(&feature, &masses, 0, &rat(1, 16));
        // A categorical target has a phase covector only on its observed class.
        for class in 1..classes {
            sample.covector[2 * class + 1] = Rat::zero();
        }
        sample.masses = Some(masses.clone());
        sample
    };
    let update = |theta: &Constitution, sample: Sample| {
        let deposit = Deposit::new(
            theta.commit(),
            vec![LinearStep {
                locus: LinearLocus::Receiving(2),
                samples: vec![sample],
            }],
            Vec::new(),
            vec![Locus::ReceivingMap(2)],
        )
        .with_reach(chain_reach());
        theta.deposited(&deposit).unwrap()
    };
    let a = sample(integer(1), integer(1));
    let b = sample(integer(8), rat(1, 4));
    let (next, reading_a) = update(&opening, a.clone());
    let (scaled, reading_b) = update(&opening, b.clone());
    assert_eq!(reading_a.charts.len(), 2);
    assert_eq!(reading_b.charts.len(), 2);
    assert_eq!(
        next.receiving_map(2).unwrap().apply(&a.feature).unwrap(),
        scaled.receiving_map(2).unwrap().apply(&b.feature).unwrap()
    );
    for (left, right) in next
        .receiving_blocks(2)
        .unwrap()
        .iter()
        .zip(scaled.receiving_blocks(2).unwrap())
    {
        assert_eq!(left.law(), right.law());
        assert!(left.law().map().entries().iter().any(|x| !x.is_zero()));
    }
    let state = next.continuing_state(0).unwrap();
    let text = state.to_text();
    assert!(
        next.receiving_phase_statistics(2)
            .unwrap()
            .cells()
            .is_positive()
    );
    // A known synthetic old-chart fixture has a valid checksum; the semantic
    // version check must still refuse it. This is not migration of user history.
    let untagged = text.replace("receiving-chart passage-relative-read-and-target-v1\n", "");
    let old_chart = ContinuingState::stamped(&untagged, &opening).unwrap();
    assert!(matches!(
        ContinuingState::from_text(&old_chart, opening.budget()),
        Err(HnnError::ContinuingState {
            what: "the receiving read and target phase chart (requires passage-relative-read-and-target-v1)"
        })
    ));
    let saved = ContinuingState::from_text(&text, opening.budget()).unwrap();
    let restored = opening.clone().continued(&saved).unwrap();
    assert_eq!(restored, next);
    assert!(
        Constitution::initial(&field, 1 << 40)
            .unwrap()
            .continued(&saved)
            .is_err()
    );
    let (continued, read_a) = update(&next, a.clone());
    let (cold, read_b) = update(&restored, a);
    assert_eq!(continued, cold);
    assert_eq!(read_a, read_b);
    // The single-anchor medium certificate cannot certify a second response path.
    // Until the paired gain owner is integrated, refuse shared-material learning explicitly.
    let source = next.source_law(0).unwrap().map();
    let mixed = Deposit::new(
        next.commit(),
        vec![
            LinearStep {
                locus: LinearLocus::Receiving(2),
                samples: vec![b],
            },
            LinearStep {
                locus: LinearLocus::SourcePort(0),
                samples: vec![Sample {
                    weight: integer(1),
                    feature: vec![integer(1); source.columns()],
                    covector: vec![integer(1); source.rows()],
                    masses: None,
                }],
            },
        ],
        Vec::new(),
        vec![Locus::ReceivingMap(2), Locus::SourcePort(0)],
    )
    .with_reach(chain_reach());
    let staged = next
        .staged_comparison_candidate(&mixed, &next.held(), 0)
        .unwrap();
    assert_eq!(staged.producing(), &next);
    assert!(
        staged
            .reading()
            .steps
            .iter()
            .any(|(locus, _)| *locus == Locus::SourcePort(0))
    );
    assert!(
        staged
            .admit(
                &crate::ratio::algebraic::ExactInterval::point(integer(1)),
                &crate::ratio::algebraic::ExactInterval::point(integer(1)),
            )
            .is_none()
    );
    assert!(matches!(
        next.deposited(&mixed),
        Err(HnnError::Unadmitted {
            reason: "paired receiving shared-material steps require the joined source/context propagation gain certificate"
        })
    ));
}

#[test]
fn staged_comparison_candidate_requires_strict_finite_admission() {
    use crate::ratio::algebraic::ExactInterval;
    let field = chain_at(1);
    let opening = Constitution::initial(&field, 1 << 40).unwrap();
    let original = opening.clone();
    let deposit = receiving_deposit(&opening, 2, 0);
    let held = opening.held();
    let candidate = opening
        .staged_comparison_candidate(&deposit, &held, 0)
        .unwrap();
    assert_eq!(candidate.producing(), &opening);
    let changes = candidate.changes();
    assert!(!changes.full_material_unchanged);
    assert_eq!(changes.published_operand_loci, vec![Locus::ReceivingMap(2)]);
    assert!(changes.tree_rings.is_empty());
    assert!(changes.population_rings.is_empty());
    assert_eq!(
        changes.carry_entries_before,
        opening.carried_remainders().len()
    );
    assert_eq!(
        changes.carry_entries_after,
        candidate.material().carried_remainders().len()
    );
    assert_eq!(opening, original);
    assert_ne!(candidate.material(), &opening);
    let identical = ExactInterval::point(integer(2));
    assert!(candidate.admit(&identical, &identical).is_none());
    let candidate = opening
        .staged_comparison_candidate(&deposit, &held, 0)
        .unwrap();
    let expected = candidate.material().clone();
    let reading = candidate.reading().clone();
    // This unit test checks only the private numerical admission boundary.
    // The frozen comparison owner must supply the actual producing scores.
    let accepted = candidate
        .admit(&identical, &ExactInterval::point(integer(1)))
        .unwrap();
    assert_eq!(accepted, (expected, reading));
    let coarse = opening
        .staged_comparison_candidate(&deposit, &held, 0)
        .unwrap();
    let finer = opening
        .staged_comparison_candidate(&deposit, &held, 1)
        .unwrap();
    for ((_, a), (_, b)) in coarse.reading().steps.iter().zip(&finer.reading().steps) {
        assert_eq!(a.step.exponent - 1, b.step.exponent);
    }
    assert_eq!(opening, original);
}
