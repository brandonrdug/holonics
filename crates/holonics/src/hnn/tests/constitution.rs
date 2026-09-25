//! Deposition, per locus: the prox step, the statistic's standing, the budgeted carry (its
//! accounting, its bound since the founding, remainder bits, the carried Gram's positivity and the
//! zero update), the squares' positivity with no clamp, the energy growth of reaction deposits,
//! the budget's refusal, the standing's lock chart, the causal diamond's window, the declared
//! initial constitution, and the refusal of a complex-bilinear block at declaration.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{OPEN_BUDGET, chain, generic, moment, phases, six_path};
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::{
    BudgetedCarry, Carrier, Constitution, DepositReading, FactorGradient, FactorStep, Lattice,
    LinearLocus, LinearStep, Locus, NormalLaw, Sample, Steps, declared_sign, gamma_length,
};
use crate::hnn::field::{ConstitutionRead, Current};
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{Deposit, ExecutionPort};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::reference::{Reference, compose, one_hot};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::inertia;
use crate::ratio::linear::vector::matrix_form;
use crate::ratio::{Rat, integer, rat};

fn sample(weight: Rat, feature: Vec<Rat>, covector: Vec<Rat>) -> Sample {
    Sample {
        weight,
        feature,
        covector,
    }
}

/// Lean `HNN/Normal.normal_prox_step` at the carried operands, `HNN/LatticeDeposit.carry`,
/// `carry_accounting`: over three deposits (clocks 1, 2, 3), the carried Gram moves by exactly
/// `Σ w f fᵀ` less its released residuals (value plus remainder), the map by exactly
/// `γ Σ w g fᵀ H'⁻¹` less its released residuals at the carried successor Gram `H'`, so
/// `(W + ΔW) H' = W H' + γ G`; `H'⁻¹` is the carried Gram's exact inverse; every entry stays on the
/// lattice, every remainder in its half-open cell on the fine lattice of its clock, and every
/// residual within half a fine unit.
#[test]
fn the_prox_step_is_exact_at_the_carried_operands() {
    let mut draw = Draw::new(3);
    let lattice = Lattice::new(4);
    let mut law = NormalLaw::with_prior(draw.dyadic_matrix(3, 4));
    let proxy = rat(1, 2);
    let carried = |law: &NormalLaw| -> (ExactRatMatrix, ExactRatMatrix) {
        (
            law.map().add(&law.map_remainder()).unwrap(),
            law.gram().add(&law.gram_remainder()).unwrap(),
        )
    };
    for clock in 1..=3 {
        let samples: Vec<Sample> = (0..2)
            .map(|_| {
                sample(
                    draw.rational().abs() + Rat::one(),
                    draw.vector(4),
                    draw.vector(3),
                )
            })
            .collect();
        let mut at = BudgetedCarry::new(lattice, clock);
        let next = law.deposited(&samples, &proxy, &mut at).unwrap();
        assert!(at.moved());
        let released = |carrier: Carrier, rows: usize, columns: usize| {
            let mut dense = vec![vec![Rat::zero(); columns]; rows];
            for (c, entry, e) in at.released() {
                if c == carrier {
                    dense[entry / columns][entry % columns] = e;
                }
            }
            ExactRatMatrix::shaped(rows, columns, dense).unwrap()
        };
        let (map, gram) = carried(&law);
        let (next_map, next_gram) = carried(&next);
        let mut gram_update = ExactRatMatrix::zero(4, 4).unwrap();
        let mut gradient = ExactRatMatrix::zero(3, 4).unwrap();
        for s in &samples {
            let outer = |left: &[Rat], right: &[Rat]| {
                ExactRatMatrix::shaped(
                    left.len(),
                    right.len(),
                    left.iter()
                        .map(|l| right.iter().map(|r| &s.weight * l * r).collect())
                        .collect(),
                )
                .unwrap()
            };
            gram_update = gram_update.add(&outer(&s.feature, &s.feature)).unwrap();
            gradient = gradient.add(&outer(&s.covector, &s.feature)).unwrap();
        }
        assert_eq!(
            next_gram
                .subtract(&gram)
                .unwrap()
                .add(&released(Carrier::Gram, 4, 4))
                .unwrap(),
            gram_update
        );
        let solved = next.gram().inverse().unwrap();
        assert_eq!(next.solved(), solved);
        let step = gradient.multiply(&solved).unwrap().scaled(&proxy);
        assert_eq!(
            next_map
                .subtract(&map)
                .unwrap()
                .add(&released(Carrier::Map, 3, 4))
                .unwrap(),
            step
        );
        assert_eq!(
            law.map()
                .add(&step)
                .unwrap()
                .multiply(&next.gram())
                .unwrap(),
            law.map()
                .multiply(&next.gram())
                .unwrap()
                .add(&gradient.scaled(&proxy))
                .unwrap()
        );
        let half = lattice.unit() / integer(2);
        let fine = Lattice::new(lattice.exponent() + gamma_length(clock));
        for value in next.map().entries().iter().chain(next.gram().entries()) {
            assert!(lattice.contains(value));
        }
        for r in next
            .map_remainder()
            .entries()
            .iter()
            .chain(next.gram_remainder().entries())
        {
            assert!(-&half <= *r && *r < half && fine.contains(r));
        }
        let fine_half = fine.unit() / integer(2);
        for (.., e) in at.released() {
            assert!(-&fine_half <= e && e < fine_half);
        }
        law = next;
    }
    assert!(law.map_remainder().entries().iter().any(|r| !r.is_zero()));
}

/// Lean `HNN/Normal.normalStatistic_standing`, `statistic_forgets_the_samples`: the law keeps the
/// statistic, never the sample list; two lists with one statistic give one law.
#[test]
fn the_normal_law_keeps_the_statistic_not_the_samples() {
    let law = NormalLaw::with_prior(ExactRatMatrix::zero(1, 1).unwrap());
    let lattice = Lattice::new(4);
    let one = || vec![Rat::one()];
    let minus = || vec![-Rat::one()];
    let mut at = BudgetedCarry::new(lattice, 1);
    let twice = law
        .deposited(
            &[
                sample(Rat::one(), one(), one()),
                sample(Rat::one(), one(), one()),
            ],
            &Rat::one(),
            &mut at,
        )
        .unwrap();
    let mut again = BudgetedCarry::new(lattice, 1);
    let signed = law
        .deposited(
            &[
                sample(Rat::one(), one(), one()),
                sample(Rat::one(), minus(), minus()),
            ],
            &Rat::one(),
            &mut again,
        )
        .unwrap();
    assert_eq!(twice, signed);
    assert_eq!(at, again);
}

/// Lean `HNN/LatticeDeposit.{div_rem_spec, rem_bounds, quot_eq_zero_of_bounds}`: the nearest
/// lattice point with ties upward, `x = q·2^(−L) + r`, `−2^(−L−1) ≤ r < 2^(−L−1)`; a remainder alone
/// divides to zero, the lower tie included.
#[test]
fn division_with_remainder_is_the_nearest_lattice_point_ties_upward() {
    let lattice = Lattice::new(3);
    for (value, quotient, remainder) in [
        (rat(1, 3), 3, rat(-1, 24)),
        (rat(-1, 3), -3, rat(1, 24)),
        (rat(1, 16), 1, rat(-1, 16)),
        (rat(-1, 16), 0, rat(-1, 16)),
        (rat(5, 8), 5, rat(0, 1)),
        (rat(-7, 5), -11, rat(-1, 40)),
    ] {
        let (q, r) = lattice.div_rem(&value);
        assert_eq!((q, r.clone()), (BigInt::from(quotient), remainder));
        assert_eq!(
            value,
            Rat::from_integer(BigInt::from(quotient)) * lattice.unit() + &r
        );
        assert!(rat(-1, 16) <= r && r < rat(1, 16));
        assert_eq!(lattice.div_rem(&r).0, BigInt::zero());
    }
    assert!(lattice.contains(&rat(3, 8)) && !lattice.contains(&rat(1, 16)));
}

/// Lean `HNN/LatticeDeposit.{carry, release, carry_accounting}` at the ties, through the carry's two
/// splits ([`Lattice::div_rem`] fine, [`Lattice::div_rem_coordinate`] coarse), with `u = 2^(−L)` and
/// the fine unit `f = 2^(−L−k_m)`: at clock 1 (`k = 1`) a fine tie `Δ = f/2` rounds up to the fine
/// point `1`, itself a coarse tie, so `q = 1`, `r = −f`, `e = −f/2`; `Δ = −f/2` rounds up to `0`
/// (`q = 0`, `r = 0`, `e = −f/2`); the coarse ties `Δ = ±f` (odd fine points) give `q = 1, r = −f`
/// and `q = 0, r = −f` (the half-open cell `[−u/2, u/2)`), releasing nothing. At clock 2 (`k = 3`)
/// the fine point `4 ≡ 2^(k−1) (mod 2^k)` is a coarse tie (`q = 1`, `r = −4f`) and `Δ = f/2` a fine
/// tie (`q = 0`, `r = f`, `e = −f/2`).
#[test]
fn the_carry_splits_its_ties_upward_at_both_lattices() {
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let lattice = theta.lattice(Locus::Standing(1)).unwrap();
    let (u, n) = (lattice.unit(), field.ring(1).width());
    // η_x / h_x = ½ with no feature energy, so a gradient `2Δ` applies the update `Δ`.
    let standing = |commit: u64, updates: Vec<Rat>| {
        Deposit::new(
            commit,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing {
                    ring: 1,
                    gradient: updates.iter().map(|x| x * integer(2)).collect(),
                },
                energy: Rat::zero(),
            }],
            Vec::new(),
        )
    };
    let check = |theta: &Constitution,
                 before: &Constitution,
                 reading: &DepositReading,
                 entry: usize,
                 (q, r, e): (i64, Rat, Rat)| {
        let moved = &theta.standing(1)[entry] - &before.standing(1)[entry];
        assert_eq!(moved, integer(q) * &u, "entry {entry}");
        let key = (Locus::Standing(1), Carrier::Standing, entry);
        assert_eq!(
            remainders(theta)
                .get(&key)
                .cloned()
                .unwrap_or_else(Rat::zero),
            r,
            "entry {entry}"
        );
        let released = reading
            .released
            .iter()
            .find(|(locus, carrier, at, _)| (*locus, *carrier, *at) == key)
            .map_or_else(Rat::zero, |(.., e)| e.clone());
        assert_eq!(released, e, "entry {entry}");
    };
    let f = Lattice::new(lattice.exponent() + gamma_length(1)).unit();
    let half = &f / integer(2);
    let mut first = vec![Rat::zero(); n];
    first[..4].clone_from_slice(&[half.clone(), -&half, f.clone(), -&f]);
    let (once, reading) = theta.deposited(&standing(0, first)).unwrap();
    check(&once, &theta, &reading, 0, (1, -&f, -&half));
    check(&once, &theta, &reading, 1, (0, Rat::zero(), -&half));
    check(&once, &theta, &reading, 2, (1, -&f, Rat::zero()));
    check(&once, &theta, &reading, 3, (0, -&f, Rat::zero()));
    let f = Lattice::new(lattice.exponent() + gamma_length(2)).unit();
    let half = &f / integer(2);
    let mut second = vec![Rat::zero(); n];
    second[4] = &f * integer(4);
    second[5] = half.clone();
    let (twice, reading) = once.deposited(&standing(1, second)).unwrap();
    assert_eq!(twice.clock(Locus::Standing(1)), 2);
    check(
        &twice,
        &once,
        &reading,
        4,
        (1, &f * integer(-4), Rat::zero()),
    );
    check(&twice, &once, &reading, 5, (0, f.clone(), -&half));
    assert_eq!(
        lattice.div_rem_coordinate(&BigInt::from(-4), 3),
        (BigInt::zero(), BigInt::from(-4))
    );
    assert_eq!(
        lattice.div_rem_coordinate(&BigInt::from(7), 0),
        (BigInt::from(7), BigInt::zero())
    );
}

/// Lean `HNN/LatticeDeposit.{carried_remainder_bounded, run_onLattice}` on the constitution: the
/// chain control's deposits keep every retained entry on its locus's lattice and every carried
/// remainder in its half-open cell.
#[test]
fn deposits_keep_every_entry_on_its_lattice_with_its_remainder_bounded() {
    let run = chain_run();
    for (_, _, theta, _) in run {
        assert!(theta.on_lattice());
        for (locus, .., r) in theta.carried_remainders() {
            let half = theta.lattice(locus).unwrap().unit() / integer(2);
            assert!(-&half <= r && r < half, "{locus:?}: {r}");
        }
    }
    let theta = &run.last().unwrap().2;
    assert_eq!(theta.commit(), CHAIN_DEPOSITS as u64);
    assert!(!theta.carried_remainders().is_empty());
}

/// Every normal law of a constitution: the source ports, the contrast ports and the receiving maps.
fn solved_laws(theta: &Constitution, rings: usize) -> Vec<&NormalLaw> {
    (0..rings)
        .flat_map(|g| {
            [
                theta.source_law(g),
                Some(theta.contrast_law(g)),
                theta.receiving_law(g),
            ]
        })
        .flatten()
        .collect()
}

/// `HNN/Normal.normal_prox_step`'s solved chart by rank-one steps: integer features at unit weight
/// make `ΔH = Σ f fᵀ` land on the lattice, so the carried Gram takes it exactly and `H'⁻¹` follows
/// by Sherman–Morrison, sample by sample; over two deposits (clocks 1 and 2, the second from a
/// non-identity Gram) it is the carried Gram's true inverse, and the Gram is `I + Σ f fᵀ` exactly,
/// releasing nothing there.
#[test]
fn the_rank_one_solve_is_the_carried_grams_inverse() {
    let lattice = Lattice::new(4);
    let mut law = NormalLaw::with_prior(ExactRatMatrix::zero(2, 3).unwrap());
    let mut exact = ExactRatMatrix::identity(3).unwrap();
    for (clock, features) in [(1, [[1, 2, 0], [0, 1, -1]]), (2, [[2, 0, 1], [1, 1, 1]])] {
        let samples: Vec<Sample> = features
            .iter()
            .map(|f| {
                sample(
                    Rat::one(),
                    f.iter().map(|x| integer(*x)).collect(),
                    vec![rat(1, 3), rat(-2, 5)],
                )
            })
            .collect();
        let mut at = BudgetedCarry::new(lattice, clock);
        let next = law.deposited(&samples, &Rat::one(), &mut at).unwrap();
        for s in &samples {
            let f =
                ExactRatMatrix::shaped(3, 1, s.feature.iter().map(|x| vec![x.clone()]).collect())
                    .unwrap();
            exact = exact
                .add(&f.multiply(&f.transpose().unwrap()).unwrap())
                .unwrap();
        }
        assert_eq!(next.gram(), exact);
        assert!(
            at.released()
                .iter()
                .all(|(carrier, ..)| *carrier != Carrier::Gram)
        );
        assert_eq!(next.solved(), exact.inverse().unwrap());
        law = next;
    }
}

/// The number of chain deposits the budgeted carry's tests read: four, the fewest whose clocks
/// reach three Elias-gamma precisions (`k_1 = 1`, `k_2 = k_3 = 3`, `k_4 = 5`).
const CHAIN_DEPOSITS: usize = 4;

/// A deposit with its predecessor, successor and reading.
type Deposited = (Constitution, Deposit, Constitution, DepositReading);

/// **The chain control's deposits** at the declared steps, shared by the budgeted carry's tests:
/// one moment, refined and compared against cycling targets and deposited each time.
fn chain_run() -> &'static [Deposited] {
    static RUN: OnceLock<Vec<Deposited>> = OnceLock::new();
    RUN.get_or_init(|| {
        let field = chain();
        let reference = Reference::new(8, Steps::campaign_one(), OPEN_BUDGET);
        let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
        let (moment_id, _) = reference
            .ingest(&mut resident, None, &one_hot(&[1, 2, 3, 0, 2]))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let targets = [[2usize, 1], [0, 3], [1, 1], [3, 0], [0, 0], [2, 2], [1, 3]];
        (0..CHAIN_DEPOSITS)
            .map(|k| {
                let before = resident.constitution().clone();
                let (pending, _) = reference
                    .refine(&mut resident, &moment_id, &phases)
                    .unwrap();
                let (staged, compared) = reference
                    .compare(
                        &mut resident,
                        pending,
                        &one_hot(&targets[k % targets.len()]),
                    )
                    .unwrap();
                let deposit = compared.deposit.into_present().unwrap();
                let reading = reference
                    .deposit(&mut resident, staged)
                    .unwrap()
                    .deposit
                    .into_present()
                    .unwrap();
                let after = resident.constitution().clone();
                // Every normal law's solved chart is its carried Gram's true inverse, whichever
                // branch (Sherman–Morrison or one inversion) the deposit took.
                for law in solved_laws(&after, field.rings().len()) {
                    assert_eq!(law.solved(), law.gram().inverse().unwrap());
                }
                (before, deposit, after, reading)
            })
            .collect()
    })
}

/// One carried array of a locus, flat in the carry's entry order.
fn entries(theta: &Constitution, locus: Locus, carrier: Carrier) -> Vec<Rat> {
    let ring = |g: usize| match locus {
        Locus::SourcePort(_) => theta.source_law(g).unwrap(),
        Locus::ReceivingMap(_) => theta.receiving_law(g).unwrap(),
        _ => theta.contrast_law(g),
    };
    match (locus, carrier) {
        (Locus::Element(g) | Locus::SourcePort(g) | Locus::ReceivingMap(g), Carrier::Map) => {
            ring(g).map().entries().to_vec()
        }
        (Locus::Element(g) | Locus::SourcePort(g) | Locus::ReceivingMap(g), Carrier::Gram) => {
            ring(g).gram().entries().to_vec()
        }
        (Locus::Element(g), Carrier::Passive) => theta.passive_factor(g).entries().to_vec(),
        (Locus::Element(g), Carrier::PassiveScale) => vec![theta.ring_scales(g)[1].clone()],
        (Locus::Element(g), Carrier::Slices) => theta
            .slices(g)
            .iter()
            .flat_map(|(u, v)| u.iter().chain(v).cloned())
            .collect(),
        (Locus::Element(g), Carrier::SliceScale) => vec![theta.ring_scales(g)[2].clone()],
        (Locus::Standing(g), Carrier::Standing) => theta.standing(g).to_vec(),
        (Locus::Standing(g), Carrier::StandingScale) => vec![theta.ring_scales(g)[0].clone()],
        (Locus::SourcePort(g), Carrier::Pair { offset, family }) => {
            let pair = theta.pair_port(g, offset).unwrap();
            [pair.outputs(), pair.current_reads(), pair.earlier_reads()][family]
                .iter()
                .flatten()
                .cloned()
                .collect()
        }
        (Locus::SourcePort(g), Carrier::PairScale) => vec![theta.ring_scales(g)[3].clone()],
        (Locus::Channel(a), Carrier::Factor(0)) => theta.contact_storage(a).entries().to_vec(),
        (Locus::Channel(a), Carrier::Factor(1)) => theta.contact_stiffness(a).entries().to_vec(),
        (Locus::Channel(a), Carrier::Factor(_)) => theta.contact_dissipation(a).entries().to_vec(),
        (Locus::Channel(a), Carrier::FactorScale(i)) => vec![theta.contact_scales(a)[i].clone()],
        other => panic!("no carried array {other:?}"),
    }
}

/// **The exact updates of a deposit** per carried array (the laws of `NormalLaw::deposited` and
/// the factor steps, recomputed): `ΔH = Σ w f fᵀ`, `ΔW = γ Σ w g (H'⁻¹ f)ᵀ` at the successor's
/// solved chart, `Δh_x = Σ w|f|²` and `Δx = (η_x / h_x') G_x` at the successor's statistic.
fn updates(deposit: &Deposit, next: &Constitution) -> Vec<((Locus, Carrier), Vec<Rat>)> {
    let steps = next.steps();
    let mut out = Vec::new();
    for step in deposit.linear() {
        let locus = step.locus.locus();
        let law = match step.locus {
            LinearLocus::SourcePort(g) => next.source_law(g).unwrap(),
            LinearLocus::Contrast(g) => next.contrast_law(g),
            LinearLocus::Receiving(g) => next.receiving_law(g).unwrap(),
        };
        let (m, n) = (law.map().rows(), law.map().columns());
        let solved = law.solved();
        let (mut gram, mut map) = (vec![Rat::zero(); n * n], vec![Rat::zero(); m * n]);
        for s in &step.samples {
            let reach: Vec<Rat> = (0..n)
                .map(|i| {
                    (0..n)
                        .map(|j| solved.get(i, j).unwrap() * &s.feature[j])
                        .sum()
                })
                .collect();
            for i in 0..n {
                for j in 0..n {
                    gram[i * n + j] += &s.weight * &s.feature[i] * &s.feature[j];
                }
            }
            for i in 0..m {
                for j in 0..n {
                    map[i * n + j] += &steps.proxy * &s.weight * &s.covector[i] * &reach[j];
                }
            }
        }
        out.push(((locus, Carrier::Gram), gram));
        out.push(((locus, Carrier::Map), map));
    }
    for step in deposit.factors() {
        let locus = step.gradient.locus();
        let flat = |m: &ExactRatMatrix| m.entries().to_vec();
        let (scale, index, family): (Carrier, Rat, Vec<(Carrier, Vec<Rat>)>) = match &step.gradient
        {
            FactorGradient::Passive { ring, gradient } => (
                Carrier::PassiveScale,
                next.ring_scales(*ring)[1].clone(),
                vec![(Carrier::Passive, flat(gradient))],
            ),
            FactorGradient::Slices { ring, gradient } => (
                Carrier::SliceScale,
                next.ring_scales(*ring)[2].clone(),
                vec![(
                    Carrier::Slices,
                    gradient
                        .iter()
                        .flat_map(|(u, v)| u.iter().chain(v).cloned())
                        .collect(),
                )],
            ),
            FactorGradient::Standing { ring, gradient } => (
                Carrier::StandingScale,
                next.ring_scales(*ring)[0].clone(),
                vec![(Carrier::Standing, gradient.clone())],
            ),
            FactorGradient::PairPort {
                ring,
                offset,
                outputs,
                current,
                earlier,
            } => (
                Carrier::PairScale,
                next.ring_scales(*ring)[3].clone(),
                [outputs, current, earlier]
                    .into_iter()
                    .enumerate()
                    .map(|(family, rows)| {
                        (
                            Carrier::Pair {
                                offset: *offset,
                                family,
                            },
                            rows.iter().flatten().cloned().collect(),
                        )
                    })
                    .collect(),
            ),
            FactorGradient::Storage { contact, gradient }
            | FactorGradient::Stiffness { contact, gradient }
            | FactorGradient::Dissipation { contact, gradient } => {
                let i = match &step.gradient {
                    FactorGradient::Storage { .. } => 0,
                    FactorGradient::Stiffness { .. } => 1,
                    _ => 2,
                };
                (
                    Carrier::FactorScale(i),
                    next.contact_scales(*contact)[i].clone(),
                    vec![(Carrier::Factor(i), flat(gradient))],
                )
            }
        };
        let rate = &steps.factor / index;
        out.push(((locus, scale), vec![step.energy.clone()]));
        for (carrier, gradient) in family {
            out.push((
                (locus, carrier),
                gradient.iter().map(|x| &rate * x).collect(),
            ));
        }
    }
    out
}

/// The carried remainders of a constitution, by locus, carrier and entry.
fn remainders(theta: &Constitution) -> BTreeMap<(Locus, Carrier, usize), Rat> {
    theta
        .carried_remainders()
        .into_iter()
        .map(|(locus, carrier, entry, r)| ((locus, carrier, entry), r))
        .collect()
}

/// The exact sums of a run's updates and of its released residuals, per entry, with each carried
/// array's starting and final values.
struct Ledger {
    updates: BTreeMap<(Locus, Carrier, usize), Rat>,
    released: BTreeMap<(Locus, Carrier, usize), Rat>,
    arrays: Vec<(Locus, Carrier)>,
}

fn ledger(run: &[Deposited]) -> Ledger {
    let mut ledger = Ledger {
        updates: BTreeMap::new(),
        released: BTreeMap::new(),
        arrays: Vec::new(),
    };
    for (_, deposit, next, reading) in run {
        for (array, values) in updates(deposit, next) {
            if !ledger.arrays.contains(&array) {
                ledger.arrays.push(array);
            }
            for (entry, value) in values.into_iter().enumerate() {
                *ledger
                    .updates
                    .entry((array.0, array.1, entry))
                    .or_insert_with(Rat::zero) += value;
            }
        }
        for (locus, carrier, entry, e) in &reading.released {
            *ledger
                .released
                .entry((*locus, *carrier, *entry))
                .or_insert_with(Rat::zero) += e;
        }
    }
    ledger
}

/// Lean `HNN/LatticeDeposit.{lattice_deposit_accounting, run_accounting}`: over the chain's
/// deposits, per entry of every carried array a deposit reached, the applied lattice steps plus the
/// carried remainder plus the residuals released (read from each `DepositReading`) equal the exact
/// sum of the updates: nothing is rounded away unreported.
#[test]
fn the_budgeted_carry_accounts_for_every_update() {
    let run = chain_run();
    let (first, last) = (&run[0].0, &run.last().unwrap().2);
    let ledger = ledger(run);
    let (start, end) = (remainders(first), remainders(last));
    let mut checked = 0;
    for &(locus, carrier) in &ledger.arrays {
        let (before, after) = (
            entries(first, locus, carrier),
            entries(last, locus, carrier),
        );
        for (entry, (x0, x)) in before.iter().zip(&after).enumerate() {
            let key = (locus, carrier, entry);
            let at = |map: &BTreeMap<_, Rat>| map.get(&key).cloned().unwrap_or_else(Rat::zero);
            assert_eq!(
                x + at(&end) + at(&ledger.released),
                x0 + at(&start) + at(&ledger.updates),
                "{key:?}"
            );
            checked += 1;
        }
    }
    assert!(checked > 100 && !ledger.released.is_empty());
    assert!(run.iter().all(|(.., reading)| {
        reading.released_bits
            == reading
                .released
                .iter()
                .map(|(.., e)| e.numer().bits() + e.denom().bits())
                .sum::<u64>()
    }));
    assert!(run.iter().any(|(.., reading)| reading.stepped > 0));
}

/// Lean `HNN/LatticeDeposit.{gamma_kraft_lt_one, release_bounded_since_founding,
/// within_one_unit_since_founding}`: the Elias-gamma weights' partial sums stay below one (exactly
/// `1 − 2^(−J)` at `M = 2^J − 1`); over the chain's deposits every entry's released residuals sum to
/// less than half a unit and its value is within one unit of the exact accumulation; and an
/// adversarial update that releases the most a clock allows (just under half a fine unit, the same
/// sign every time) over 255 deposits releases `(1 − 2^(−8))(1 − 2^(−20))·u/2`, just under `u/2`,
/// with the value unmoved.
#[test]
fn the_release_since_the_founding_stays_below_half_a_unit() {
    let mut partial = Rat::zero();
    for m in 1u64..=4095 {
        partial += Rat::new(BigInt::one(), BigInt::one() << gamma_length(m) as usize);
        assert!(partial < Rat::one());
        if (m + 1).is_power_of_two() {
            let j = (m + 1).ilog2() as usize;
            assert_eq!(
                partial,
                Rat::one() - Rat::new(BigInt::one(), BigInt::one() << j)
            );
        }
    }
    let run = chain_run();
    let (first, last) = (&run[0].0, &run.last().unwrap().2);
    let ledger = ledger(run);
    for &(locus, carrier) in &ledger.arrays {
        let u = last.lattice(locus).unwrap().unit();
        let (before, after) = (
            entries(first, locus, carrier),
            entries(last, locus, carrier),
        );
        for (entry, (x0, x)) in before.iter().zip(&after).enumerate() {
            let key = (locus, carrier, entry);
            let at = |map: &BTreeMap<_, Rat>| map.get(&key).cloned().unwrap_or_else(Rat::zero);
            assert!(at(&ledger.released).abs() < &u / integer(2), "{key:?}");
            assert!((x - (x0 + at(&ledger.updates))).abs() < u, "{key:?}");
        }
    }
    // The adversary: ring 0's standing, rate η_x / h_x = ½ (no energy), each update just under half
    // a fine unit of the clock it advances to.
    let field = chain();
    let mut theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let n = field.ring(0).width();
    let lattice = theta.lattice(Locus::Standing(0)).unwrap();
    let u = lattice.unit();
    let shy = Rat::one() - Rat::new(BigInt::one(), BigInt::one() << 20);
    let (mut released, mut applied) = (Rat::zero(), Rat::zero());
    for m in 1u64..=255 {
        let fine = Lattice::new(lattice.exponent() + gamma_length(m));
        let update = fine.unit() / integer(2) * &shy;
        let deposit = Deposit::new(
            theta.commit(),
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing {
                    ring: 0,
                    gradient: vec![&update * integer(2); n],
                },
                energy: Rat::zero(),
            }],
            Vec::new(),
        );
        let (next, reading) = theta.deposited(&deposit).unwrap();
        assert_eq!(next.clock(Locus::Standing(0)), m);
        assert_eq!(reading.released.len(), n);
        released += &reading.released[0].3;
        applied += &update;
        theta = next;
    }
    assert_eq!(released, applied);
    let budget =
        (Rat::one() - Rat::new(BigInt::one(), BigInt::one() << 8)) * &shy * &u / integer(2);
    assert_eq!(released, budget);
    assert!(released < &u / integer(2));
    assert!(theta.standing(0).iter().all(Zero::is_zero));
    assert!(theta.carried_remainders().is_empty());
}

/// Lean `HNN/LatticeDeposit.{carried_gram_posDef, carried_gram_posDef_rule}`: after every chain
/// deposit each carried Gram `H` of width `n` is within one unit of the exact Gram (the unit prior
/// plus every statistic that reached it), which is `⪰ I`; `H − (1 − n·u) I` has no negative
/// inertia, and `n·u ≤ 1/(2L_R)`, so `H ⪰ (1 − 1/(2L_R)) I` with no clamp.
#[test]
fn the_carried_gram_stays_positive_definite() {
    let run = chain_run();
    let grain = integer(16);
    let mut exact: BTreeMap<Locus, Vec<Rat>> = BTreeMap::new();
    let mut checked = 0;
    for (_, deposit, next, _) in run {
        for ((locus, carrier), values) in updates(deposit, next) {
            if carrier != Carrier::Gram {
                continue;
            }
            let start = exact
                .entry(locus)
                .or_insert_with(|| entries(&run[0].0, locus, Carrier::Gram));
            for (x, dx) in start.iter_mut().zip(values) {
                *x += dx;
            }
        }
        for (locus, gram_exact) in &exact {
            let gram = entries(next, *locus, Carrier::Gram);
            let n = (0..=gram.len()).find(|n| n * n == gram.len()).unwrap();
            let u = next.lattice(*locus).unwrap().unit();
            assert!(gram.iter().zip(gram_exact).all(|(h, x)| (h - x).abs() < u));
            let identity = ExactRatMatrix::identity(n).unwrap();
            let above_prior = flat(gram_exact, n).subtract(&identity).unwrap();
            assert_eq!(inertia(&matrix_form(&above_prior).unwrap()).negative, 0);
            let margin = Rat::one() - integer(n as i64) * &u;
            assert!(integer(2) * &grain * integer(n as i64) * &u <= Rat::one());
            let shifted = flat(&gram, n).subtract(&identity.scaled(&margin)).unwrap();
            assert_eq!(inertia(&matrix_form(&shifted).unwrap()).negative, 0);
            assert_eq!(inertia(&matrix_form(&flat(&gram, n)).unwrap()).positive, n);
            checked += 1;
        }
    }
    assert!(checked >= 2 * CHAIN_DEPOSITS);
}

/// A flat square array as a matrix.
fn flat(entries: &[Rat], n: usize) -> ExactRatMatrix {
    ExactRatMatrix::shaped(n, n, entries.chunks(n).map(<[Rat]>::to_vec).collect()).unwrap()
}

/// Lean `HNN/LatticeDeposit.{remainder_numerator_bounded, remainder_rat_bits_bounded}`: after every
/// chain deposit each carried remainder at a locus of clock `m` is `ρ·2^(−L−k_m)` with
/// `|ρ| ≤ 2^(k_m−1)`, and takes at most `L + 2k_m + 1` bits; the remainders' bits therefore stay
/// bounded by the carried entries, not by the updates' denominators.
#[test]
fn a_carried_remainder_takes_its_lattice_and_clock_bits() {
    for (_, _, theta, _) in chain_run() {
        let mut bound = 0u64;
        for (locus, _, _, r) in theta.carried_remainders() {
            let lattice = theta.lattice(locus).unwrap();
            let k = gamma_length(theta.clock(locus));
            let scaled = &r * Rat::from_integer(BigInt::one() << (lattice.exponent() + k) as usize);
            assert!(scaled.is_integer(), "{locus:?}: {r}");
            assert!(scaled.abs() <= Rat::from_integer(BigInt::one() << (k - 1) as usize));
            let bits = r.numer().bits() + r.denom().bits();
            assert!(bits <= u64::from(lattice.exponent() + 2 * k + 1));
            bound += u64::from(lattice.exponent() + 2 * k + 1);
        }
        assert!(theta.carrier_bits().remainders <= bound);
    }
}

/// Lean `HNN/LatticeDeposit.{carry_zero, carry_entry_zero}`: a deposit whose updates are all zero
/// leaves the constitution but its commit (no clock advances, nothing is released or stepped); a
/// deposit that updates one entry of a locus advances its clock once and leaves every other entry's
/// value and remainder, releasing nothing there.
#[test]
fn a_zero_update_advances_nothing() {
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let n = field.ring(1).width();
    let standing = |commit: u64, gradient: Vec<Rat>| {
        Deposit::new(
            commit,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing { ring: 1, gradient },
                energy: Rat::zero(),
            }],
            Vec::new(),
        )
    };
    let (thirds, _) = theta.deposited(&standing(0, vec![rat(1, 3); n])).unwrap();
    assert_eq!(thirds.clock(Locus::Standing(1)), 1);
    let carried = remainders(&thirds);
    assert_eq!(carried.len(), n);
    let (zero, reading) = thirds
        .deposited(&standing(1, vec![Rat::zero(); n]))
        .unwrap();
    assert_eq!(zero.clock(Locus::Standing(1)), 1);
    assert_eq!(zero.standing(1), thirds.standing(1));
    assert_eq!(remainders(&zero), carried);
    assert!(reading.released.is_empty() && reading.stepped == 0);
    let mut one = vec![Rat::zero(); n];
    one[0] = rat(1, 5);
    let (moved, reading) = zero.deposited(&standing(2, one)).unwrap();
    assert_eq!(moved.clock(Locus::Standing(1)), 2);
    assert!(reading.released.iter().all(|(_, _, entry, _)| *entry == 0));
    for (i, (x, y)) in moved
        .standing(1)
        .iter()
        .zip(zero.standing(1))
        .enumerate()
        .skip(1)
    {
        let key = (Locus::Standing(1), Carrier::Standing, i);
        assert_eq!(x, y);
        assert_eq!(remainders(&moved).get(&key), carried.get(&key));
    }
}

fn psd(factor: &ExactRatMatrix) -> bool {
    let form = factor.multiply(&factor.transpose().unwrap()).unwrap();
    inertia(&matrix_form(&form).unwrap()).negative == 0
}

/// Lean `HNN/Normal.factorCarrier_psd`, `additive_carrier_update_leaves_psd`: arbitrary factor
/// steps keep `C = ccᵀ`, `K = bbᵀ`, `D = FFᵀ` and `−W_s = ffᵀ` positive semidefinite with no clamp;
/// an additive step of the form itself does not.
#[test]
fn the_factor_carriers_stay_positive_semidefinite_with_no_clamp() {
    let field = chain();
    let theta = generic(&field, 7);
    let mut draw = Draw::new(8);
    let big = |draw: &mut Draw, k: usize| draw.matrix(k, k).scaled(&integer(-40));
    let factors = vec![
        FactorStep {
            gradient: FactorGradient::Storage {
                contact: 0,
                gradient: big(&mut draw, field.contact(0).width()),
            },
            energy: Rat::zero(),
        },
        FactorStep {
            gradient: FactorGradient::Stiffness {
                contact: 1,
                gradient: big(&mut draw, field.contact(1).width()),
            },
            energy: Rat::zero(),
        },
        FactorStep {
            gradient: FactorGradient::Dissipation {
                contact: 1,
                gradient: big(&mut draw, field.contact(1).width()),
            },
            energy: Rat::zero(),
        },
        FactorStep {
            gradient: FactorGradient::Passive {
                ring: 1,
                gradient: big(&mut draw, field.ring(1).width()),
            },
            energy: Rat::zero(),
        },
    ];
    let deposit = Deposit::new(0, Vec::new(), factors, Vec::new());
    let (next, _) = theta.deposited(&deposit).unwrap();
    for a in 0..2 {
        assert!(psd(next.contact_storage(a)));
        assert!(psd(next.contact_stiffness(a)));
        assert!(psd(next.contact_dissipation(a)));
    }
    assert!(psd(next.passive_factor(1)));
    let additive = ExactRatMatrix::identity(2)
        .unwrap()
        .subtract(&ExactRatMatrix::identity(2).unwrap().scaled(&integer(2)))
        .unwrap();
    assert_eq!(inertia(&matrix_form(&additive).unwrap()).negative, 2);
}

/// Lean `HNN/Normal.reaction_deposit_storage_unchanged`: a deposit of reaction material and ports
/// leaves the storage forms, so its energy growth is `ε_k = 0`; a storage deposit (the counterexample,
/// `storage_deposit_does_work`) grows it.
#[test]
fn reaction_deposits_have_zero_energy_growth() {
    let field = chain();
    let theta = generic(&field, 9);
    let mut draw = Draw::new(10);
    let n = field.ring(1).width();
    let reaction = Deposit::new(
        0,
        vec![LinearStep {
            locus: LinearLocus::Contrast(1),
            samples: vec![sample(Rat::one(), draw.vector(n), draw.vector(n))],
        }],
        vec![FactorStep {
            gradient: FactorGradient::Slices {
                ring: 1,
                gradient: (0..n).map(|_| (draw.vector(n), draw.vector(n))).collect(),
            },
            energy: Rat::one(),
        }],
        Vec::new(),
    );
    let (_, reading) = theta.deposited(&reaction).unwrap();
    assert_eq!(reading.growth, Some(Rat::zero()));
    let k = field.contact(0).width();
    let storage = Deposit::new(
        0,
        Vec::new(),
        vec![FactorStep {
            gradient: FactorGradient::Storage {
                contact: 0,
                gradient: ExactRatMatrix::identity(k).unwrap(),
            },
            energy: Rat::zero(),
        }],
        Vec::new(),
    );
    let (_, grown) = theta.deposited(&storage).unwrap();
    assert!(grown.growth.is_none_or(|epsilon| epsilon > Rat::zero()));
}

/// Design (d), the budget and stop rule: a deposit whose successor exceeds `B_Θ` is refused with
/// `ConstitutionBudget`, naming the loci that grew most; the predecessor stays published, and no
/// further deposit is admitted.
#[test]
fn the_budget_refuses_the_successor_and_keeps_the_predecessor() {
    let field = chain();
    let (current, _) = moment(&field, 11, 0);
    // One bit above the declared initial constitution: the first deposit that grows it is refused.
    let budget = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET)
        .unwrap()
        .exact_bits()
        + 1;
    let reference = Reference::new(8, Steps::campaign_one(), budget);
    let tight = Constitution::initial(&field, Steps::campaign_one(), budget).unwrap();
    let mut resident = reference.mount_with(&field, &current, tight).unwrap();
    let before = resident.constitution().clone();
    let (moment_id, _) = reference
        .ingest(&mut resident, None, &one_hot(&[1, 2, 3, 0, 2, 1, 3]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let mut refused = None;
    for _ in 0..4 {
        let (pending, _) = reference
            .refine(&mut resident, &moment_id, &phases)
            .unwrap();
        let (staged, _) = reference
            .compare(&mut resident, pending, &one_hot(&[2, 1]))
            .unwrap();
        match reference.deposit(&mut resident, staged) {
            Ok(_) => continue,
            Err(error) => {
                refused = Some(error);
                break;
            }
        }
    }
    let Some(HnnError::ConstitutionBudget {
        bits,
        budget: declared,
        loci,
        ..
    }) = refused
    else {
        panic!("the budget refuses: {refused:?}");
    };
    assert!(bits > declared && !loci.is_empty());
    let stop = resident.stopped().unwrap().commit;
    assert_eq!(resident.constitution().commit(), stop);
    if stop == 0 {
        assert_eq!(resident.constitution(), &before);
    }
    let (pending, _) = reference
        .refine(&mut resident, &moment_id, &phases)
        .unwrap();
    let (staged, _) = reference
        .compare(&mut resident, pending, &one_hot(&[0, 0]))
        .unwrap();
    assert!(matches!(
        reference.deposit(&mut resident, staged),
        Err(HnnError::DepositsStopped { .. })
    ));
}

/// Lean `HNN/Normal.standing_deposit`, `sheetClass_locally_constant`, `sheet_fold_witness`: the
/// standing moves only by a deposit through its lock chart; the word reads it only by its sheet
/// classes, which change exactly where the deposit carries a contrast across zero.
#[test]
fn the_standing_moves_only_by_deposit_and_a_class_only_across_zero() {
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET)
        .unwrap()
        .with_ports(2, Some(vec![rat(1, 8); 4]), None, None)
        .unwrap();
    let current = Current::at_rest(&field);
    let classes = |theta: &Constitution| -> Vec<Vec<bool>> {
        Operands::at_cut(&field, theta, &current)
            .unwrap()
            .rings()
            .iter()
            .map(|ring| ring.sheets().to_vec())
            .collect()
    };
    let start = classes(&theta);
    let step = |amount: Rat| {
        Deposit::new(
            0,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing {
                    ring: 2,
                    gradient: vec![amount; 4],
                },
                energy: Rat::zero(),
            }],
            Vec::new(),
        )
    };
    // q_2 = 1/8 on every coordinate; ring 2's contrast is U q_1 − q_2 = −1/8 on its matched
    // coordinates. A small step keeps every class; a step past the fold flips them.
    let (small, _) = theta.deposited(&step(rat(1, 16))).unwrap();
    assert_eq!(classes(&small), start);
    assert_ne!(small.standing(2), theta.standing(2));
    let (crossed, _) = theta.deposited(&step(rat(-1, 2))).unwrap();
    assert_ne!(classes(&crossed)[2], start[2]);
}

/// Lean `HNN/Normal.deposit_local`, `windowGram_apply_eq_zero`, `HNN/Retention.deposit_descends`:
/// on the six-ring path a compare's deposit reaches only the causal diamond; every locus outside it
/// is unchanged, and each element's statistic (carried value plus remainder) sums only over its
/// window (one tick each here).
#[test]
fn a_deposit_reaches_only_the_diamond_and_sums_only_its_window() {
    let field = six_path(2);
    let theta = generic(&field, 13);
    let (current, open) = moment(&field, 14, 9);
    let phases = phases(&field, &theta, &current);
    let pending = PendingRatio::produce(&current, &open, &phases, 0);
    let (word, faces) = pending.read(&field, &theta).unwrap();
    let targets = [1usize, 0];
    let anchors = target_phases(&field, pending.anchor(), 2, &targets).unwrap();
    let ratio = HolonRatio::compare(faces, &targets, &anchors).unwrap();
    let back = word
        .pull_back(
            &ratio.covector().unwrap(),
            theta.receiving_map(2).unwrap(),
            &current.lift()[2],
            &phases,
        )
        .unwrap();
    let (_, deposit) = compose(&field, &theta, &pending, &back).unwrap();
    for step in deposit.linear() {
        if let LinearLocus::Contrast(g) = step.locus {
            assert_eq!(step.samples.len(), 1, "ring {g}'s window is one tick");
            let tick = back.elements[g].iter().find(|tick| tick.tick == g).unwrap();
            assert_eq!(step.samples[0].feature, tick.contrast);
        }
    }
    let (next, reading) = theta.deposited(&deposit).unwrap();
    for g in 3..6 {
        assert_eq!(next.passive_factor(g), theta.passive_factor(g));
        assert_eq!(next.contrast_port(g), theta.contrast_port(g));
        assert_eq!(next.slices(g), theta.slices(g));
    }
    for g in 4..6 {
        assert_eq!(next.standing(g), theta.standing(g));
    }
    for a in 3..5 {
        assert_eq!(next.contact_storage(a), theta.contact_storage(a));
        assert_eq!(next.contact_stiffness(a), theta.contact_stiffness(a));
    }
    assert!(!reading.loci.contains(&Locus::Element(3)));
    assert!(reading.loci.contains(&Locus::Channel(2)));
    // The carried Gram: its lattice value plus its remainder plus the residual the deposit released
    // is the exact statistic.
    let law = next.contrast_law(1);
    let gram = law.gram().add(&law.gram_remainder()).unwrap();
    let feature = &deposit
        .linear()
        .iter()
        .find(|step| step.locus == LinearLocus::Contrast(1))
        .unwrap()
        .samples[0]
        .feature;
    for i in 0..4 {
        for j in 0..4 {
            let prior = if i == j { Rat::one() } else { Rat::zero() };
            let released: Rat = reading
                .released
                .iter()
                .filter(|(locus, carrier, entry, _)| {
                    (*locus, *carrier, *entry) == (Locus::Element(1), Carrier::Gram, i * 4 + j)
                })
                .map(|(.., e)| e.clone())
                .sum();
            assert_eq!(
                gram.get(i, j).unwrap() + released,
                prior + &feature[i] * &feature[j]
            );
        }
    }
}

/// A deposit staged at one commit is refused at another: `E` is never mixed across two cuts.
#[test]
fn a_stale_deposit_is_refused() {
    let field = chain();
    let theta = generic(&field, 15);
    let mut draw = Draw::new(16);
    let n = field.ring(1).width();
    let deposit = Deposit::new(
        0,
        vec![LinearStep {
            locus: LinearLocus::Contrast(1),
            samples: vec![sample(Rat::one(), draw.vector(n), draw.vector(n))],
        }],
        Vec::new(),
        Vec::new(),
    );
    let (next, _) = theta.deposited(&deposit).unwrap();
    assert_eq!(
        next.deposited(&deposit),
        Err(HnnError::StaleDeposit {
            staged: 0,
            published: 1
        })
    );
}

/// The declared initial constitution and priors (design (d), R3 D2), on the chain control: `E = 0`
/// (`2d_0 × |A|`), the receiving map `R` (`2|A| × 2d_R`) the declared `±1` pattern times 1/2, the
/// pair port's outputs 0 on ring 0's width, `W_s = −½I` (the passive factor `½I`), `W_c = 0`,
/// `q = 0`, the slices the skew cyclic shift, `C = I` and `K = D = ½I` on every channel.
#[test]
fn the_initial_constitution_is_the_declared_one() {
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let source = theta.source_port(0).unwrap();
    assert!((source.rows(), source.columns()) == (4, 4));
    assert!(source.entries().iter().all(Zero::is_zero));
    let map = theta.receiving_map(2).unwrap();
    assert_eq!((map.rows(), map.columns()), (8, 4));
    assert!(map.entries().iter().all(|x| x.abs() == rat(1, 2)));
    assert_eq!(
        map.get(3, 2).unwrap(),
        &(declared_sign((1 << 40) + (2 << 20), 3, 2) * rat(1, 2))
    );
    let pair = theta.pair_port(0, 1).unwrap();
    assert_eq!(pair.rank(), 4);
    assert!(pair.outputs().iter().flatten().all(Zero::is_zero));
    for g in 0..field.rings().len() {
        let n = field.ring(g).width();
        assert_eq!(
            theta.passive_factor(g),
            &ExactRatMatrix::identity(n).unwrap().scaled(&rat(1, 2))
        );
        assert!(theta.contrast_port(g).entries().iter().all(Zero::is_zero));
        assert!(theta.standing(g).iter().all(Zero::is_zero));
        for (rho, (u, v)) in theta.slices(g).iter().enumerate() {
            assert!(u[rho].is_one() && v[(rho + 1) % n].is_one());
        }
    }
    for a in 0..field.contacts().len() {
        let k = field.contact(a).width();
        let identity = ExactRatMatrix::identity(k).unwrap();
        assert_eq!(theta.contact_storage(a), &identity);
        assert_eq!(theta.contact_stiffness(a), &identity.scaled(&rat(1, 2)));
        assert_eq!(theta.contact_dissipation(a), &identity.scaled(&rat(1, 2)));
    }
    assert_eq!(theta.commit(), 0);
    assert_eq!(theta.steps(), &Steps::campaign_one());
}

/// Design (d), "Reaction": **a complex-bilinear block is refused at declaration.** A reaction slice
/// is declared only as its factor pair (`Constitution::with_element`, whose `compile_fail` doctest
/// refuses a full block, `E0308`), so every declared slice `u vᵀ − v uᵀ` is skew and workless, and
/// the ring's element `K = W_s + Σ σ_ρ A_ρ` has exactly its passive part as its symmetric part, for
/// any declared factors (the owner's real-bilinear reaction, Lean
/// `Holon/Reaction.skewReaction_workless`). The block a complex-bilinear reaction needs is not
/// workless: on one complex node, multiplication by `c` realifies to `[[Re c, −Im c], [Im c, Re c]]`,
/// whose power `⟨x, M x⟩ = Re c · |x|²` vanishes for `c = i` and not for `c = 1`, so no nonzero
/// such block is power-neutral for both (Lean `Holon/Reaction.bilinear_reaction_workless_iff_zero`).
#[test]
fn a_complex_bilinear_block_has_no_declaration() {
    let field = chain();
    let mut draw = Draw::new(97);
    let ring = 1;
    let n = field.ring(ring).width();
    let slices: Vec<(Vec<Rat>, Vec<Rat>)> =
        (0..n).map(|_| (draw.vector(n), draw.vector(n))).collect();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET)
        .unwrap()
        .with_ports(ring, Some(draw.vector(n)), None, None)
        .unwrap()
        .with_element(ring, draw.matrix(n, n), draw.matrix(n, n), slices)
        .unwrap();
    let operands = crate::hnn::propagation::ring_operands(&field, &theta, ring).unwrap();
    let (element, passive) = (operands.element(), operands.passive());
    assert!(operands.sheets().iter().any(|sheet| !*sheet));
    for i in 0..n {
        for j in 0..n {
            let symmetric = element.get(i, j).unwrap() + element.get(j, i).unwrap();
            assert_eq!(symmetric, passive.get(i, j).unwrap() * integer(2));
        }
    }
    for _ in 0..4 {
        let x = draw.vector(n);
        let reaction = element.subtract(passive).unwrap().apply(&x).unwrap();
        let power: Rat = x.iter().zip(&reaction).map(|(a, b)| a * b).sum();
        assert!(power.is_zero());
    }
    let multiply = |re: Rat, im: Rat| {
        ExactRatMatrix::shaped(2, 2, vec![vec![re.clone(), -im.clone()], vec![im, re]]).unwrap()
    };
    let x = vec![rat(3, 2), rat(-1, 3)];
    let power = |block: &ExactRatMatrix| -> Rat {
        let moved = block.apply(&x).unwrap();
        x.iter().zip(&moved).map(|(a, b)| a * b).sum()
    };
    assert!(power(&multiply(Rat::zero(), Rat::one())).is_zero());
    assert_eq!(
        power(&multiply(Rat::one(), Rat::zero())),
        &x[0] * &x[0] + &x[1] * &x[1]
    );
}
