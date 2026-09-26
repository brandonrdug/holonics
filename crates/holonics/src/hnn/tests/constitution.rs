//! Deposition, per locus: the prox step through the solved chart and its released residual, the
//! chart's certificate, warm start and refinement, the statistic's standing, the budgeted carry (its
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
    BudgetedCarry, Carrier, ChartRule, Constitution, DepositReading, FactorGradient, FactorStep,
    Lattice, LinearLocus, LinearStep, Locus, NormalLaw, Sample, Steps, declared_sign, gamma_length,
    refined_once,
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
        target: None,
    }
}

/// `‖A‖∞`, the largest absolute row sum (Lean `HNN/LatticeWord.rowNorm`).
fn row_norm(matrix: &ExactRatMatrix) -> Rat {
    (0..matrix.rows())
        .map(|i| {
            (0..matrix.columns())
                .map(|j| matrix.get(i, j).unwrap().abs())
                .sum::<Rat>()
        })
        .max()
        .unwrap_or_else(Rat::zero)
}

/// `1 − X H`, the left residual of a chart `X` of `H⁻¹`.
fn left_residual(chart: &ExactRatMatrix, gram: &ExactRatMatrix) -> ExactRatMatrix {
    ExactRatMatrix::identity(gram.rows())
        .unwrap()
        .subtract(&chart.multiply(gram).unwrap())
        .unwrap()
}

/// The chart rule of the fixtures: the lattice `L`, and the grain `L_R = 16` of campaign 1.
fn rule(lattice: Lattice) -> ChartRule {
    ChartRule::new(lattice, 16)
}

/// Lean `HNN/Normal.normal_prox_step` at the carried operands through the executed chart,
/// `HNN/LatticeWord.{prox_chart_residual, prox_chart_certificate}`, `HNN/LatticeDeposit.carry`,
/// `carry_accounting`: over three deposits (clocks 1, 2, 3), the carried Gram moves by exactly
/// `Σ w f fᵀ` less its released residuals (value plus remainder); the solved chart `X̂` of the carried
/// successor Gram `H'` is symmetric, on its lattice, and certified, `‖1 − X̂H'‖∞ = δ ≤ δ_ℓ`; the map
/// moves by exactly `γ Σ w g fᵀX̂` less its released residuals, so `(W + ΔW)H' = WH' + γG − ρ` with the
/// released prox residual `ρ = γG(1 − X̂H')`, whose norm is within the reading's certificate; every
/// entry stays on the lattice, every remainder in its half-open cell on the fine lattice of its clock,
/// and every residual within half a fine unit.
#[test]
fn the_prox_step_releases_its_charts_residual_at_the_carried_operands() {
    let mut draw = Draw::new(3);
    let lattice = Lattice::new(4);
    let rule = rule(lattice);
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
        let (next, reading) = law.deposited(&samples, &proxy, &rule, &mut at).unwrap();
        let reading = reading.unwrap();
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
        // The chart: symmetric, on its lattice, certified below the rule's target.
        let chart = next.solved();
        assert_eq!(chart, chart.transpose().unwrap());
        let chart_lattice = Lattice::new(reading.exponent);
        assert!(chart.entries().iter().all(|x| chart_lattice.contains(x)));
        let residual = left_residual(&chart, &next.gram());
        assert_eq!(row_norm(&residual), reading.certificate);
        assert_eq!(&reading.certificate, next.chart().certificate());
        assert!(reading.certificate <= rule.target() && reading.target == rule.target());
        // The map moves by the executed chart's step.
        let step = gradient.multiply(&chart).unwrap().scaled(&proxy);
        assert_eq!(
            next_map
                .subtract(&map)
                .unwrap()
                .add(&released(Carrier::Map, 3, 4))
                .unwrap(),
            step
        );
        // The prox identity up to the released residual ρ = γ G (1 − X̂H').
        let rho = gradient.multiply(&residual).unwrap().scaled(&proxy);
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
                .subtract(&rho)
                .unwrap()
        );
        assert!(row_norm(&rho) <= reading.released);
        assert_eq!(reading.read, rule.read(&reading.released));
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
            &rule(lattice),
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
            &rule(lattice),
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

/// Every normal law of a constitution, with its locus: the source ports, the contrast ports and the
/// receiving maps.
fn solved_laws(theta: &Constitution, rings: usize) -> Vec<(Locus, &NormalLaw)> {
    (0..rings)
        .flat_map(|g| {
            [
                theta.source_law(g).map(|law| (Locus::SourcePort(g), law)),
                Some((Locus::Element(g), theta.contrast_law(g))),
                theta
                    .receiving_law(g)
                    .map(|law| (Locus::ReceivingMap(g), law)),
            ]
        })
        .flatten()
        .collect()
}

/// Lean `HNN/LatticeWord.{prox_chart_certificate, inverse_chart_deviation}` on a normal law's solved
/// chart: integer features at unit weight make `ΔH = Σ f fᵀ` land on the lattice, so the carried Gram
/// is `I + Σ f fᵀ` exactly (releasing nothing there); over two deposits (clocks 1 and 2, the second
/// from a non-identity Gram) the chart `X̂` is symmetric with `H'X̂` within `δ ≤ δ_ℓ` of `1` in both
/// residuals (`1 − H'X̂ = (1 − X̂H')ᵀ`), and within `‖X̂‖∞δ/(1 − δ)` of the exact inverse.
#[test]
fn the_solved_chart_certifies_the_carried_grams_inverse() {
    let lattice = Lattice::new(4);
    let rule = rule(lattice);
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
        let (next, reading) = law
            .deposited(&samples, &Rat::one(), &rule, &mut at)
            .unwrap();
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
        let chart = next.solved();
        let delta = next.chart().certificate().clone();
        assert_eq!(Some(&delta), reading.as_ref().map(|r| &r.certificate));
        assert!(delta <= rule.target());
        let left = left_residual(&chart, &exact);
        let right = ExactRatMatrix::identity(3)
            .unwrap()
            .subtract(&exact.multiply(&chart).unwrap())
            .unwrap();
        assert_eq!(right, left.transpose().unwrap());
        assert_eq!(row_norm(&left), delta);
        let inverse = exact.inverse().unwrap();
        let deviation = row_norm(&inverse.subtract(&chart).unwrap());
        assert!(deviation <= row_norm(&chart) * &delta / (Rat::one() - &delta));
        law = next;
    }
}

/// Lean `HNN/LatticeWord.{warm_start_residual, warm_start_certificate}` and the warm start's rank-one
/// steps: after a deposit of a large return, the previous chart alone has residual exactly
/// `(1 − X̂H) − X̂ΔH`, within `δ + ‖ΔH‖∞‖X̂‖∞` and past 1 (outside Newton–Schulz's contraction); the
/// rank-one steps at the chart's lattice carry the residual instead, so the warm start's certificate
/// is small, and the chart reaches its target by refinement with no restart.
#[test]
fn the_warm_start_carries_the_residual_through_the_rank_one_steps() {
    let lattice = Lattice::new(4);
    let rule = rule(lattice);
    let law = NormalLaw::with_prior(ExactRatMatrix::zero(2, 4).unwrap());
    let ints = |values: [i64; 4]| values.iter().map(|x| integer(*x)).collect::<Vec<Rat>>();
    let covector = || vec![rat(1, 3), rat(-1, 2)];
    let (first, _) = law
        .deposited(
            &[
                sample(Rat::one(), ints([1, 2, 0, 0]), covector()),
                sample(Rat::one(), ints([0, 1, 1, 0]), covector()),
            ],
            &Rat::one(),
            &rule,
            &mut BudgetedCarry::new(lattice, 1),
        )
        .unwrap();
    let (second, reading) = first
        .deposited(
            &[sample(Rat::one(), ints([6, 0, 3, 9]), covector())],
            &Rat::one(),
            &rule,
            &mut BudgetedCarry::new(lattice, 2),
        )
        .unwrap();
    let reading = reading.unwrap();
    let (chart, before, after) = (first.solved(), first.gram(), second.gram());
    let moved = after.subtract(&before).unwrap();
    let plain = left_residual(&chart, &after);
    assert_eq!(
        plain,
        left_residual(&chart, &before)
            .subtract(&chart.multiply(&moved).unwrap())
            .unwrap()
    );
    let delta = first.chart().certificate();
    assert!(row_norm(&plain) <= delta + row_norm(&moved) * row_norm(&chart));
    assert!(row_norm(&plain) > Rat::one());
    let warm = reading.warm.unwrap();
    assert!(warm < rat(1, 4), "the warm start's certificate {warm}");
    assert!(!reading.cold);
    assert!(reading.certificate <= rule.target());
    assert_eq!(
        row_norm(&left_residual(&second.solved(), &after)),
        reading.certificate
    );
}

/// Lean `HNN/LatticeWord.{newton_schulz_left, rounded_refinement_certificate_left}`: one
/// refinement `X' = (2 − XH)X` squares the left residual exactly, `1 − X'H = (1 − XH)²`; on a lattice
/// fine enough to hold it the executed refinement is that `X'` with certificate `‖R²‖∞ ≤ δ²`, and on a
/// coarse one its certificate stays within `δ² + 2n·2^(−L)‖H‖∞` (the chart rule's rounding bound).
#[test]
fn a_rounded_refinement_squares_the_residual() {
    let gram = ExactRatMatrix::shaped(
        3,
        3,
        vec![
            vec![integer(3), integer(1), Rat::zero()],
            vec![integer(1), integer(4), rat(1, 2)],
            vec![Rat::zero(), rat(1, 2), integer(2)],
        ],
    )
    .unwrap();
    let coarse = Lattice::new(3);
    let chart = ExactRatMatrix::shaped(
        3,
        3,
        gram.inverse()
            .unwrap()
            .to_rows()
            .iter()
            .map(|row| {
                row.iter()
                    .map(|x| Rat::from_integer(coarse.div_rem(x).0) * coarse.unit())
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let residual = left_residual(&chart, &gram);
    let delta = row_norm(&residual);
    assert!(delta > Rat::zero() && delta < rat(1, 2));
    let two = ExactRatMatrix::identity(3).unwrap().scaled(&integer(2));
    let exact = two
        .subtract(&chart.multiply(&gram).unwrap())
        .unwrap()
        .multiply(&chart)
        .unwrap();
    let squared = residual.multiply(&residual).unwrap();
    assert_eq!(left_residual(&exact, &gram), squared);
    let rows = gram.to_rows();
    // Fine enough: the executed refinement is the exact one.
    let (refined, before, after) = refined_once(&chart.to_rows(), 20, &rows).unwrap();
    assert_eq!(before, delta);
    assert_eq!(ExactRatMatrix::shaped(3, 3, refined).unwrap(), exact);
    assert_eq!(after, row_norm(&squared));
    assert!(after <= &delta * &delta);
    // Coarse: the rounding enters, within the rule's bound.
    let (refined, _, after) = refined_once(&chart.to_rows(), 6, &rows).unwrap();
    let executed = ExactRatMatrix::shaped(3, 3, refined).unwrap();
    assert_eq!(after, row_norm(&left_residual(&executed, &gram)));
    let rounding = integer(6) * Lattice::new(6).unit() * row_norm(&gram);
    assert!(after <= &delta * &delta + rounding && after < delta);
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
                // Every normal law's solved chart is certified against its carried Gram, below its
                // locus's target, and symmetric.
                for (locus, law) in solved_laws(&after, field.rings().len()) {
                    let chart = law.solved();
                    let delta = law.chart().certificate();
                    assert_eq!(&row_norm(&left_residual(&chart, &law.gram())), delta);
                    assert!(*delta <= after.chart_rule(locus).unwrap().target());
                    assert_eq!(chart, chart.transpose().unwrap());
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
        (Locus::ReceivingMap(g), Carrier::Target) => ring(g).target().unwrap().entries().to_vec(),
        (Locus::ReceivingMap(g), Carrier::Harmonic) => theta.harmonic(g).unwrap().to_vec(),
        (Locus::ReceivingMap(g), Carrier::HarmonicScale) => {
            vec![theta.harmonic_scale(g).unwrap().clone()]
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
/// the factor steps, recomputed): `ΔH = Σ w f fᵀ`, `ΔW = γ Σ w g (X̂f)ᵀ` at the successor's solved
/// chart `X̂`, `Δh_x = Σ w|f|²` and `Δx = (η_x / h_x') G_x` at the successor's statistic; at the
/// receiving map (Decision 26) `ΔB = Σ w χ fᵀ` and `ΔW = Σ w (χ − W f)(X̂f)ᵀ` at the predecessor's
/// map, and the harmonic step `Δh_R = (η_x / h_x') Π Rᵀ Σ w g`.
fn updates(
    deposit: &Deposit,
    before: &Constitution,
    next: &Constitution,
) -> Vec<((Locus, Carrier), Vec<Rat>)> {
    let steps = next.steps();
    let mut out = Vec::new();
    for step in deposit.linear() {
        let locus = step.locus.locus();
        let (law, was) = match step.locus {
            LinearLocus::SourcePort(g) => {
                (next.source_law(g).unwrap(), before.source_law(g).unwrap())
            }
            LinearLocus::Contrast(g) => (next.contrast_law(g), before.contrast_law(g)),
            LinearLocus::Receiving(g) => (
                next.receiving_law(g).unwrap(),
                before.receiving_law(g).unwrap(),
            ),
        };
        let (m, n) = (law.map().rows(), law.map().columns());
        let solved = law.solved();
        let (mut gram, mut map) = (vec![Rat::zero(); n * n], vec![Rat::zero(); m * n]);
        let mut target = vec![Rat::zero(); m * n];
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
            // The row covector: the proxy step's `γ g`, or the exogenous residual `χ − W f`.
            let row: Vec<Rat> = match &s.target {
                Some(face) => (0..m)
                    .map(|i| {
                        let read: Rat = (0..n)
                            .map(|j| was.map().get(i, j).unwrap() * &s.feature[j])
                            .sum();
                        &face[i] - read
                    })
                    .collect(),
                None => s.covector.iter().map(|g| &steps.proxy * g).collect(),
            };
            for i in 0..m {
                for j in 0..n {
                    map[i * n + j] += &s.weight * &row[i] * &reach[j];
                    if let Some(face) = &s.target {
                        target[i * n + j] += &s.weight * &face[i] * &s.feature[j];
                    }
                }
            }
        }
        out.push(((locus, Carrier::Gram), gram));
        out.push(((locus, Carrier::Map), map));
        if law.is_exogenous() {
            out.push(((locus, Carrier::Target), target));
        }
    }
    for step in deposit.harmonic() {
        let locus = Locus::ReceivingMap(step.ring);
        let rate = &steps.factor / next.harmonic_scale(step.ring).unwrap();
        out.push(((locus, Carrier::HarmonicScale), vec![step.energy.clone()]));
        out.push((
            (locus, Carrier::Harmonic),
            step.gradient.iter().map(|x| &rate * x).collect(),
        ));
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
    for (before, deposit, next, reading) in run {
        for (array, values) in updates(deposit, before, next) {
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
    for (before, deposit, next, _) in run {
        for ((locus, carrier), values) in updates(deposit, before, next) {
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
    let (_, deposit) = compose(&field, &theta, &pending, &back, &targets).unwrap();
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

/// A target face on `m` realified rows: the margin `margin` at row `2·class` (Decision 26).
fn face(m: usize, class: usize, margin: i64) -> Vec<Rat> {
    let mut face = vec![Rat::zero(); m];
    face[2 * class] = integer(margin);
    face
}

/// An exogenous sample: a weight, a feature, a zero covector (the law does not read it) and a face.
fn exogenous(weight: Rat, feature: Vec<Rat>, target: Vec<Rat>) -> Sample {
    Sample {
        weight,
        covector: vec![Rat::zero(); target.len()],
        feature,
        target: Some(target),
    }
}

/// `Σ w l rᵀ` over samples, with `l` read off each sample.
fn outer_sum(samples: &[Sample], left: impl Fn(&Sample) -> Vec<Rat>) -> ExactRatMatrix {
    let (rows, columns) = (left(&samples[0]).len(), samples[0].feature.len());
    let mut sum = ExactRatMatrix::zero(rows, columns).unwrap();
    for s in samples {
        let l = left(s);
        let outer = ExactRatMatrix::shaped(
            rows,
            columns,
            l.iter()
                .map(|x| s.feature.iter().map(|y| &s.weight * x * y).collect())
                .collect(),
        )
        .unwrap();
        sum = sum.add(&outer).unwrap();
    }
    sum
}

/// Decision 26 (`exogenous_normal_step`, `exogenous_chart_residual`): at the exogenous law, over
/// three deposits (clocks 1, 2, 3) with remainders on every carrier, the carried Gram moves by
/// exactly `F = Σ w f fᵀ`, the target statistic by `T = Σ w χ fᵀ`, and the map by
/// `(T − W F) X̂` at the predecessor's map and the executed chart, each less its released residuals
/// (value plus remainder); the chart term `(T − WF)(1 − X̂H')` lies within the reading's released
/// bound; the reading's statistic is `‖W'H' − B'‖∞` of the published law and its prior weight the
/// chart's mean diagonal `tr(X̂)/n`. From `WH = B` (the founding, and features and faces on the lattice, so `H` and
/// `B` carry nothing) the step's statistic residual is exactly `W'H' − B' = −(T − WF)(1 − X̂H')` at
/// the exact map. A prox law refuses a target face, and the exogenous law a sample without one.
#[test]
fn the_exogenous_step_keeps_its_statistic_up_to_the_chart_term() {
    let (m, n) = (4, 3);
    let mut draw = Draw::new(43);
    let lattice = Lattice::new(4);
    let rule = rule(lattice);
    let prior = draw.half_matrix(m, n);
    let mut law = NormalLaw::exogenous(prior.clone());
    assert!(law.is_exogenous());
    assert_eq!(law.target().unwrap(), prior);
    let carried = |law: &NormalLaw| -> [ExactRatMatrix; 3] {
        [
            law.map().add(&law.map_remainder()).unwrap(),
            law.gram().add(&law.gram_remainder()).unwrap(),
            law.target()
                .unwrap()
                .add(&law.target_remainder().unwrap())
                .unwrap(),
        ]
    };
    for clock in 1..=3 {
        let samples: Vec<Sample> = (0..2)
            .map(|t| {
                exogenous(
                    draw.rational().abs() + Rat::one(),
                    draw.vector(n),
                    face(m, (clock as usize + t) % (m / 2), 7),
                )
            })
            .collect();
        let mut at = BudgetedCarry::new(lattice, clock);
        let (next, reading) = law
            .deposited(&samples, &Rat::one(), &rule, &mut at)
            .unwrap();
        let reading = reading.unwrap();
        let released = |carrier: Carrier, rows: usize, columns: usize| {
            let mut dense = vec![vec![Rat::zero(); columns]; rows];
            for (c, entry, e) in at.released() {
                if c == carrier {
                    dense[entry / columns][entry % columns] = e;
                }
            }
            ExactRatMatrix::shaped(rows, columns, dense).unwrap()
        };
        let moved = |before: &ExactRatMatrix, after: &ExactRatMatrix, carrier: Carrier| {
            after
                .subtract(before)
                .unwrap()
                .add(&released(carrier, before.rows(), before.columns()))
                .unwrap()
        };
        let [map, gram, target] = carried(&law);
        let [next_map, next_gram, next_target] = carried(&next);
        let features = outer_sum(&samples, |s| s.feature.clone());
        let faces = outer_sum(&samples, |s| s.target.clone().unwrap());
        assert_eq!(moved(&gram, &next_gram, Carrier::Gram), features);
        assert_eq!(moved(&target, &next_target, Carrier::Target), faces);
        let chart = next.solved();
        let driven = faces
            .subtract(&law.map().multiply(&features).unwrap())
            .unwrap();
        assert_eq!(
            moved(&map, &next_map, Carrier::Map),
            driven.multiply(&chart).unwrap()
        );
        let term = driven
            .multiply(&left_residual(&chart, &next.gram()))
            .unwrap();
        assert!(row_norm(&term) <= reading.released);
        let receipt = reading.exogenous.clone().unwrap();
        let statistic = next
            .map()
            .multiply(&next.gram())
            .unwrap()
            .subtract(&next.target().unwrap())
            .unwrap();
        assert_eq!(receipt.statistic, row_norm(&statistic));
        assert_eq!(receipt.statistic, next.statistic_residual());
        let trace: Rat = (0..n).map(|i| chart.get(i, i).unwrap().clone()).sum();
        assert_eq!(receipt.prior, trace / integer(n as i64));
        assert!(next.map().entries().iter().all(|x| lattice.contains(x)));
        law = next;
    }
    // From WH = B, with every feature and face on the lattice.
    let founding = NormalLaw::exogenous(prior);
    let samples: Vec<Sample> = (0..2)
        .map(|t| exogenous(integer(1 + t as i64), draw.dyadic_vector(n), face(m, t, 7)))
        .collect();
    let mut at = BudgetedCarry::new(lattice, 1);
    let (next, _) = founding
        .deposited(&samples, &Rat::one(), &rule, &mut at)
        .unwrap();
    assert!(next.gram_remainder().entries().iter().all(Zero::is_zero));
    assert!(
        next.target_remainder()
            .unwrap()
            .entries()
            .iter()
            .all(Zero::is_zero)
    );
    let features = outer_sum(&samples, |s| s.feature.clone());
    let faces = outer_sum(&samples, |s| s.target.clone().unwrap());
    let chart = next.solved();
    let driven = faces
        .subtract(&founding.map().multiply(&features).unwrap())
        .unwrap();
    let exact = founding
        .map()
        .add(&driven.multiply(&chart).unwrap())
        .unwrap();
    assert_eq!(
        exact
            .multiply(&next.gram())
            .unwrap()
            .subtract(&next.target().unwrap())
            .unwrap(),
        driven
            .multiply(&left_residual(&chart, &next.gram()))
            .unwrap()
            .scaled(&-Rat::one())
    );
    // The laws refuse the other's samples.
    let mut at = BudgetedCarry::new(lattice, 1);
    let prox = NormalLaw::with_prior(ExactRatMatrix::zero(m, n).unwrap());
    assert!(
        prox.deposited(&samples, &Rat::one(), &rule, &mut at)
            .is_err()
    );
    let bare = sample(Rat::one(), draw.vector(n), vec![Rat::zero(); m]);
    assert!(
        founding
            .deposited(&[bare], &Rat::one(), &rule, &mut at)
            .is_err()
    );
}

/// Decision 26 (`prior_weight_identity`), on a one-dimensional fixture: from the declared prior
/// `W_0 = 1/2` (`H_0 = 1`, `B_0 = W_0 H_0`), features `f = 1` with weights 1, 2, 4 carry the Gram to
/// 2, 4, 8, whose charts are exact; the map is `W_n = W_0 H_0 H_n⁻¹ + T_n H_n⁻¹` exactly at every
/// deposit, so the prior's weight is `1/H_n = 1/(1 + λ)` (`λ = Σ w f²`), which the reading reports,
/// and the statistic `WH = B` holds exactly.
#[test]
fn the_prior_weight_decays_as_the_inverse_gram() {
    let lattice = Lattice::new(10);
    let rule = rule(lattice);
    let prior = rat(1, 2);
    let mut law =
        NormalLaw::exogenous(ExactRatMatrix::shaped(1, 1, vec![vec![prior.clone()]]).unwrap());
    let mut target = Rat::zero();
    for (clock, (weight, face)) in [(1i64, 3i64), (2, -1), (4, 5)].into_iter().enumerate() {
        let samples = vec![exogenous(
            integer(weight),
            vec![Rat::one()],
            vec![integer(face)],
        )];
        let mut at = BudgetedCarry::new(lattice, clock as u64 + 1);
        let (next, reading) = law
            .deposited(&samples, &Rat::one(), &rule, &mut at)
            .unwrap();
        let receipt = reading.unwrap().exogenous.unwrap();
        target += integer(weight * face);
        let gram = next.gram().get(0, 0).unwrap().clone();
        assert_eq!(next.chart().certificate(), &Rat::zero());
        assert_eq!(next.solved().get(0, 0).unwrap(), &gram.recip());
        assert_eq!(next.map().get(0, 0).unwrap(), &((&prior + &target) / &gram));
        assert_eq!(receipt.prior, gram.recip());
        assert_eq!(receipt.statistic, Rat::zero());
        assert!(at.released().is_empty());
        law = next;
    }
    assert_eq!(law.gram().get(0, 0).unwrap(), &integer(8));
    assert_eq!(law.map().get(0, 0).unwrap(), &rat(43, 16));
}

/// Decision 26 at the receiving locus over the chain's deposits: `R`'s law is exogenous, each
/// sample carries its target's code face at the receiver's margin, and the deposit's reading reports
/// its receipt exactly when the window's features reached the locus; the bound harmonic coordinate stays in the fixed space of the ring's rotation after
/// every deposit, moves only by the deposit's harmonic step, and moves.
#[test]
fn the_receiving_locus_regresses_the_code_face_and_moves_its_standing() {
    let run = chain_run();
    let field = chain();
    let ring = field.ring(2);
    let margin = field.margins()[0];
    let (mut moved, mut receipts) = (false, 0);
    for (before, deposit, after, reading) in run {
        assert!(after.receiving_law(2).unwrap().is_exogenous());
        let receiving = deposit
            .linear()
            .iter()
            .find(|step| step.locus == LinearLocus::Receiving(2))
            .unwrap();
        for sample in &receiving.samples {
            let face = sample.target.as_ref().unwrap();
            let classes: Vec<usize> = (0..face.len()).filter(|&i| !face[i].is_zero()).collect();
            assert_eq!(classes.len(), 1);
            assert_eq!(classes[0] % 2, 0);
            assert_eq!(face[classes[0]], Rat::from_integer(BigInt::from(margin)));
        }
        let reached = receiving
            .samples
            .iter()
            .any(|sample| sample.feature.iter().any(|x| !x.is_zero()));
        assert_eq!(
            reading.charts.iter().any(|(locus, chart)| {
                *locus == Locus::ReceivingMap(2) && chart.exogenous.is_some()
            }),
            reached
        );
        receipts += usize::from(reached);
        assert!(
            reading
                .charts
                .iter()
                .filter(|(locus, _)| *locus != Locus::ReceivingMap(2))
                .all(|(_, chart)| chart.exogenous.is_none())
        );
        let (was, now) = (before.harmonic(2).unwrap(), after.harmonic(2).unwrap());
        assert!(ring.is_harmonic(now));
        for step in deposit.harmonic() {
            assert!(ring.is_harmonic(&step.gradient));
        }
        if deposit.harmonic().is_empty() {
            assert_eq!(was, now);
        }
        moved |= was != now;
    }
    assert!(moved && receipts > 0);
}
