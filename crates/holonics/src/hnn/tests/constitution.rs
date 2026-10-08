//! Deposition, per locus: the prox step through the solved chart and its released residual, the
//! chart's certificate, warm start and refinement, the statistic's standing, the budgeted carry (its
//! accounting, its bound since the founding, remainder bits, the carried Gram's positivity and the
//! zero update), the squares' positivity with no clamp, the energy growth of reaction deposits,
//! the budget's refusal, the standing's lock chart, what reaches a locus inside its causal diamond,
//! the declared initial constitution, and the refusal of a complex-bilinear block at declaration.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{OPEN_BUDGET, chain, chain_reach, generic, moment, phases, six_path};
use crate::hnn::tests::support::encoded;
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::{
    BudgetedCarry, Carrier, ChartRule, Constitution, DepositReading, FactorGradient, FactorStep,
    Family, Lattice, LinearLocus, LinearStep, Locus, NormalLaw, Sample, declared_sign,
    gamma_length, refined_once,
};
use crate::hnn::field::{ConstitutionRead, Current};
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{Deposit, ExecutionPort};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::receiving::ActiveAddress;
use crate::hnn::reference::{Reference, compose};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::inertia;
use crate::ratio::linear::vector::matrix_form;
use crate::ratio::{Rat, integer, rat};

fn sample(weight: Rat, feature: Vec<Rat>, covector: Vec<Rat>) -> Sample {
    Sample {
        weight,
        feature,
        covector,
        masses: None,
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
/// released prox residual `ρ = γG(1 − X̂H')`, whose norm is within the reading's certificate; the
/// published successors satisfy the deposition's one balance
/// `W′H′ − (WH + WF + γG) = −ρ + W c_H + c_W H′` with each carry term `c = r − r′ − e`
/// (`HNN/LatticeWord.carried_deposition_balance`); every
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
        // The deposition's one balance on the published map and Gram (Lean
        // `HNN/LatticeWord.carried_deposition_balance`): `W′H′ − (WH + WF + γG) = −ρ + W c_H + c_W H′`,
        // each carry term `c = r − r′ − e`.
        let gram_carry = law
            .gram_remainder()
            .subtract(&next.gram_remainder())
            .unwrap()
            .subtract(&released(Carrier::Gram, 4, 4))
            .unwrap();
        let map_carry = law
            .map_remainder()
            .subtract(&next.map_remainder())
            .unwrap()
            .subtract(&released(Carrier::Map, 3, 4))
            .unwrap();
        assert_eq!(
            next.map()
                .multiply(&next.gram())
                .unwrap()
                .subtract(
                    &law.map()
                        .multiply(&law.gram())
                        .unwrap()
                        .add(&law.map().multiply(&gram_update).unwrap())
                        .unwrap()
                        .add(&gradient.scaled(&proxy))
                        .unwrap()
                )
                .unwrap(),
            law.map()
                .multiply(&gram_carry)
                .unwrap()
                .add(&map_carry.multiply(&next.gram()).unwrap())
                .unwrap()
                .subtract(&rho)
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

/// **The founding's standing wave scaled `depth` times deeper into its lobes** (a test chart, never
/// a law): the carry's laws are exercised on the standing, whose unit moves then keep every lobe
/// (module header of `hnn::constitution`, "Within a lobe").
fn deep(theta: Constitution, depth: i64) -> Constitution {
    let rings = theta.standing_contrasts().len();
    (0..rings).fold(theta, |theta, g| {
        let scaled = theta
            .standing(g)
            .iter()
            .map(|x| x * integer(depth))
            .collect();
        theta.with_ports(g, Some(scaled), None, None).unwrap()
    })
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
    let theta = deep(Constitution::initial(&field, OPEN_BUDGET).unwrap(), 256);
    let lattice = theta.lattice(Locus::Standing(1)).unwrap();
    let (u, n) = (lattice.unit(), field.ring(1).width());
    // At `R = 0` no gain reaches the stations, so the certified step is the covector bound's: at a
    // covector scale `c = 1` it is `η = 1`, and with no feature energy `h_x = 1`, so a gradient `Δ`
    // applies the update `Δ`.
    let standing = |commit: u64, updates: Vec<Rat>| {
        Deposit::new(
            commit,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing {
                    ring: 1,
                    gradient: updates,
                    reach: vec![(1, Rat::zero())],
                },
                energy: Rat::zero(),
                covector: Rat::one(),
            }],
            Vec::new(),
        )
        .with_reach(chain_reach())
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

/// Lean `HNN/LatticeDeposit.{quot_fine_eq_floor, step_coordinate_eq_floor}` at the carry's two
/// splits: [`Lattice::div_rem`] at the fine lattice `2^(−L−k)ℤ`, then
/// [`Lattice::div_rem_coordinate`] at `2^(−L)ℤ`, give `q = ⌊y·2^L + 1/2 + 2^(−k−1)⌋` for `k ≥ 1`.
/// The values `y = n/(3·2^(L+k+1))` cross four cells on each side of zero. They include every cell
/// boundary `(z − 1/2)·2^(−L) − 2^(−L−k−1)` (`n` a multiple of three) and rationals off every
/// dyadic lattice.
#[test]
fn the_two_splits_compose_into_one_floor() {
    for exponent in [0, 3] {
        for finer in [1, 3, 5] {
            let (lattice, fine) = (Lattice::new(exponent), Lattice::new(exponent + finer));
            let shift = rat(1, 2) + Rat::new(BigInt::one(), BigInt::one() << (finer + 1) as usize);
            let reach = 3_i64 << (finer + 3);
            for n in -reach..=reach {
                let y = Rat::new(
                    BigInt::from(n),
                    BigInt::from(3) << (exponent + finer + 1) as usize,
                );
                let (point, _) = fine.div_rem(&y);
                let (quotient, _) = lattice.div_rem_coordinate(&point, finer);
                let floor = (&y / lattice.unit() + &shift).floor().to_integer();
                assert_eq!(quotient, floor, "L = {exponent}, k = {finer}, y = {y}");
            }
        }
    }
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

/// `cI`, the scaled identity of width `n`.
fn scaled_identity(n: usize, c: Rat) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        n,
        n,
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| if i == j { c.clone() } else { Rat::zero() })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

/// The receiving map's scaled prior (`NormalLaw::with_scaled_prior`, `SolvedChart::founded`): at
/// `H_0 = 2I` the founding chart is `½I` exactly on `2^(−1)ℤ` (`δ = 0`), and `k = 0` is the unit
/// prior. Over two deposits, the second reaching coordinates the first did not and one coordinate
/// never reached, the carried Gram is `2I + Σ f fᵀ` exactly; the chart is `½` on the diagonal off
/// its support; the warm start carries the newly reached coordinates in at the prior's chart, so it
/// needs no restart (entering them at `1` would leave the residual `1 − 2 = −1` there, outside the
/// contraction); and each executed certificate is the exact `‖1 − X̂H'‖∞` of the dense chart.
#[test]
fn a_scaled_prior_carries_its_chart_off_the_support() {
    let lattice = Lattice::new(4);
    let rule = rule(lattice);
    let n = 5;
    assert_eq!(
        NormalLaw::with_scaled_prior(ExactRatMatrix::zero(2, n).unwrap(), 0),
        NormalLaw::with_prior(ExactRatMatrix::zero(2, n).unwrap())
    );
    let mut law = NormalLaw::with_scaled_prior(ExactRatMatrix::zero(2, n).unwrap(), 1);
    assert_eq!(law.gram(), scaled_identity(n, integer(2)));
    assert_eq!(law.solved(), scaled_identity(n, rat(1, 2)));
    assert_eq!(
        (law.chart().scale(), law.chart().exponent()),
        (1, 1)
    );
    assert!(law.chart().certificate().is_zero());
    let ints = |values: [i64; 5]| values.iter().map(|x| integer(*x)).collect::<Vec<Rat>>();
    let covector = || vec![rat(1, 3), rat(-1, 2)];
    let mut exact = scaled_identity(n, integer(2));
    for (clock, features) in [
        (1, vec![ints([1, 2, 0, 0, 0]), ints([0, 1, 0, 0, 0])]),
        (2, vec![ints([3, 0, 2, 1, 0])]),
    ] {
        let samples: Vec<Sample> = features
            .iter()
            .map(|f| sample(Rat::one(), f.clone(), covector()))
            .collect();
        let (next, reading) = law
            .deposited(
                &samples,
                &Rat::one(),
                &rule,
                &mut BudgetedCarry::new(lattice, clock),
            )
            .unwrap();
        let reading = reading.unwrap();
        for f in &features {
            let f = ExactRatMatrix::shaped(n, 1, f.iter().map(|x| vec![x.clone()]).collect())
                .unwrap();
            exact = exact
                .add(&f.multiply(&f.transpose().unwrap()).unwrap())
                .unwrap();
        }
        assert_eq!(next.gram(), exact);
        assert_eq!(next.chart().scale(), 1);
        let chart = next.solved();
        let support = next.chart().support().to_vec();
        for i in (0..n).filter(|i| !support.contains(i)) {
            for j in 0..n {
                let expected = if i == j { rat(1, 2) } else { Rat::zero() };
                assert_eq!(chart.get(i, j).unwrap(), &expected, "({i}, {j})");
            }
        }
        assert!(!support.contains(&4));
        assert!(!reading.cold, "deposit {clock} restarted");
        assert!(reading.warm.as_ref().is_some_and(|warm| *warm < rat(1, 4)));
        assert!(reading.certificate <= rule.target());
        assert_eq!(row_norm(&left_residual(&chart, &exact)), reading.certificate);
        law = next;
    }
    assert_eq!(law.chart().support(), &[0, 1, 2, 3]);
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
        let field = super::learning::chain_two();
        let reference = Reference::new(8, OPEN_BUDGET);
        let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
        let (moment_id, _) = reference
            .ingest(&mut resident, None, &encoded(&field, &[1, 0, 1, 0, 0]))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let targets = [[0usize, 1], [0, 1], [1, 1], [1, 0], [0, 0], [0, 0], [1, 1]];
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
                        &encoded(&field, &targets[k % targets.len()]),
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
/// the factor steps, recomputed): `ΔH = Σ w f fᵀ`, `ΔW = η Σ w g (X̂f)ᵀ` at the successor's solved
/// chart `X̂` and the locus's certified step `η` (zero where none was certified), `Δh_x = Σ w|f|²`
/// and `Δx = (η_x / h_x') G_x` at the successor's statistic and the family's certified step `η_x`.
///
/// Where the deposit moved a receiving prior from `2^k` to `2^(k′)` (`ChartReading::prior`), that
/// move is one more update of the receiving law, after its step: `(2^(k′) − 2^k) I` on the Gram, and
/// `(x − 1)(W_s + r_s)` on the map, `x = 2^(k − k′)`, with `W_s + r_s` the stepped map's value
/// (the prior carry's design §3). The step itself is read at the stepped successor's chart, the
/// one it was taken at, from the same deposit on the predecessor without its prior pairs
/// (`Constitution::without_prior_pairs`).
fn updates(
    before: &Constitution,
    deposit: &Deposit,
    next: &Constitution,
    reading: &DepositReading,
) -> Vec<((Locus, Carrier), Vec<Rat>)> {
    let moves: Vec<(Locus, u32, u32)> = reading
        .charts
        .iter()
        .filter_map(|(locus, chart)| chart.prior.as_ref().map(|prior| (*locus, prior)))
        .filter(|(_, prior)| prior.to != prior.from)
        .map(|(locus, prior)| (locus, prior.from, prior.to))
        .collect();
    let stepped = (!moves.is_empty()).then(|| {
        before
            .without_prior_pairs()
            .deposited(deposit)
            .expect("the step deposits without its prior pairs")
            .0
    });
    let next = stepped.as_ref().unwrap_or(next);
    let mut out = updates_at(deposit, next, reading);
    for (locus, from, to) in moves {
        let Locus::ReceivingMap(g) = locus else {
            panic!("a prior moved off a receiving map: {locus:?}")
        };
        let law = next.receiving_law(g).unwrap();
        let power = |e: u32| Rat::from_integer(BigInt::one() << e as usize);
        let n = law.gram().rows();
        let shift = power(to) - power(from);
        let gram: Vec<Rat> = (0..n * n)
            .map(|i| if i % (n + 1) == 0 { shift.clone() } else { Rat::zero() })
            .collect();
        let x = power(from) / power(to);
        let carried = remainders(next);
        let map: Vec<Rat> = law
            .map()
            .entries()
            .iter()
            .enumerate()
            .map(|(i, w)| {
                let r = carried
                    .get(&(locus, Carrier::Map, i))
                    .cloned()
                    .unwrap_or_else(Rat::zero);
                (&x - Rat::one()) * (w + r)
            })
            .collect();
        out.push(((locus, Carrier::Gram), gram));
        out.push(((locus, Carrier::Map), map));
    }
    out
}

/// [`updates`] at one successor, every step read at its chart.
fn updates_at(
    deposit: &Deposit,
    next: &Constitution,
    reading: &DepositReading,
) -> Vec<((Locus, Carrier), Vec<Rat>)> {
    let mut out = Vec::new();
    for step in deposit.linear() {
        let locus = step.locus.locus();
        let certified = reading.linear_step(locus);
        let law = match step.locus {
            LinearLocus::SourcePort(g) => next.source_law(g).unwrap(),
            LinearLocus::Contrast(g) => next.contrast_law(g),
            LinearLocus::Receiving(g) => next.receiving_law(g).unwrap(),
        };
        let (m, n) = (law.map().rows(), law.map().columns());
        let solved = law.solved();
        // The receiving map's covectors pass through its class metric (the constitution's law).
        let metric = match step.locus {
            LinearLocus::Receiving(_) => {
                crate::hnn::constitution::receiving_class_metric(&step.samples)
            }
            _ => None,
        };
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
                    let covector = match (&metric, i % 2) {
                        (Some(scale), 0) => &s.covector[i] * scale,
                        _ => s.covector[i].clone(),
                    };
                    map[i * n + j] += &certified * &s.weight * covector * &reach[j];
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
            FactorGradient::Standing { ring, gradient, .. } => (
                Carrier::StandingScale,
                next.ring_scales(*ring)[0].clone(),
                vec![(Carrier::Standing, gradient.clone())],
            ),
            FactorGradient::Resonator {
                ring,
                family,
                gradient,
            } => (
                Carrier::ResonatorScale(*family),
                next.resonator_scales(*ring).unwrap()[*family].clone(),
                vec![(Carrier::Resonator(*family), vec![gradient.clone()])],
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
        let rate = reading.family_step(locus, step.gradient.family()) / index;
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
        for (array, values) in updates(before, deposit, next, reading) {
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
    // The chain's receiving prior is located (from `2^0`) and moves on this run, so the ledger
    // reads a move's updates as well as the steps'.
    assert!(run.iter().any(|(.., reading)| {
        reading
            .charts
            .iter()
            .any(|(_, chart)| chart.prior.as_ref().is_some_and(|prior| prior.to != prior.from))
    }));
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
    // The adversary: ring 0's standing at `R = 0`, so its certified step is the covector bound's,
    // `η = 1` at `c = 1`, and `h_x = 1` (no energy): each update just under half a fine unit of the
    // clock it advances to.
    let field = chain();
    let mut theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let founded = theta.standing(0).to_vec();
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
                    gradient: vec![update.clone(); n],
                    reach: vec![(0, Rat::zero())],
                },
                energy: Rat::zero(),
                covector: Rat::one(),
            }],
            Vec::new(),
        )
        .with_reach(chain_reach());
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
    // The founding's standing: the lattice never moved.
    assert_eq!(theta.standing(0), founded.as_slice());
    assert!(theta.carried_remainders().is_empty());
}

/// Lean `HNN/LatticeDeposit.{carried_gram_posDef, carried_gram_posDef_rule}`: after every chain
/// deposit each carried Gram `H` of width `n` is within one unit of the exact Gram (its prior in
/// force, `2^k I` with `k ≥ 0` and every move's shift, plus every statistic that reached it), which
/// is `⪰ I`; `H − (1 − n·u) I` has no negative
/// inertia, and `n·u ≤ 1/(2L_R)`, so `H ⪰ (1 − 1/(2L_R)) I` with no clamp.
#[test]
fn the_carried_gram_stays_positive_definite() {
    let run = chain_run();
    let grain = integer(16);
    let mut exact: BTreeMap<Locus, Vec<Rat>> = BTreeMap::new();
    let mut checked = 0;
    for (before, deposit, next, reading) in run {
        for ((locus, carrier), values) in updates(before, deposit, next, reading) {
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
        for (locus, carrier, _, r) in theta.carried_remainders() {
            if matches!(carrier, Carrier::Factor(_) | Carrier::FactorScale(_)) {
                // These physical coordinates now retain exact unresolved material. Their
                // rational bits are charged directly, not bounded by the old gamma-grid theorem.
                bound += r.numer().bits() + r.denom().bits();
                continue;
            }
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
        assert!(theta.exact_bits() <= theta.budget());
    }
}

/// Actual C/K/D material and normalization share exact coarse accumulation. A later opposite
/// contribution cancels the same contemporary remainder; no finite future or tolerance kernel
/// is assumed, and the other carriers retain their separately declared gamma law.
#[test]
fn unresolved_contact_direction_and_normalization_accumulate_without_release() {
    use crate::hnn::constitution::Carry;
    let lattice = Lattice::new(15);
    let tiny = Rat::new(BigInt::one(), BigInt::from(3) << 31usize);
    for carrier in [Carrier::Factor(0), Carrier::Factor(1), Carrier::Factor(2),
        Carrier::FactorScale(0), Carrier::FactorScale(1), Carrier::FactorScale(2)] {
        let mut carry = Carry::default();
        let mut value = vec![Rat::zero(); 2];
        let mut exact = vec![Rat::zero(); 2];
        for (m,update) in [vec![tiny.clone(), -&tiny],
            vec![&tiny / integer(7), &tiny / integer(11)],
            vec![-&tiny, tiny.clone()]].into_iter().enumerate() {
            let mut at = BudgetedCarry::new(lattice,m as u64+1);
            carry.deposit_all(&mut at,carrier,&mut value,&update);
            assert!(at.released().is_empty());
            for i in 0..2 {
                exact[i] += &update[i];
                assert_eq!(&value[i] + carry.at(i),exact[i]);
                let r=carry.at(i);
                assert!(-lattice.unit()/integer(2) <= r && r < lattice.unit()/integer(2));
            }
        }
        assert!(value.iter().all(Rat::is_zero));
        assert_eq!(carry.at(0),&tiny / integer(7));
        assert_eq!(carry.at(1),&tiny / integer(11));
        let mut at=BudgetedCarry::new(lattice,4);
        at.rebase(2,&mut [(&mut carry,&mut value)]).unwrap();
        for i in 0..2 { assert_eq!(&value[i] + carry.at(i),exact[i]); }
        assert!(at.released().is_empty());
    }
}

/// An exact unresolved contact coordinate cannot evade the existing constitution budget.
/// This is a synthetic deposition-law control, not an observed physical teaching or a curriculum.
#[test]
fn unresolved_contact_material_is_refused_atomically_at_the_existing_budget() {
    let field=chain();
    let budget=Constitution::initial(&field,OPEN_BUDGET).unwrap().exact_bits()+1;
    let theta=Constitution::initial(&field,budget).unwrap();
    let before=theta.clone();
    let tiny=Rat::new(BigInt::one(),BigInt::from(3)<<31usize);
    let gradient=theta.contact_storage(0).scaled(&tiny);
    let deposit=Deposit::new(theta.commit(),vec![],vec![FactorStep {
        gradient:FactorGradient::Storage { contact:0,gradient },
        energy:Rat::zero(),covector:Rat::one(),
    }],vec![]).with_reach(chain_reach());
    assert!(matches!(theta.deposited(&deposit),Err(HnnError::ConstitutionBudget { .. })));
    assert_eq!(theta,before);
    assert!(theta.carried_remainders().is_empty());
}

/// Lean `HNN/LatticeDeposit.{carry_zero, carry_entry_zero}`: a deposit whose updates are all zero
/// leaves the constitution but its commit (no clock advances, nothing is released or stepped); a
/// deposit that updates one entry of a locus advances its clock once and leaves every other entry's
/// value and remainder, releasing nothing there.
#[test]
fn a_zero_update_advances_nothing() {
    let field = chain();
    let theta = deep(Constitution::initial(&field, OPEN_BUDGET).unwrap(), 256);
    let n = field.ring(1).width();
    let standing = |commit: u64, gradient: Vec<Rat>| {
        Deposit::new(
            commit,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing {
                    ring: 1,
                    gradient,
                    reach: vec![(1, Rat::zero())],
                },
                energy: Rat::zero(),
                covector: Rat::one(),
            }],
            Vec::new(),
        )
        .with_reach(chain_reach())
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
            covector: Rat::one(),
        },
        FactorStep {
            gradient: FactorGradient::Stiffness {
                contact: 1,
                gradient: big(&mut draw, field.contact(1).width()),
            },
            energy: Rat::zero(),
            covector: Rat::one(),
        },
        FactorStep {
            gradient: FactorGradient::Dissipation {
                contact: 1,
                gradient: big(&mut draw, field.contact(1).width()),
            },
            energy: Rat::zero(),
            covector: Rat::one(),
        },
        FactorStep {
            gradient: FactorGradient::Passive {
                ring: 1,
                gradient: big(&mut draw, field.ring(1).width()),
            },
            energy: Rat::zero(),
            covector: Rat::one(),
        },
    ];
    let deposit = Deposit::new(0, Vec::new(), factors, Vec::new()).with_reach(chain_reach());
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

/// `hnn::constitution`, "The factor families' certified step" and "The tightened certificate" (Lean
/// `Holon/Deposition.{certified_step_descends, factor_unit_step_alignment, square_ray_deriv_bound,
/// joint_move_triangle, joint_step_descends}`): on a generic constitution (its receiving map nonzero,
/// so the comparisons' covectors reach every family), every stepping family, a normal law's and a
/// factor family's alike, holds its own certificate `ηC ≤ a`, `ηc ≤ 1` with `C = ½·κ²·b`, and the
/// families together hold the joint one, `½ (Σ η m)² ≤ Σ η a` with `m² ≥ κ² b`; the factor families
/// step (the declared `η_x` is retired), each moving its entries by exactly `η G_x / h_x′` less what
/// its budgeted carry holds and releases.
#[test]
fn every_family_steps_by_its_certificate() {
    let field = super::learning::chain_two();
    let reference = Reference::new(8, OPEN_BUDGET);
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), generic(&field, 71))
        .unwrap();
    let (moment_id, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &[1, 0, 1, 0, 0]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let targets = [[0usize, 1], [0, 1], [1, 1], [1, 0]];
    let mut factor_families = 0;
    for target in &targets {
        let (pending, _) = reference
            .refine(&mut resident, &moment_id, &phases)
            .unwrap();
        let (staged, compared) = reference
            .compare(&mut resident, pending, &encoded(&field, target))
            .unwrap();
        let deposit = compared.deposit.into_present().unwrap();
        let before = resident.constitution().clone();
        let reading = reference
            .deposit(&mut resident, staged)
            .unwrap()
            .deposit
            .into_present()
            .unwrap();
        // The joint certificate: `½ (Σ η m)² ≤ Σ η a` over every stepping family whose move the
        // realized score reads, `m ≥ √(κ² b)`; a standing held in its lobes moves nothing there
        // (Lean `HNN/Normal.lobe_move_is_null`) and is not in it.
        let joint = reading.joint.clone().expect("families stepped");
        assert!(joint.holds());
        let (mut moved, mut decrease) = (Rat::zero(), Rat::zero());
        for (_, step) in &reading.steps {
            if step.family == Family::Standing {
                continue;
            }
            moved += &step.step.step * &step.bound;
            decrease += &step.step.step * &step.step.alignment;
        }
        assert_eq!(joint.decrease, decrease);
        assert_eq!(joint.curvature, rat(1, 2) * &moved * &moved);
        for (locus, step) in &reading.steps {
            assert!(step.step.holds(), "{locus:?} {:?}", step.family);
            assert!(step.step.alignment.is_positive());
            // Each family's own curvature, `B = 1`, and its move bound at or above `√(κ² b)`.
            assert_eq!(step.step.curvature, rat(1, 2) * &step.gain * &step.moves);
            assert!(&step.bound * &step.bound >= &step.gain * &step.moves);
            if step.family == Family::Map {
                continue;
            }
            factor_families += 1;
            // The standing's move, exactly: its entries plus their remainders and releases move by
            // `η G / h′` at the carried statistic `h′`.
            if let Locus::Standing(g) = *locus {
                let factor = deposit
                    .factors()
                    .iter()
                    .find(|factor| factor.gradient.locus() == *locus)
                    .unwrap();
                let FactorGradient::Standing { gradient, .. } = &factor.gradient else {
                    unreachable!()
                };
                let after = resident.constitution();
                let scale = after.ring_scales(g)[0].clone();
                let remainder = |theta: &Constitution, i: usize| {
                    remainders(theta)
                        .get(&(*locus, Carrier::Standing, i))
                        .cloned()
                        .unwrap_or_else(Rat::zero)
                };
                for (i, dx) in gradient.iter().enumerate() {
                    let released: Rat = reading
                        .released
                        .iter()
                        .filter(|(at, carrier, entry, _)| {
                            (*at, *carrier, *entry) == (*locus, Carrier::Standing, i)
                        })
                        .map(|(.., e)| e.clone())
                        .sum();
                    assert_eq!(
                        &after.standing(g)[i] + remainder(after, i) + released,
                        &before.standing(g)[i]
                            + remainder(&before, i)
                            + &step.step.step * dx / &scale
                    );
                }
            }
        }
    }
    assert!(factor_families > 0);
}

/// A channel family's gain reads its contact's conductance bound, `G_a ≤ Y_a` when `β_a ≥ 0`; a
/// contact whose exponent is negative has none, and a step of its channel is refused
/// (`UncertifiedConductance`), while a step elsewhere is certified.
#[test]
fn a_channel_step_through_an_unbounded_conductance_is_refused() {
    let mut declared = super::learning::chain_declaration(1 << 16);
    declared.contacts[1].exponent = integer(-2);
    let field = crate::hnn::field::Field::declare(declared).unwrap();
    let theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let step = |contact: usize| {
        let k = field.contact(contact).width();
        Deposit::new(
            0,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Storage {
                    contact,
                    gradient: ExactRatMatrix::identity(k).unwrap(),
                },
                energy: Rat::zero(),
                covector: Rat::one(),
            }],
            Vec::new(),
        )
        .with_reach(chain_reach())
    };
    assert_eq!(
        theta.deposited(&step(1)),
        Err(HnnError::UncertifiedConductance { contact: 1 })
    );
    assert!(theta.deposited(&step(0)).is_ok());
}

/// Lean `Holon/Deposition.committed_energy_bound` at the commit: a rank-one storage `C = e₀e₀ᵀ`
/// grows outside its range under a certified step that moves its column off `e₀` (at `R = 0` the
/// step is the covector bound's, `η = 1`), which no dyadic `ε` of the declared search certifies, so
/// the deposit is refused (`UncertifiedStorage`) and the predecessor is kept; the same step on the
/// full-rank campaign storage `C = I` is certified.
#[test]
fn a_storage_growth_outside_its_range_is_refused() {
    let field = chain();
    let k = field.contact(0).width();
    let initial = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let e0 = |i: usize| if i == 0 { Rat::one() } else { Rat::zero() };
    let rank_one = initial
        .clone()
        .with_channel(
            0,
            ExactRatMatrix::from_diagonal((0..k).map(e0).collect()).unwrap(),
            initial.contact_stiffness(0).clone(),
            initial.contact_dissipation(0).clone(),
        )
        .unwrap();
    // The storage factor's column 0 moves toward `e₁`.
    let gradient = ExactRatMatrix::shaped(
        k,
        k,
        (0..k)
            .map(|i| {
                (0..k)
                    .map(|j| {
                        if (i, j) == (1, 0) {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let deposit = Deposit::new(
        0,
        Vec::new(),
        vec![FactorStep {
            gradient: FactorGradient::Storage {
                contact: 0,
                gradient,
            },
            energy: Rat::zero(),
            covector: Rat::one(),
        }],
        Vec::new(),
    )
    .with_reach(chain_reach());
    assert_eq!(
        rank_one.deposited(&deposit),
        Err(HnnError::UncertifiedStorage)
    );
    let (_, certified) = initial.deposited(&deposit).unwrap();
    assert!(certified.storage_growth.is_positive());
}

/// Lean `HNN/Normal.reaction_deposit_storage_unchanged`: a deposit of reaction material and ports
/// leaves every storage form (contacts' C/K, unpumped resonators' C/K), so its certified storage
/// growth is `ε_k = 0`; a contact storage deposit (the counterexample, `storage_deposit_does_work`)
/// grows it, and the product since the founding carries it.
#[test]
fn reaction_deposits_have_zero_storage_growth() {
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
            covector: Rat::one(),
        }],
        Vec::new(),
    )
    .with_reach(chain_reach());
    let (_, reading) = theta.deposited(&reaction).unwrap();
    assert_eq!(reading.storage_growth, Rat::zero());
    // A storage deposit at `R = 0`: its certified step is the covector bound's, `η = 1` at `c = 1`,
    // so `c = I` moves by `G/h_x′ = I` and `C = I` grows to `4I`, certified at `ε = 2² ≥ 3`.
    let k = field.contact(0).width();
    let initial = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let storage = Deposit::new(
        0,
        Vec::new(),
        vec![FactorStep {
            gradient: FactorGradient::Storage {
                contact: 0,
                gradient: ExactRatMatrix::identity(k).unwrap(),
            },
            energy: Rat::zero(),
            covector: Rat::one(),
        }],
        Vec::new(),
    )
    .with_reach(chain_reach());
    let (_, grown) = initial.deposited(&storage).unwrap();
    assert_eq!(grown.storage_growth, integer(4));
    assert_eq!(grown.storage_product, Rat::one() + &grown.storage_growth);
}

/// Design (d), the budget and stop rule: a deposit whose successor exceeds `B_Θ` is refused with
/// `ConstitutionBudget`, naming the loci that grew most; the predecessor stays published, and no
/// further deposit is admitted.
#[test]
fn the_budget_refuses_the_successor_and_keeps_the_predecessor() {
    let field = chain();
    let (current, _) = moment(&field, 11, 0);
    // One bit above the declared initial constitution: the first deposit that grows it is refused.
    let budget = Constitution::initial(&field, OPEN_BUDGET)
        .unwrap()
        .exact_bits()
        + 1;
    let reference = Reference::new(8, budget);
    let tight = Constitution::initial(&field, budget).unwrap();
    let mut resident = reference.mount_with(&field, &current, tight).unwrap();
    let before = resident.constitution().clone();
    let (moment_id, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &[1, 2, 3, 0, 2, 1, 3]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let mut refused = None;
    for _ in 0..4 {
        let (pending, _) = reference
            .refine(&mut resident, &moment_id, &phases)
            .unwrap();
        let (staged, _) = reference
            .compare(&mut resident, pending, &encoded(&field, &[2, 1]))
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
        .compare(&mut resident, pending, &encoded(&field, &[0, 0]))
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
    let theta = Constitution::initial(&field, OPEN_BUDGET)
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
                    reach: vec![(2, Rat::zero()), (1, Rat::zero())],
                },
                energy: Rat::zero(),
                covector: Rat::one(),
            }],
            Vec::new(),
        )
        .with_reach(chain_reach())
    };
    // q_2 = 1/8 on every coordinate; ring 2's contrast is U q_1 − q_2 = 3/128 − 1/8 < 0 on its
    // matched coordinates (q_1 founded at 3 units of 2^(−7)). At `R = 0` the certified step is the
    // covector bound's, `η = 1`, so the step moves `q_2` by the gradient. A small step keeps every
    // class and lobe, and is taken whole, offering nothing to the lock.
    let (small, reading) = theta.deposited(&step(rat(1, 16))).unwrap();
    assert_eq!(classes(&small), start);
    assert_ne!(small.standing(2), theta.standing(2));
    assert!(reading.lobe.is_none() && reading.lock.is_none());
    // A step past the node is held in its lobes (every class kept, Lean `lobe_ray_keeps_class`):
    // the lobe halves it until no slice leaves its lobe, and offers the crossings to the lock.
    let (held, reading) = theta.deposited(&step(rat(-1, 2))).unwrap();
    assert_eq!(classes(&held), start);
    let lobe = reading.lobe.expect("the crossing was offered");
    assert!(lobe.offered.iter().any(|&(r, _)| r == 2));
    assert!(lobe.held.iter().any(|&(g, _)| g == 2));
    for (r, (before, after)) in theta
        .standing_contrasts()
        .iter()
        .zip(held.standing_contrasts())
        .enumerate()
    {
        for (rho, (x, y)) in before.iter().zip(&after).enumerate() {
            assert_eq!(x.is_negative(), y.is_negative(), "({r}, {rho})");
            assert!(x.is_zero() || !y.is_zero(), "({r}, {rho}) reached its node");
        }
    }
    // The lock's proposal turns ring 2's sheets by a half-turn; the constitution takes it only on
    // the successor it was made at, as a commit of its own. The exact comparison decides whether a
    // machine takes it (`holon::deposition::strictly_better`).
    let proposal = reading.lock.expect("the chart's step turns a sheet");
    assert!(proposal.crossings().iter().any(|&(r, _)| r == 2));
    assert!(matches!(
        theta.locked(&proposal),
        Err(HnnError::StaleDeposit { .. })
    ));
    let (turned, lock) = held.locked(&proposal).unwrap();
    assert_eq!(lock.commit, held.commit() + 1);
    assert_eq!(turned.commit(), held.commit() + 1);
    assert_ne!(classes(&turned)[2], start[2]);
    for &(r, rho) in proposal.crossings() {
        assert_ne!(
            held.standing_contrasts()[r][rho].is_negative(),
            turned.standing_contrasts()[r][rho].is_negative()
        );
    }
}

/// **The founding is a standing wave off its nodes** (module header of `hnn::constitution`, "The
/// founding"; Lean `HNN/Normal.{founding_off_node, chain_founding, channel_fixed_node}`): on the
/// chain every slice's contrast sits at its component's first lattice unit in the `+1` lobe (the
/// coarsest standing unit of the rings it joins), the lock chart reads what `Field::contrast`
/// reads, every class is the tie rule's `+1` at `q = 0` (the declared element unchanged), and the
/// chain has no fixed node. A single channel between two rings is a singular chart: its ends are
/// the field's fixed nodes, founded on their node.
#[test]
fn the_standing_is_founded_off_its_nodes() {
    let field = chain();
    let theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    assert!(theta.fixed_nodes().is_empty());
    let unit = |g: usize| theta.lattice(Locus::Standing(g)).unwrap().unit();
    let coarsest = unit(0).max(unit(1)).max(unit(2));
    for (g, contrast) in theta.standing_contrasts().iter().enumerate() {
        assert_eq!(&field.standing_contrast(&theta, g).unwrap(), contrast);
        for (rho, x) in contrast.iter().enumerate() {
            // Ring 0's third and fourth nodes and ring 1's third meet no channel: their components
            // are their own, `Δ = −q`.
            let first = if (g == 0 || g == 1) && rho >= 4 {
                unit(g)
            } else {
                coarsest.clone()
            };
            assert_eq!(x, &first, "({g}, {rho})");
        }
    }
    let current = Current::at_rest(&field);
    let operands = Operands::at_cut(&field, &theta, &current).unwrap();
    assert!(operands.rings().iter().all(|ring| ring.sheets().iter().all(|s| *s)));
    // The chain at one matched coordinate founds at (4, 3, 2) units.
    assert_eq!(theta.standing(0)[0], &coarsest * integer(2));
    assert_eq!(theta.standing(1)[0], &coarsest * integer(3));
    assert_eq!(theta.standing(2)[0], &coarsest * integer(2));
    // One channel between two rings: the chart is singular, its ends fixed nodes.
    let pair = super::support::small_field(&[2, 2], vec![super::support::contact(0, 1, 2, 0)], 1);
    let theta = Constitution::initial(&pair, OPEN_BUDGET).unwrap();
    assert_eq!(theta.fixed_nodes().len(), 8);
    for contrast in theta.standing_contrasts() {
        assert!(contrast.iter().all(Zero::is_zero));
    }
    // Campaign 1's cycle of rings 5, 7, 11, 13: rings 2 and 3 alone share nodes 7..11, a single
    // channel there, so their 16 realified slices are its fixed nodes; every other slice is off its
    // node in the `+1` lobe.
    let campaign = crate::hnn::field::Field::declare(
        crate::hnn::field::FieldDeclaration::campaign_one(6148),
    )
    .unwrap();
    let theta = Constitution::initial(&campaign, OPEN_BUDGET).unwrap();
    // Ring 2's receiving map founds at its declared prior 2I (chart ½I), and a replaced map keeps it.
    let receiving = theta.receiving_law(2).unwrap();
    let n = receiving.gram().rows();
    assert_eq!(receiving.gram(), scaled_identity(n, integer(2)));
    assert_eq!(receiving.solved(), scaled_identity(n, rat(1, 2)));
    let replaced = theta
        .clone()
        .with_ports(2, None, None, Some(receiving.map().clone()))
        .unwrap();
    assert_eq!(replaced.receiving_law(2), Some(receiving));
    let fixed = theta.fixed_nodes();
    assert_eq!(fixed.len(), 16);
    assert!(fixed.iter().all(|&(g, rho)| (g == 2 || g == 3) && (14..22).contains(&rho)));
    for (g, contrast) in theta.standing_contrasts().iter().enumerate() {
        for (rho, x) in contrast.iter().enumerate() {
            assert_eq!(x.is_zero(), fixed.contains(&(g, rho)), "({g}, {rho})");
            assert!(!x.is_negative());
        }
    }
}

/// Lean `HNN/Normal.deposit_local`, `windowGram_apply_eq_zero`, `HNN/Retention.deposit_descends`:
/// on the six-ring path a compare's deposit reaches only the causal diamond; every locus outside it
/// is unchanged, and each element's statistic (carried value plus remainder) sums only over the
/// ticks inside its causal diamond (one tick each here).
#[test]
fn a_deposit_reaches_only_the_diamond_and_sums_only_its_window() {
    let field = six_path(2);
    let theta = generic(&field, 13);
    let (current, open) = moment(&field, 14, 9);
    let phases = phases(&field, &theta, &current);
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        0,
    )
    .unwrap();
    let (word, faces) = pending.read(&field, &theta).unwrap();
    let targets = [1usize, 0];
    let anchors = target_phases(&field, pending.anchor(), 2, &encoded(&field, &targets)).unwrap();
    let ratio = HolonRatio::compare(faces, &targets, &anchors).unwrap();
    let back = word
        .pull_back(
            &ratio.covector().unwrap(),
            theta.receiving_map(2).unwrap(),
            &current.lift()[2],
            &phases,
        )
        .unwrap();
    let (_, deposit) = compose(
        &field,
        &theta,
        &pending,
        &crate::hnn::WordOpening::Rest,
        &back,
        &targets,
        &[],
    )
    .unwrap();
    for step in deposit.linear() {
        if let LinearLocus::Contrast(g) = step.locus {
            assert_eq!(step.samples.len(), 1, "ring {g}'s diamond holds one tick");
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
    )
    .with_reach(chain_reach());
    let (next, _) = theta.deposited(&deposit).unwrap();
    assert_eq!(
        next.deposited(&deposit),
        Err(HnnError::StaleDeposit {
            staged: 0,
            published: 1
        })
    );
}

/// The declared initial constitution and priors (design (d), R3 D2, the landmark tree), on the chain
/// control: `E` (`2d_0 × |A|`) the declared `±1` pattern times 1/2 (kind 0), the receiving map `R`
/// (`2|A| × 2d_R`) zero, the receiving parametron's tree empty, the pair port's outputs 0 on ring
/// 0's width, `W_s = −½I` (the passive factor `½I`), `W_c = 0`,
/// `q = 0`, the slices the skew cyclic shift, `C = I` and `K = D = ½I` on every channel.
#[test]
fn the_initial_constitution_is_the_declared_one() {
    let field = chain();
    let theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let source = theta.source_port(0).unwrap();
    assert!((source.rows(), source.columns()) == (8, 4));
    assert!(source.entries().iter().all(|x| x.abs() == rat(1, 2)));
    assert_eq!(
        source.get(3, 2).unwrap(),
        &(declared_sign(0, 3, 2) * rat(1, 2))
    );
    let map = theta.receiving_map(2).unwrap();
    assert_eq!((map.rows(), map.columns()), (8, 4));
    assert!(map.entries().iter().all(Zero::is_zero));
    let tree = theta.landmarks(2).unwrap();
    assert_eq!(
        (tree.nodes(), tree.passed(), tree.declaration().depth),
        (0, 0, 2)
    );
    let pair = theta.pair_port(0, 1).unwrap();
    assert_eq!(pair.rank(), field.ring(0).width());
    assert!(pair.outputs().iter().flatten().all(Zero::is_zero));
    for g in 0..field.rings().len() {
        let n = field.ring(g).width();
        assert_eq!(
            theta.passive_factor(g),
            &ExactRatMatrix::identity(n).unwrap().scaled(&rat(1, 2))
        );
        assert!(theta.contrast_port(g).entries().iter().all(Zero::is_zero));
        // The standing is founded off its nodes, every slice in the `+1` lobe
        // (`the_standing_is_founded_off_its_nodes`).
        assert!(theta.standing_contrasts()[g].iter().all(Signed::is_positive));
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
    let theta = Constitution::initial(&field, OPEN_BUDGET)
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

/// **The gains read the span factor term by term** (`hnn::constitution`, "The pumped medium's
/// reach"; Lean `Holon/Deposition.{station_tick_gain, entry_span_gain}`): every tick's term
/// `g^(2(T_j − τ − 1))` is multiplied by `F(T_j − τ)`, and each station's squared re-entry sum by
/// `F` of its longest span; with no factor the passive medium's sums are read unchanged.
#[test]
fn the_gains_read_the_span_factor_term_by_term() {
    let reach = crate::hnn::constitution::Reach {
        receiver: 2,
        stations: vec![3, 5],
        entries: vec![0, 2],
        phases: 1,
        loci: Default::default(),
    };
    let growth = rat(9, 8);
    let factor: Vec<Rat> = (0..=5)
        .map(|s| integer(1) + rat(s, 2) * rat(s, 3))
        .collect();
    let power = |x: &Rat, k: u64| (0..k).fold(Rat::one(), |value, _| value * x);
    let (mut ticks, mut passive_ticks) = (Rat::zero(), Rat::zero());
    let (mut entries, mut passive_entries) = (Rat::zero(), Rat::zero());
    for &station in &reach.stations {
        for tau in 0..station {
            let term = power(&(&growth * &growth), station - tau - 1);
            ticks += &term * &factor[(station - tau) as usize];
            passive_ticks += term;
        }
        let sum: Rat = reach
            .entries
            .iter()
            .filter(|&&entry| entry <= station)
            .map(|&entry| power(&growth, station - entry))
            .sum();
        entries += &sum * &sum * &factor[station as usize];
        passive_entries += &sum * &sum;
    }
    assert_eq!(reach.tick_gain(&growth, Some(&factor)), ticks);
    assert_eq!(reach.entry_gain(&growth, Some(&factor)), entries);
    assert_eq!(reach.tick_gain(&growth, None), passive_ticks);
    assert_eq!(reach.entry_gain(&growth, None), passive_entries);
}

/// Lean `HNN/LatticeDeposit/Rebase.{rebase_value_add_rem, rebase_onLattice, invariant_history,
/// history_accounting, history_release_lt, history_within_founding_unit}`: over seeded histories
/// that interleave deposits of non-dyadic updates with re-bases onto finer lattices, a re-base keeps
/// every entry plus its carried remainder exactly, lands the entry on the finer lattice with the
/// remainder in the finer half cell, and releases nothing; after every move the entry, remainder
/// and releases sum to the founding value plus every update, the releases stay within
/// `u₀/2·Σ_{m ≤ clock} 2^(−k_m)` and so below half the founding unit `u₀`, and the entry stays
/// within `u₀/2 + u/2` of the exact accumulation, `u` the current unit.
#[test]
fn a_rebase_keeps_value_plus_carry_and_the_releases_stay_below_the_founding_half_unit() {
    use crate::hnn::constitution::Carry;
    let width = 4;
    let (mut refined, mut releasing) = (0, 0);
    for seed in 0..48 {
        let mut draw = Draw::new(seed);
        let founding = Lattice::new(2 + (draw.next() % 3) as u32);
        let half = founding.unit() / integer(2);
        let start = draw.dyadic_vector(width);
        let (mut lattice, mut clock) = (founding, 0u64);
        let mut entries = start.clone();
        let mut carry = Carry::default();
        let mut accumulated = vec![Rat::zero(); width];
        let mut released = vec![Rat::zero(); width];
        let mut kraft = Rat::zero();
        let mut rebases = 0;
        for _ in 0..24 {
            let mut at = BudgetedCarry::new(lattice, clock + 1);
            if draw.next().is_multiple_of(4) {
                let levels = (draw.next() % 3) as u32;
                let before: Vec<Rat> = (0..width).map(|i| &entries[i] + carry.at(i)).collect();
                at.rebase(levels, &mut [(&mut carry, &mut entries)])
                    .unwrap();
                lattice = at.lattice();
                assert_eq!(lattice.exponent(), founding.exponent() + rebases + levels);
                rebases += levels;
                refined += usize::from(levels > 0);
                let fine_half = lattice.unit() / integer(2);
                for i in 0..width {
                    assert_eq!(&entries[i] + carry.at(i), before[i]);
                    assert!(lattice.contains(&entries[i]));
                    assert!(-&fine_half <= carry.at(i) && carry.at(i) < fine_half);
                }
                assert!(at.released().is_empty() && !at.moved());
            } else {
                let updates = draw.vector(width);
                carry.deposit_all(&mut at, Carrier::Map, &mut entries, &updates);
                for i in 0..width {
                    accumulated[i] += &updates[i];
                }
                for (_, i, e) in at.released() {
                    released[i] += e;
                    releasing += 1;
                }
                if at.moved() {
                    clock += 1;
                    kraft += Rat::new(BigInt::one(), BigInt::one() << gamma_length(clock));
                }
            }
            let current_half = lattice.unit() / integer(2);
            for i in 0..width {
                let exact = &start[i] + &accumulated[i];
                assert_eq!(&entries[i] + carry.at(i) + &released[i], exact);
                assert!(lattice.contains(&entries[i]));
                assert!(released[i].abs() <= &half * &kraft && released[i].abs() < half);
                assert!((&entries[i] - &exact).abs() < &half + &current_half);
            }
        }
    }
    assert!(refined > 0 && releasing > 0);
}

/// The re-base is refused once the deposit has staged an entry, whose applied coordinate is in the
/// coarser unit, and for a remainder past its array.
#[test]
fn a_rebase_is_refused_mid_deposit_and_past_its_array() {
    use crate::hnn::constitution::Carry;
    let lattice = Lattice::new(3);
    let mut entries = vec![Rat::zero(); 2];
    let mut carry = Carry::default();
    let mut at = BudgetedCarry::new(lattice, 1);
    carry.deposit_all(
        &mut at,
        Carrier::Map,
        &mut entries,
        &[rat(1, 3), rat(-2, 7)],
    );
    assert!(matches!(
        at.rebase(1, &mut [(&mut carry, &mut entries)]),
        Err(HnnError::Rebase { staged: 2, .. })
    ));
    let mut at = BudgetedCarry::new(lattice, 2);
    assert!(matches!(
        at.rebase(1, &mut [(&mut carry, &mut entries[..1])]),
        Err(HnnError::Shape { .. })
    ));
    assert_eq!(at.lattice(), lattice);
}

/// Lean `HNN/LatticeDeposit/Rebase.{rebase_value_add_rem, rebase_onLattice, rebase_clock}` at the
/// machine: after a compare's deposit on the six-ring path reaches the channels, re-basing each contact's channel keeps every
/// factor and scale entry plus its carried remainder, lands the entries on the finer lattice with
/// the remainders in its half cell, keeps the clock, and leaves every other locus as it was; a
/// re-base by zero levels is the identity, a ring locus is refused, and the re-based constitution
/// takes the next deposit's carry on the finer lattice.
#[test]
fn a_contacts_channel_rebases_with_its_carried_remainders() {
    let field = six_path(2);
    let every = crate::hnn::retention::loci(&field).into_iter().collect();
    let start = generic(&field, 13);
    let (current, open) = moment(&field, 14, 9);
    // One compare's deposit, staged by the machine path at a constitution.
    let stage = |theta: &Constitution| {
        let phases = phases(&field, theta, &current);
        let pending = PendingRatio::produce(
            &current,
            &open,
            &ActiveAddress::boundary(phases.depth()),
            &phases,
            0,
        )
        .unwrap();
        let (word, faces) = pending.read(&field, theta).unwrap();
        let targets = [1usize, 0];
        let anchors = target_phases(&field, pending.anchor(), 2, &encoded(&field, &targets)).unwrap();
        let ratio = HolonRatio::compare(faces, &targets, &anchors).unwrap();
        let back = word
            .pull_back(
                &ratio.covector().unwrap(),
                theta.receiving_map(2).unwrap(),
                &current.lift()[2],
                &phases,
            )
            .unwrap();
        compose(
            &field,
            theta,
            &pending,
            &crate::hnn::WordOpening::Rest,
            &back,
            &targets,
            &[],
        )
        .unwrap()
        .1
    };
    let deposit = stage(&start);
    let (deposited, _) = start.deposited(&deposit).unwrap();
    let theta = &deposited;
    assert!(
        theta
            .carried_remainders()
            .iter()
            .any(|(l, ..)| matches!(l, Locus::Channel(_)))
    );
    let carriers = [
        Carrier::Factor(0),
        Carrier::Factor(1),
        Carrier::Factor(2),
        Carrier::FactorScale(0),
        Carrier::FactorScale(1),
        Carrier::FactorScale(2),
    ];
    let remainders = |theta: &Constitution, locus: Locus, carrier: Carrier| {
        let mut dense = vec![Rat::zero(); entries(theta, locus, carrier).len()];
        for (l, c, i, r) in theta.carried_remainders() {
            if (l, c) == (locus, carrier) {
                dense[i] = r;
            }
        }
        dense
    };
    let mut moved = 0;
    let contacts = (0..)
        .take_while(|a| theta.lattice(Locus::Channel(*a)).is_ok())
        .count();
    assert!(contacts > 0);
    for a in 0..contacts {
        let locus = Locus::Channel(a);
        assert_eq!(&theta.rebased(locus, 0, &every).unwrap(), theta);
        for levels in 1..=3 {
            let next = theta.rebased(locus, levels, &every).unwrap();
            let finer = next.lattice(locus).unwrap();
            assert_eq!(
                finer.exponent(),
                theta.lattice(locus).unwrap().exponent() + levels
            );
            assert_eq!(next.clock(locus), theta.clock(locus));
            assert_eq!(next.commit(), theta.commit() + 1);
            assert!(next.storage_product() >= theta.storage_product());
            let half = finer.unit() / integer(2);
            for carrier in carriers {
                let (before, carried) = (
                    entries(theta, locus, carrier),
                    remainders(theta, locus, carrier),
                );
                let (after, rest) = (
                    entries(&next, locus, carrier),
                    remainders(&next, locus, carrier),
                );
                for i in 0..before.len() {
                    assert_eq!(&after[i] + &rest[i], &before[i] + &carried[i]);
                    assert!(finer.contains(&after[i]));
                    assert!(-&half <= rest[i] && rest[i] < half);
                    moved += usize::from(after[i] != before[i]);
                }
            }
            assert!(next.on_lattice());
            let rebased = start.rebased(locus, levels, &every).unwrap();
            assert!(matches!(
                rebased.deposited(&deposit),
                Err(HnnError::StaleDeposit { .. })
            ));
            let (later, _) = rebased.deposited(&stage(&rebased)).unwrap();
            assert!(later.on_lattice());
            assert_eq!(later.lattice(locus).unwrap(), finer);
            let others = |t: &Constitution| {
                t.carried_remainders()
                    .into_iter()
                    .filter(|(l, ..)| *l != locus)
                    .collect::<Vec<_>>()
            };
            assert_eq!(others(&next), others(theta));
            assert_eq!(
                next.rebased(locus, 0, &every).unwrap().contact_storage(a),
                next.contact_storage(a)
            );
        }
    }
    assert!(moved > 0);
    assert!(matches!(
        theta.rebased(Locus::Element(0), 1, &every),
        Err(HnnError::RebaseLocus { .. })
    ));
    let mut released = theta.clone();
    released
        .release(&std::collections::BTreeSet::from([Locus::Channel(0)]))
        .unwrap();
    assert!(matches!(
        released.rebased(Locus::Channel(0), 1, &every),
        Err(HnnError::ReleasedLocus { .. })
    ));
}

/// **The receiving step pairs the original covector** (Astra's counterexample, October 2): a uniform
/// two-class reading with target class 0 (`g = (½, 0, −½, 0)`), a unit feature and the class
/// metric's move `D = (½, 0, −½, 0)ᵀ` read the alignment `½`, not the scaled covector's `1`.
#[test]
fn the_receiving_step_pairs_the_original_covector() {
    use crate::hnn::constitution::{Sample, receiving_fisher_face_probe};
    let half = Rat::new(1.into(), 2.into());
    let sample = Sample {
        weight: Rat::from_integer(1.into()),
        feature: vec![Rat::from_integer(1.into())],
        covector: vec![half.clone(), Rat::zero(), -half.clone(), Rat::zero()],
        masses: None,
    };
    let unit = vec![vec![half.clone()], vec![Rat::zero()], vec![-half.clone()], vec![Rat::zero()]];
    let (_, oscillation, alignment) = receiving_fisher_face_probe(&[sample], &unit).unwrap();
    assert_eq!(alignment, half);
    assert_eq!(oscillation, Rat::from_integer(1.into()));
}

// -------------------------------------------------------------------------------------------
// the receiving law's face masses and its phase statistics (October 8)

/// A receiving face as a sample: weight one, the given feature, covector and carried masses.
fn face_sample(feature: Vec<Rat>, covector: Vec<Rat>, masses: Option<Vec<Rat>>) -> Sample {
    Sample {
        weight: Rat::one(),
        feature,
        covector,
        masses,
    }
}

/// **A soft observed face carries its own masses** (the located defect, repaired in its owner): the
/// descent covector `(⅙, 0, −⅙, 0)` is `q̃ − p̃` for `p̃ = (½, ½)` against the soft `q̃ = (⅔, ⅓)`.
/// The one-hot reconstruction reads it as the one-hot target at class 0 with `p̃ = (⅚, ⅙)`, a
/// distribution too, and accepts it; the carried masses are read as they stand, and every consumer
/// of the face's masses (the prequential terms, the class metric) sees them. Where `q̃` is one-hot
/// the two readings agree, and carried masses that are no distribution over the covector's classes
/// are refused, not reread as a one-hot face.
#[test]
fn a_soft_observed_face_carries_its_own_masses_and_the_one_hot_reconstruction_is_unchanged() {
    use crate::hnn::constitution::{
        face_masses, prequential_terms, receiving_class_metric, receiving_fisher_face_probe,
    };
    let feature = vec![Rat::one(), Rat::zero()];
    let soft = vec![rat(1, 6), Rat::zero(), rat(-1, 6), Rat::zero()];
    let carried = face_sample(feature.clone(), soft.clone(), Some(vec![rat(1, 2), rat(1, 2)]));
    let reconstructed = face_sample(feature.clone(), soft, None);
    assert_eq!(face_masses(&carried), Some(vec![rat(1, 2), rat(1, 2)]));
    assert_eq!(face_masses(&reconstructed), Some(vec![rat(5, 6), rat(1, 6)]));

    // The prequential terms read the masses: the read through this map is (1, 0) at the two class
    // rows, so the curvature is Var_p̃ = p̃_0 (1 − p̃_0), ¼ at the face's own masses and 5/36 at the
    // reconstruction's; the alignment Σ g_Re · read = ⅙ does not depend on them.
    let map = ExactRatMatrix::shaped(
        4,
        2,
        vec![
            vec![Rat::one(), Rat::zero()],
            vec![Rat::zero(), Rat::zero()],
            vec![Rat::zero(), Rat::one()],
            vec![Rat::zero(), Rat::zero()],
        ],
    )
    .unwrap();
    assert_eq!(
        prequential_terms(&[carried], &map),
        Some((rat(1, 6), rat(1, 4)))
    );
    assert_eq!(
        prequential_terms(&[reconstructed], &map),
        Some((rat(1, 6), rat(5, 36)))
    );

    // The Fisher face reads them: a unit step that moves class 0's magnitude by 1 has the curvature
    // 2 (119/80) Var_p̃ (¼ and 5/36 here), the oscillation 1 and the original covector's alignment ⅙.
    let unit = vec![vec![Rat::one()], vec![Rat::zero()], vec![Rat::zero()], vec![Rat::zero()]];
    let soft = vec![rat(1, 6), Rat::zero(), rat(-1, 6), Rat::zero()];
    let fisher = |masses: Option<Vec<Rat>>| {
        let sample = face_sample(vec![Rat::one()], soft.clone(), masses);
        receiving_fisher_face_probe(&[sample], &unit)
    };
    assert_eq!(
        fisher(Some(vec![rat(1, 2), rat(1, 2)])),
        Some((rat(119, 160), Rat::one(), rat(1, 6)))
    );
    assert_eq!(fisher(None), Some((rat(119, 288), Rat::one(), rat(1, 6))));

    // The class metric reads the masses: p̃ = (⅞, ⅛) against q̃ = (⅛, ⅞) is a trace 7/32 (the
    // power of two at or below 32/7 is 4), the reconstruction's (¾, ¼) a trace 3/8 (8/3: 2).
    let steep = vec![rat(-3, 4), Rat::zero(), rat(3, 4), Rat::zero()];
    let carried = face_sample(feature.clone(), steep.clone(), Some(vec![rat(7, 8), rat(1, 8)]));
    let reconstructed = face_sample(feature.clone(), steep, None);
    assert_eq!(receiving_class_metric(&[carried]), Some(integer(4)));
    assert_eq!(receiving_class_metric(&[reconstructed]), Some(integer(2)));

    // A one-hot target: the reconstruction is exact and the carried masses agree with it.
    let one_hot = vec![rat(-1, 4), Rat::zero(), rat(1, 4), Rat::zero()];
    let masses = Some(vec![rat(1, 4), rat(3, 4)]);
    assert_eq!(
        face_masses(&face_sample(feature.clone(), one_hot.clone(), None)),
        masses
    );
    assert_eq!(
        face_masses(&face_sample(feature.clone(), one_hot.clone(), masses.clone())),
        masses
    );

    // Carried masses must be a distribution over the covector's classes: a wrong count, a negative
    // entry or a sum off one is no face, whatever the one-hot reconstruction would have read.
    for refused in [
        vec![Rat::one()],
        vec![rat(3, 2), rat(-1, 2)],
        vec![rat(1, 2), rat(1, 4)],
        vec![rat(1, 3), rat(1, 3), rat(1, 3)],
    ] {
        let covector = vec![rat(1, 6), Rat::zero(), rat(-1, 6), Rat::zero()];
        assert_eq!(
            face_masses(&face_sample(feature.clone(), covector, Some(refused))),
            None
        );
    }
}

/// The chain's constitution with its receiving map `W` of quarters (so the predicted phases
/// `W_(2c+1) · f` are nonzero), founded at the declared prior.
fn receiving_chain() -> (crate::hnn::field::Field, Constitution, ExactRatMatrix) {
    let field = chain();
    let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let (rows, n) = {
        let map = opening.receiving_law(2).unwrap().map();
        (map.rows(), map.columns())
    };
    let map = ExactRatMatrix::shaped(
        rows,
        n,
        (0..rows)
            .map(|r| {
                (0..n)
                    .map(|j| rat(((3 * r + 5 * j) % 7) as i64 - 3, 4))
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let theta = opening.with_ports(2, None, None, Some(map.clone())).unwrap();
    (field, theta, map)
}

/// A hand-built deposit of one receiving window at ring 2's map alone, on the chain's reach.
fn receiving_window(theta: &Constitution, samples: Vec<Sample>) -> Deposit {
    Deposit::new(
        theta.commit(),
        vec![LinearStep {
            locus: LinearLocus::Receiving(2),
            samples,
        }],
        Vec::new(),
        vec![Locus::ReceivingMap(2)],
    )
    .with_reach(chain_reach())
}

/// **A receiving deposit absorbs its window's phase comparisons into its own successor**, from the
/// map in force before it. Two readings on the chain's four classes, the map `W` of quarters:
/// - a soft face of weight 1 at the feature `e_0`, carried `p̃ = (½, ¼, ⅛, ⅛)` against the observed
///   `q̃ = (¼, ¼, ½, 0)` with phase gaps `Δ = (½, −¼, ¼, ·)` (class 3 has no mass, and a stray
///   covector entry there carries none): its covector is `(q̃_c − p̃_c, q̃_c Δ_c / 2)`;
/// - a one-hot face of weight 2 at `e_0 + e_1`, uncarried, target class 3 at the gap `Δ = ¾`, with a
///   stray phase entry at a class of no mass.
/// The lifted doubled targets are `t_c = W_(2c+1) f + 2Δ_c` at the classes of mass, and the
/// statistics are the hand sums `S_c = Σ w q_c f fᵀ`, `m_c = Σ w q_c t_c f`, `s_c = Σ w q_c t_c²`
/// and `N = Σ w #{c : q_c > 0} = 3 + 2`. The statistics are written whole by a checkpoint and a
/// restored constitution holds them again.
#[test]
fn a_receiving_deposit_absorbs_its_phase_comparisons_through_the_map_before_it() {
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::phase_family::PhaseStatistics;
    let (field, theta, map) = receiving_chain();
    let (a, n) = (field.alphabet(), map.columns());
    assert_eq!((a, map.rows()), (4, 8));
    let at = |r: usize, j: usize| map.get(r, j).unwrap().clone();
    let unit = |j: usize| -> Vec<Rat> { (0..n).map(|i| if i == j { Rat::one() } else { Rat::zero() }).collect() };
    let e0 = unit(0);
    let e01: Vec<Rat> = (0..n).map(|i| if i < 2 { Rat::one() } else { Rat::zero() }).collect();

    // The soft face.
    let produced = [rat(1, 2), rat(1, 4), rat(1, 8), rat(1, 8)];
    let observed = [rat(1, 4), rat(1, 4), rat(1, 2), Rat::zero()];
    let gaps = [rat(1, 2), rat(-1, 4), rat(1, 4), rat(1, 3)];
    let mut soft_covector: Vec<Rat> = (0..a)
        .flat_map(|c| [&observed[c] - &produced[c], &observed[c] * &gaps[c] / integer(2)])
        .collect();
    soft_covector[7] = rat(1, 3);
    let soft = Sample {
        weight: integer(1),
        feature: e0.clone(),
        covector: soft_covector,
        masses: Some(produced.to_vec()),
    };
    // The one-hot face.
    let produced_hot = [rat(1, 8), rat(1, 8), rat(1, 4), rat(1, 2)];
    let gap_hot = rat(3, 4);
    let mut hot_covector: Vec<Rat> = (0..a)
        .flat_map(|c| {
            let q = if c == 3 { Rat::one() } else { Rat::zero() };
            let phase = if c == 3 { &gap_hot / integer(2) } else { Rat::zero() };
            [q - &produced_hot[c], phase]
        })
        .collect();
    hot_covector[1] = rat(1, 16);
    let hot = Sample {
        weight: integer(2),
        feature: e01.clone(),
        covector: hot_covector,
        masses: None,
    };

    let deposit = receiving_window(&theta, vec![soft, hot]);
    let (next, _) = theta.deposited(&deposit).unwrap();
    let phase = next
        .receiving_law(2)
        .unwrap()
        .phase_statistics()
        .expect("a receiving law carries phase statistics");

    // The hand targets: the prediction at the map before the deposit plus twice the gap.
    let soft_target = |c: usize| {
        let predicted = at(2 * c + 1, 0);
        if observed[c].is_zero() { predicted } else { predicted + integer(2) * &gaps[c] }
    };
    let mut expected = PhaseStatistics::founded(a, n);
    let soft_targets: Vec<Rat> = (0..a).map(|c| soft_target(c)).collect();
    expected
        .absorb(&integer(1), &e0, &observed, &soft_targets)
        .unwrap();
    // The one-hot face carries no masses of its own: the text path's categorical faces have no
    // consumer of this statistic and are not retained (it is founded lazily by the soft face).
    assert_eq!(phase, &expected);

    // And the sums, by hand: N counts the soft face's three classes of positive mass; class 0 holds
    // the soft face alone and class 3 (no soft mass) holds nothing.
    assert_eq!((phase.classes(), phase.features()), (a, n));
    assert_eq!(phase.cells(), &integer(3));
    let zeros = vec![vec![Rat::zero(); n]; n];
    let mut gram0 = zeros.clone();
    gram0[0][0] = rat(1, 4);
    assert_eq!(phase.gram(0), &gram0[..]);
    let mut moment0 = vec![Rat::zero(); n];
    moment0[0] = rat(1, 4) * soft_target(0);
    assert_eq!(phase.moment(0), &moment0[..]);
    assert_eq!(phase.second(0), &(rat(1, 4) * soft_target(0) * soft_target(0)));
    assert_eq!(phase.gram(3), &zeros[..]);
    assert_eq!(phase.moment(3), &vec![Rat::zero(); n][..]);
    assert_eq!(phase.second(3), &Rat::zero());

    // A receiving law that only categorical faces reach founds no statistics at all.
    let hot_only = receiving_window(&theta, vec![hot_only_sample(&e01)]);
    let (categorical, _) = theta.deposited(&hot_only).unwrap();
    assert_eq!(categorical.receiving_law(2).unwrap().phase_statistics(), None);

    // A checkpoint writes the statistics whole and a restored constitution holds them again.
    let state = next.continuing_state(0).unwrap();
    let read = ContinuingState::from_text(&state.to_text()).unwrap();
    assert_eq!(read, state);
    let restored = Constitution::initial(&field, OPEN_BUDGET)
        .unwrap()
        .continued(&read)
        .unwrap();
    assert_eq!(restored, next);
    assert_eq!(restored.receiving_law(2).unwrap().phase_statistics(), Some(&expected));
}

/// **Only a reached face of nonnegative weight is absorbed** ([`absorb_phase`]): a zero weight, a
/// zero feature, a covector that is no face's and a face of no observed mass leave the statistics
/// as they were; a negative weight, a negative observed mass (carried masses a covector contradicts)
/// and observed masses that are no distribution are refused, typed. On a zero map the lifted target
/// is `4 g_(2c+1) / q_c`, so the reached one-hot face below (`g = (½, ⅛, −½, 0)` on `p̃ = (½, ½)`,
/// target class 0, gap `¼`) absorbs `q = (1, 0)`, `t = (½, 0)`.
#[test]
fn only_a_reached_face_of_nonnegative_weight_is_absorbed_and_the_rest_is_skipped_or_refused() {
    use crate::hnn::constitution::absorb_phase;
    use crate::hnn::phase_family::PhaseStatistics;
    let map = ExactRatMatrix::zero(4, 2).unwrap();
    let founded = PhaseStatistics::founded(2, 2);
    let absorbed = |samples: &[Sample]| {
        let mut statistics = founded.clone();
        absorb_phase(&mut statistics, &map, samples).map(|()| statistics)
    };
    let feature = vec![Rat::one(), Rat::zero()];
    let hot = vec![rat(1, 2), rat(1, 8), rat(-1, 2), Rat::zero()];
    let reached = face_sample(feature.clone(), hot.clone(), None);

    let statistics = absorbed(&[reached.clone()]).unwrap();
    assert_eq!(statistics.cells(), &integer(1));
    assert_eq!(statistics.gram(0), &[vec![Rat::one(), Rat::zero()], vec![Rat::zero(), Rat::zero()]][..]);
    assert_eq!(statistics.moment(0), &[rat(1, 2), Rat::zero()][..]);
    assert_eq!(statistics.second(0), &rat(1, 4));
    assert_eq!(statistics.second(1), &Rat::zero());

    // Skipped: nothing reached the locus, or the covector is no face's, or no class has mass.
    let skipped = [
        Sample { weight: Rat::zero(), ..reached.clone() },
        Sample { feature: vec![Rat::zero(); 2], ..reached.clone() },
        face_sample(feature.clone(), vec![Rat::one(); 4], None),
        face_sample(feature.clone(), vec![rat(-1, 2), Rat::zero(), rat(-1, 2), Rat::zero()], None),
    ];
    for sample in skipped {
        assert_eq!(absorbed(&[sample]).unwrap(), founded);
    }
    // A covector off the map's rows is a shape refusal, not a skipped face.
    assert!(matches!(
        absorbed(&[face_sample(feature.clone(), vec![rat(1, 2), rat(1, 8), rat(-1, 2)], None)]),
        Err(HnnError::Shape { .. })
    ));

    // Refused: the sample is a face, but its comparison cannot be a regression's.
    let refused = [
        Sample { weight: integer(-1), ..reached },
        // carried p̃ = (½, ½) with q̃ = p̃ + g = (−¼, 5/4): a negative observed mass
        face_sample(
            feature.clone(),
            vec![rat(-3, 4), Rat::zero(), rat(3, 4), Rat::zero()],
            Some(vec![rat(1, 2), rat(1, 2)]),
        ),
        // carried p̃ = (½, ½) with q̃ = (¾, ¾): no distribution
        face_sample(
            feature,
            vec![rat(1, 4), Rat::zero(), rat(1, 4), Rat::zero()],
            Some(vec![rat(1, 2), rat(1, 2)]),
        ),
    ];
    for sample in refused {
        assert!(matches!(absorbed(&[sample]), Err(HnnError::Unadmitted { .. })));
    }
}

/// **A move of the prior leaves the phase statistics as they were**, and `prior_scale` reads the
/// ridge `2^k I` in force: the receiving law below (the prior carry's fixture) holds statistics
/// and moves `k = 2` to `k′ = 1` by its pair's Newton point; the moved law holds the same
/// statistics, and the sources and contrasts of a constitution hold none.
#[test]
fn a_moved_prior_keeps_the_phase_statistics_and_the_ridge_is_read_at_its_scale() {
    use crate::hnn::constitution::LocatedPrior;
    use crate::hnn::phase_family::PhaseStatistics;
    let lattice = Lattice::new(4);
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
    let law = NormalLaw::with_receiving_prior(map, 2);
    assert_eq!(law.prior_scale(), 2);
    // Founded lazily by the deposit at the first soft face, so none is held at founding.
    assert_eq!(law.phase_statistics(), None);
    // One deposit so the Gram has a support (the prior carry's window at t = 1).
    let reading = |feature: [Rat; 2], masses: [Rat; 2], target: usize| {
        let covector: Vec<Rat> = (0..2)
            .flat_map(|c| {
                let q = if c == target { Rat::one() } else { Rat::zero() };
                [q - &masses[c], rat(1, 16)]
            })
            .collect();
        face_sample(feature.to_vec(), covector, None)
    };
    let samples = vec![
        reading([rat(-1, 4), rat(1, 2)], [rat(3, 8), rat(5, 8)], 0),
        reading([rat(1, 4), rat(-1, 4)], [rat(5, 8), rat(3, 8)], 0),
        reading([rat(-1, 2), rat(1, 4)], [rat(3, 8), rat(5, 8)], 0),
    ];
    let mut at = BudgetedCarry::new(lattice, 1);
    let (law, _) = law.deposited(&samples, &rat(1, 4), &rule, &mut at).unwrap();
    // The statistics a window left, and a pair whose Newton point asks for k′ = 1.
    let mut statistics = PhaseStatistics::founded(2, 2);
    statistics
        .absorb(&Rat::one(), &[rat(1, 2), rat(-1, 4)], &[rat(1, 2), rat(1, 2)], &[rat(1, 3), rat(-2, 3)])
        .unwrap();
    let s = rat(5, 3);
    let law = law
        .with_phase(Some(statistics.clone()))
        .with_located(Some(LocatedPrior::from_parts(2, Rat::zero(), s.clone(), s)));
    let (moved, read) = law
        .moved_prior(&rule, &mut BudgetedCarry::new(lattice, 2))
        .unwrap()
        .unwrap();
    assert_eq!((read.from, read.to, read.held), (2, 1, None));
    assert_eq!(moved.prior_scale(), 1);
    assert_eq!(moved.phase_statistics(), Some(&statistics));

    // Sources and contrasts hold none; the receiving law holds none until a soft face reaches it.
    let mut declared = super::learning::chain_declaration(1 << 16);
    declared.receivers[0].receiving_prior = 3;
    let field = crate::hnn::field::Field::declare(declared.by_lattice_rule()).unwrap();
    let theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let receiving = theta.receiving_law(2).unwrap();
    assert_eq!(receiving.prior_scale(), 3);
    assert_eq!(receiving.phase_statistics(), None);
    assert_eq!(theta.source_law(0).unwrap().phase_statistics(), None);
    for g in 0..field.rings().len() {
        assert_eq!(theta.contrast_law(g).phase_statistics(), None);
    }
    let zero = ExactRatMatrix::zero(4, 2).unwrap();
    assert_eq!(NormalLaw::with_prior(zero.clone()).phase_statistics(), None);
    assert_eq!(NormalLaw::with_scaled_prior(zero, 2).phase_statistics(), None);
}

// -------------------------------------------------------------------------------------------
// the receiving step's alignment, certified against the smooth face (October 8)

/// **The odometer's misreading of a receiving step's alignment, exactly**
/// ([`crate::hnn::constitution::odometer_alignment_defect_probe`]). Two classes at `p̃ = (½, ½)` with
/// the magnitude move `Δ_Re = (1, −1)`: every class `s` reads `Σ_c p̃_c |Δ_c − Δ_s| = 1`, so the
/// defect is `1/16`. Three classes at `p̃ = (½, ¼, ¼)` with `Δ_Re = (0, 2, 4)` read `3/2, 3/2, 5/2`,
/// the least `3/2`, so a weight-two face's defect is `2 · (3/2) / 16 = 3/16`. The phase rows add
/// nothing. A face whose masses are unread (a covector that is no face's `q − p̃`) has no bound.
#[test]
fn the_odometer_defect_is_read_exactly_at_the_least_class() {
    use crate::hnn::constitution::odometer_alignment_defect_probe;
    let two = Sample {
        weight: Rat::one(),
        feature: vec![Rat::one()],
        covector: vec![rat(1, 8), rat(1, 5), rat(-1, 8), rat(1, 7)],
        masses: Some(vec![rat(1, 2), rat(1, 2)]),
    };
    let unit_two = vec![vec![Rat::one()], vec![integer(9)], vec![-Rat::one()], vec![integer(-9)]];
    assert_eq!(odometer_alignment_defect_probe(&[two], &unit_two), Some(rat(1, 16)));

    let three = Sample {
        weight: integer(2),
        feature: vec![Rat::one()],
        covector: vec![
            rat(1, 4),
            Rat::zero(),
            rat(-1, 8),
            Rat::zero(),
            rat(-1, 8),
            Rat::zero(),
        ],
        masses: Some(vec![rat(1, 2), rat(1, 4), rat(1, 4)]),
    };
    let unit_three = vec![
        vec![Rat::zero()],
        vec![integer(5)],
        vec![integer(2)],
        vec![Rat::zero()],
        vec![integer(4)],
        vec![integer(-3)],
    ];
    assert_eq!(odometer_alignment_defect_probe(&[three], &unit_three), Some(rat(3, 16)));

    // No face: the one-hot reconstruction of (½, 0, ½, 0) leaves a negative mass.
    let stray = Sample {
        weight: Rat::one(),
        feature: vec![Rat::one()],
        covector: vec![rat(1, 2), Rat::zero(), rat(1, 2), Rat::zero()],
        masses: None,
    };
    assert_eq!(odometer_alignment_defect_probe(&[stray], &unit_two), None);
}

/// **A receiving step its alignment cannot certify is refused, and one it can is taken.** On the
/// chain's four classes, a soft face at `p̃ = (¼, ¼, ¼, ¼)` observed as `q̃ = (¼ + ε, ¼ − ε, ¼, ¼)`
/// with no phase gap. The class metric is `4` here, and one reading's step is `Δ = c·(4 g_Re, g_Im)`
/// with `c = w fᵀX̂f > 0`, so the alignment is `8cε²` and the odometer's defect `cε/8`: the step is
/// certified exactly when `ε > 1/64`. At `ε = 1/128` the map's step is refused (no certified map step
/// at the receiving locus; the deposit itself is admitted, so its phase statistics still absorb the
/// reading), and at `ε = 1/8` it is taken with an alignment below the uncorrected one.
#[test]
fn a_receiving_step_its_alignment_cannot_certify_is_refused() {
    let (field, theta, map) = receiving_chain();
    let (a, n) = (field.alphabet(), map.columns());
    assert_eq!(a, 4);
    let e0: Vec<Rat> = (0..n).map(|i| if i == 0 { Rat::one() } else { Rat::zero() }).collect();
    let quarter = rat(1, 4);
    let face = |epsilon: Rat| Sample {
        weight: Rat::one(),
        feature: e0.clone(),
        covector: vec![
            epsilon.clone(),
            Rat::zero(),
            -epsilon,
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
        ],
        masses: Some(vec![quarter.clone(); 4]),
    };
    let map_steps = |reading: &crate::hnn::constitution::DepositReading| {
        reading
            .steps
            .iter()
            .filter(|(locus, step)| *locus == Locus::ReceivingMap(2) && step.family == Family::Map)
            .count()
    };

    let (refused, reading) = theta
        .deposited(&receiving_window(&theta, vec![face(rat(1, 128))]))
        .unwrap();
    assert_eq!(map_steps(&reading), 0);
    assert_eq!(
        refused
            .receiving_law(2)
            .unwrap()
            .phase_statistics()
            .unwrap()
            .cells(),
        &integer(4)
    );

    let (_, reading) = theta
        .deposited(&receiving_window(&theta, vec![face(rat(1, 8))]))
        .unwrap();
    assert_eq!(map_steps(&reading), 1);
}

/// A categorical (one-hot, uncarried) receiving face on the chain's four classes, target class 3.
fn hot_only_sample(feature: &[Rat]) -> Sample {
    let produced = [rat(1, 8), rat(1, 8), rat(1, 4), rat(1, 2)];
    let covector: Vec<Rat> = (0..4)
        .flat_map(|c| {
            let q = if c == 3 { Rat::one() } else { Rat::zero() };
            [q - &produced[c], Rat::zero()]
        })
        .collect();
    Sample {
        weight: integer(1),
        feature: feature.to_vec(),
        covector,
        masses: None,
    }
}
