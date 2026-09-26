//! The word on declared lattices (Decision 24; Lean `HNN/LatticeWord`): the declared precisions,
//! the certified inverse charts and their refinement, the executed adjoint, the carrier's refusal,
//! error feedback, and a resident's warm start.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::{generic, moment};
use super::support::{Draw, Medium, chorded_field};
use crate::hnn::HnnError;
use crate::hnn::chart::{
    ChartKey, ChartStart, ChartWords, Charts, WordLattice, carry, certificate, newton_schulz_step,
    refine,
};
use crate::hnn::constitution::Lattice;
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldDeclaration};
use crate::hnn::propagation::Operands;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::dot;
use crate::ratio::{Rat, integer, rat};

/// The ℓ∞ operator norm, the largest absolute row sum (Lean `rowNorm`).
fn row_norm(m: &ExactRatMatrix) -> Rat {
    (0..m.rows())
        .map(|i| m.row(i).unwrap().iter().map(|x| x.abs()).sum::<Rat>())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// `I − ½K` for a passive `K = −ffᵀ + Σ (u vᵀ − v uᵀ)` of dyadic factors: the ring's operator.
fn ring_operator(draw: &mut Draw, n: usize) -> ExactRatMatrix {
    let f = draw.dyadic_matrix(n, n).scaled(&rat(1, 4));
    let mut k = f
        .multiply(&f.transpose().unwrap())
        .unwrap()
        .scaled(&-Rat::one());
    for _ in 0..n {
        let (u, v) = (draw.dyadic_vector(n), draw.dyadic_vector(n));
        let outer = |a: &[Rat], b: &[Rat]| {
            ExactRatMatrix::shaped(
                n,
                n,
                (0..n)
                    .map(|i| (0..n).map(|j| &a[i] * &b[j]).collect())
                    .collect(),
            )
            .unwrap()
        };
        k = k
            .add(&outer(&u, &v).subtract(&outer(&v, &u)).unwrap())
            .unwrap();
    }
    ExactRatMatrix::identity(n)
        .unwrap()
        .subtract(&k.scaled(&rat(1, 2)))
        .unwrap()
}

/// Campaign 1's declared precisions by rule: `L_R = 16`, `X_w = 2d_R = 22`, the widest solve
/// `w = 26` (ring 3's `2·13`) and `e_max = e_0 + A = 2 + 2`, so `D_c = ⌈log₂ 292,864⌉ = 19`,
/// `L_c = 38` and `L_w = ⌈log₂(4·16·22·4·3)⌉ = ⌈log₂ 16,896⌉ = 15`; and the field codes them in
/// its description.
#[test]
fn the_rule_declares_campaign_ones_precisions() {
    let field = Field::declare(FieldDeclaration::campaign_one(6148)).unwrap();
    let word = field.word_lattice().unwrap();
    assert_eq!(*word, WordLattice::by_rule(16, 22, 26, 4));
    assert_eq!(
        (
            word.chart_exponent(),
            word.target_exponent(),
            word.transient_exponent()
        ),
        (38, 19, 15)
    );
    assert_eq!(word.target(), Rat::new(BigInt::one(), BigInt::one() << 19));
    let steps = crate::hnn::Steps::campaign_one();
    assert_ne!(
        field.describe(&steps, 1 << 33, 64),
        field
            .clone()
            .with_exact_word()
            .describe(&steps, 1 << 33, 64),
        "the description codes the word's precisions"
    );
}

/// Lean `HNN/LatticeWord.{feedback_tick, feedback_rem_bounds, feedback_accounting_zero,
/// feedback_sum_within_half_unit}`: each split keeps `x + r′ = y + r` exactly with `x` on the
/// lattice and `r′` in its half-open cell `[−u/2, u/2)`, ties upward; over a sequence from a zero
/// remainder `Σ x + r_T = Σ y`, so the partial sums track within half a unit.
#[test]
fn error_feedback_carries_its_remainder_exactly() {
    let lattice = Lattice::new(6);
    let (unit, half) = (lattice.unit(), lattice.unit() / integer(2));
    let mut tie = vec![Rat::zero()];
    assert_eq!(
        carry(&lattice, &[half.clone()], &mut tie),
        vec![unit.clone()]
    );
    assert_eq!(tie, vec![-half.clone()], "ties upward");
    let mut draw = Draw::new(21);
    let mut remainder = vec![Rat::zero(); 5];
    let (mut carried, mut images) = (vec![Rat::zero(); 5], vec![Rat::zero(); 5]);
    for _ in 0..40 {
        let image: Vec<Rat> = (0..5).map(|_| draw.rational() * rat(1, 7)).collect();
        let before = remainder.clone();
        let values = carry(&lattice, &image, &mut remainder);
        for i in 0..5 {
            assert_eq!(&values[i] + &remainder[i], &image[i] + &before[i]);
            assert!(lattice.contains(&values[i]));
            assert!(-&half <= remainder[i] && remainder[i] < half);
            carried[i] += &values[i];
            images[i] += &image[i];
        }
    }
    for i in 0..5 {
        assert_eq!(&carried[i] + &remainder[i], images[i]);
        assert!((&carried[i] - &images[i]).abs() <= half);
    }
}

/// Lean `HNN/LatticeWord.{rounded_refinement_certificate, newton_schulz_iter_rowNorm,
/// inverse_chart_deviation}`: one rounded step leaves `‖1 − AX″‖∞ ≤ ‖1 − AX‖∞² + ‖A‖∞ n 2^(−L)/2`,
/// the certificate the refinement reports is `‖1 − AX̂‖∞` read exactly, and a certified chart lies
/// within `‖X̂‖∞δ/(1 − δ)` of the exact inverse.
#[test]
fn a_rounded_newton_schulz_step_squares_the_residual_up_to_its_rounding() {
    let mut draw = Draw::new(22);
    let exponent = 30;
    let n = 5;
    for _ in 0..4 {
        let a = ring_operator(&mut draw, n);
        let inverse = a.inverse().unwrap();
        // A start off the inverse: the inverse's chart on a coarse lattice, re-read on the fine one.
        let coarse = ChartWords::of_matrix(&inverse, 8).unwrap();
        let start = ChartWords::of_matrix(&coarse.to_matrix().unwrap(), exponent).unwrap();
        let delta = certificate(&a, &start).unwrap();
        assert!(delta < rat(1, 2));
        let next = newton_schulz_step(&a, &start).unwrap();
        let rounding =
            row_norm(&a) * integer(n as i64) * (Lattice::new(exponent).unit() / integer(2));
        let after = certificate(&a, &next).unwrap();
        assert!(after <= &delta * &delta + &rounding);
        let residual = ExactRatMatrix::identity(n)
            .unwrap()
            .subtract(&a.multiply(&next.to_matrix().unwrap()).unwrap())
            .unwrap();
        assert_eq!(
            row_norm(&residual),
            after,
            "the certificate is read exactly"
        );
        let deviation = row_norm(&inverse.subtract(&next.to_matrix().unwrap()).unwrap());
        let norm = row_norm(&next.to_matrix().unwrap());
        assert!(deviation <= &norm * &after / (Rat::one() - &after));
    }
}

/// The refinement's three starts (module header): cold from the scaled transpose where no chart
/// is kept, even where `‖1 − A‖∞ > 1` (so no scaled identity would start it); warm from the last
/// chart when a deposit moves the operator by `D`, whose start's certificate is at most
/// `‖1 − AX̂‖∞ + ‖D‖∞‖X̂‖∞` (Lean `warm_start_certificate`); and at an unchanged operator, the same
/// chart with no step.
#[test]
fn the_refinement_starts_cold_warm_or_idle() {
    let mut draw = Draw::new(23);
    let lattice = WordLattice::by_rule(16, 10, 10, 4);
    let n = 8;
    let a = ring_operator(&mut draw, n);
    let identity = ExactRatMatrix::identity(n).unwrap();
    assert!(row_norm(&identity.subtract(&a).unwrap()) > Rat::one());
    let (cold, reading) = refine(ChartKey::Ring(0), &a, None, &lattice).unwrap();
    assert_eq!(reading.start, ChartStart::Transpose);
    assert!(reading.steps > 0);
    assert!(reading.certificate <= lattice.target());
    let (idle, again) = refine(ChartKey::Ring(0), &a, Some(&cold), &lattice).unwrap();
    assert_eq!(
        (idle.clone(), again.start, again.steps),
        (cold.clone(), ChartStart::Warm, 0)
    );
    let deposit = draw.dyadic_matrix(n, n).scaled(&rat(1, 4096));
    let moved = a.add(&deposit).unwrap();
    let start = certificate(&moved, &cold).unwrap();
    assert!(
        start
            <= certificate(&a, &cold).unwrap()
                + row_norm(&deposit) * row_norm(&cold.to_matrix().unwrap())
    );
    let (_, warm) = refine(ChartKey::Ring(0), &moved, Some(&cold), &lattice).unwrap();
    assert_eq!(warm.start, ChartStart::Warm);
    assert!(warm.certificate <= lattice.target());
}

/// Lean `HNN/LatticeWord.{executed_adjoint_pairing, executed_adjoint_unique}`: the executed chart
/// and its transpose pair exactly, `⟨λ, X̂x⟩ = ⟨X̂ᵀλ, x⟩`, each the exact product of the chart's
/// values.
#[test]
fn the_executed_adjoint_pairs_with_its_chart() {
    let mut draw = Draw::new(24);
    let a = ring_operator(&mut draw, 6);
    let (chart, _) = refine(
        ChartKey::Ring(0),
        &a,
        None,
        &WordLattice::by_rule(16, 6, 6, 4),
    )
    .unwrap();
    let matrix = chart.to_matrix().unwrap();
    for _ in 0..4 {
        let (x, lambda) = (draw.vector(6), draw.vector(6));
        let image = chart.apply(&x).unwrap();
        assert_eq!(image, matrix.apply(&x).unwrap());
        let pulled = chart.apply_transpose(&lambda).unwrap();
        assert_eq!(dot(&lambda, &image), dot(&pulled, &x));
    }
}

/// The carrier (the device's, `holonics-cuda::hnn::lattice`): a chart's coordinate is a signed
/// 64-bit word, and a product entry whose ℓ1 bound `Σ_j |q_ij x_j|` reaches `2^127` is refused
/// whatever its value, while one just below it is admitted; nothing is rounded.
#[test]
fn the_carrier_refuses_a_sum_past_its_certificate() {
    let big = BigInt::from(i64::MAX);
    let chart = ChartWords::of_coordinates(1, 2, 0, &[big.clone(), -big.clone()]).unwrap();
    let word = Rat::from_integer(big.clone());
    // (2^63 − 1)² · 2 < 2^127: admitted, and the sum cancels to zero.
    assert_eq!(
        chart.apply(&[word.clone(), word.clone()]).unwrap(),
        vec![Rat::zero()]
    );
    let wide =
        ChartWords::of_coordinates(1, 3, 0, &[big.clone(), big.clone(), -big.clone()]).unwrap();
    assert!(matches!(
        wide.apply(&[word.clone(), word.clone(), word.clone()]),
        Err(HnnError::Carrier { .. })
    ));
    assert!(matches!(
        ChartWords::of_coordinates(1, 1, 0, &[BigInt::one() << 63]),
        Err(HnnError::Carrier { .. })
    ));
}

/// A resident's warm start (Decision 24): operands read at a cut refine every chart and keep it;
/// read again at the same constitution they start warm, take no step and execute the same charts,
/// so a read at an unchanged operator returns the same word.
#[test]
fn a_resident_reads_again_its_certified_charts() {
    let field = chorded_field();
    let medium = Medium::encoding(&field, 25);
    let current = Current::at_rest(&field);
    let mut charts = Charts::new();
    let first = Operands::at_cut_charted(&field, &medium, &current, &mut charts).unwrap();
    assert_eq!(charts.len(), field.rings().len() + field.contacts().len());
    assert!(
        first
            .charts()
            .iter()
            .all(|reading| reading.start != ChartStart::Warm)
    );
    let second = Operands::at_cut_charted(&field, &medium, &current, &mut charts).unwrap();
    assert!(
        second
            .charts()
            .iter()
            .all(|reading| reading.start == ChartStart::Warm && reading.steps == 0)
    );
    let solves = |operands: &Operands| {
        (
            operands
                .rings()
                .iter()
                .map(|ring| ring.solve().unwrap())
                .collect::<Vec<_>>(),
            operands
                .contacts()
                .iter()
                .map(|contact| contact.solve().unwrap())
                .collect::<Vec<_>>(),
        )
    };
    assert_eq!(solves(&first), solves(&second));
    assert!(charts.bits() > 0);
}

/// On a deposited constitution the resident's charts move by warm refinements only: a generic
/// constitution nearby (the chain's generic material, its standing moved by a quarter) refines from
/// the charts the first left, every certificate at most the target.
#[test]
fn a_deposit_moves_the_charts_by_warm_refinement() {
    let field = super::learning::chain();
    let theta = generic(&field, 26);
    let (current, _) = moment(&field, 27, 9);
    let mut charts = Charts::new();
    Operands::at_cut_charted(&field, &theta, &current, &mut charts).unwrap();
    let passive = theta.passive_factor(1).clone();
    let moved = theta
        .clone()
        .with_element(
            1,
            passive
                .add(
                    &ExactRatMatrix::identity(passive.rows())
                        .unwrap()
                        .scaled(&rat(1, 1024)),
                )
                .unwrap(),
            theta.contrast_port(1).clone(),
            theta.slices(1).to_vec(),
        )
        .unwrap();
    let after = Operands::at_cut_charted(&field, &moved, &current, &mut charts).unwrap();
    let target = field.word_lattice().unwrap().target();
    for reading in after.charts() {
        assert_eq!(reading.start, ChartStart::Warm);
        assert!(reading.certificate <= target);
    }
    assert!(after.charts().iter().any(|reading| reading.steps > 0));
}
