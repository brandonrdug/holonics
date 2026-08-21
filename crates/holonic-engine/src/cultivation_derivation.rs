//! Exact, bounded W3 cultivation return over one two-coordinate section.
//!
//! This is the small derivation owner for the constrained W3 control.  It consumes only the
//! supplied development continuation and subject-control terminal sections plus the two receiver
//! potentials.  It never opens held-out material and never looks up an expected output.  The
//! resulting one-coordinate delta is an exact rational map; its adjoint, defect, factorization,
//! reconstruction fibre, and counted work travel together.

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::embedding_fiber::AlignedMaterial;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix, LinearFactorization};
use crate::exact_work::ExactWork;

/// A terminal hidden point section supplied by the caller as caused continuation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiddenPointSection {
    pub coordinates: Vec<Rat>,
}

/// The W3 vocabulary uses both names for the same terminal point face.
pub type TerminalHiddenPointSection = HiddenPointSection;

impl HiddenPointSection {
    pub fn new(coordinates: Vec<Rat>) -> Self {
        Self { coordinates }
    }
}

/// The first lexicographic coordinate pair whose two terminal sections have nonzero determinant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinatePair {
    pub first: usize,
    pub second: usize,
    pub determinant: Rat,
    /// `v = (c_j, -c_i)`, which annihilates the two-coordinate subject-control section.
    pub control_annihilator: [Rat; 2],
    /// Octaves of the exact aligned two-entry factor. This is a material-derived carrier face,
    /// not a caller rank or width.
    pub control_factor_octaves: u32,
}

/// The exact resident-grain face of the constrained activation.  The raw rational remains
/// available in `value`; the interval is what the strict receiver is allowed to use.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlacedActivation {
    pub value: Rat,
    pub lower: Rat,
    pub upper: Rat,
    pub grain: i32,
}

/// A complete exact W3 return.  `target_potential` is supplied input, not a value read from any
/// held-out face; the reconstruction fibre therefore answers only the declared one-coordinate
/// map's supplied development continuation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CultivationDerivation {
    /// The caused target vocabulary row receiving the supported delta.
    pub target_vocabulary: usize,
    pub pair: CoordinatePair,
    pub target_potential: Rat,
    pub strongest_competing_upper_face: Rat,
    /// The supplied strict response gap `competitor - target`.
    pub strict_target_gap: Rat,
    pub u_exponent: i32,
    pub u_scale: Rat,
    pub placed_activation: PlacedActivation,
    pub lower_development_delta: Rat,
    pub development_delta: Rat,
    pub separated_potential: Rat,
    pub map: ExactRatMatrix,
    pub domain_metric: ExactRatMatrix,
    pub codomain_metric: ExactRatMatrix,
    pub adjoint: ExactRatMatrix,
    pub adjoint_on_unit: Rat,
    pub adjoint_defect: Rat,
    pub bare_transpose_defect: Rat,
    /// The perturbed-domain metric's adjoint, retained as the metric control.
    pub perturbed_adjoint: ExactRatMatrix,
    pub metric_perturbation: ExactRatMatrix,
    pub rank: usize,
    pub factorization: LinearFactorization,
    pub sparse_defect: ExactRatMatrix,
    pub sparse_defect_factorization: LinearFactorization,
    pub reconstruction_fibre: Option<(Vec<Rat>, Vec<Vec<Rat>>)>,
    pub work: ExactWork,
}

impl CultivationDerivation {
    /// Canonical JSON bytes for the complete exact return. Struct field order is fixed by the
    /// declaration above; no digest is computed from an omitted summary or invented hash.
    pub fn canonical_receipt_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec(self)
    }

    /// SHA-256 over [`Self::canonical_receipt_bytes`], suitable for binding the actual receipt
    /// bytes into a rest metadata record.
    pub fn canonical_receipt_digest(&self) -> Result<String, serde_json::Error> {
        Ok(format!(
            "{:x}",
            Sha256::digest(&self.canonical_receipt_bytes()?)
        ))
    }

    /// Canonical bytes for the exact metric adjoint alone.  The full derivation and this
    /// narrower certificate are carried separately so a detached child can parse either face.
    pub fn canonical_adjoint_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec(&self.adjoint)
    }

    pub fn canonical_adjoint_digest(&self) -> Result<String, serde_json::Error> {
        Ok(format!(
            "{:x}",
            Sha256::digest(&self.canonical_adjoint_bytes()?)
        ))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CultivationDerivationError {
    #[error("the terminal sections have different coordinate extents")]
    DimensionMismatch,
    #[error("at least two terminal coordinates are required")]
    TooFewCoordinates,
    #[error("every coordinate pair is control-collinear")]
    NoSeparatingPair,
    #[error("the target and competing face do not have a positive strict gap")]
    NonPositiveGap,
    #[error(
        "every non-collinear pair is below the resident grain or cannot separate the declared receiver"
    )]
    NoAdmissiblePair,
    #[error("a rational cannot be placed at the requested resident grain")]
    GrainOverflow,
    #[error("exact linear return failed: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("coordinate {index} is not dyadic and cannot enter AlignedMaterial")]
    NonDyadic { index: usize },
    #[error("aligned coordinate {index} exceeds the signed material carrier")]
    AlignmentOverflow { index: usize },
}

fn rat_integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn power_of_two(exponent: i32) -> Result<Rat, CultivationDerivationError> {
    if exponent >= 0 {
        Ok(Rat::from_integer(
            BigInt::one()
                << usize::try_from(exponent)
                    .map_err(|_| CultivationDerivationError::GrainOverflow)?,
        ))
    } else {
        let magnitude = exponent
            .checked_abs()
            .ok_or(CultivationDerivationError::GrainOverflow)?;
        Ok(Rat::new(
            BigInt::one(),
            BigInt::one()
                << usize::try_from(magnitude)
                    .map_err(|_| CultivationDerivationError::GrainOverflow)?,
        ))
    }
}

fn floor_integer(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if numerator.is_negative() && !remainder.is_zero() {
        quotient - 1
    } else {
        quotient
    }
}

fn ceil_integer(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if numerator.is_positive() && !remainder.is_zero() {
        quotient + 1
    } else {
        quotient
    }
}

/// Place one exact activation at a declared resident grain and retain both endpoint faces.
pub fn place_activation(
    value: Rat,
    grain: i32,
) -> Result<PlacedActivation, CultivationDerivationError> {
    let step = power_of_two(
        grain
            .checked_neg()
            .ok_or(CultivationDerivationError::GrainOverflow)?,
    )?;
    let reciprocal = Rat::from_integer(BigInt::one()) / &step;
    let scaled = &value * reciprocal;
    let lower_integer = floor_integer(scaled.numer(), scaled.denom());
    let upper_integer = ceil_integer(scaled.numer(), scaled.denom());
    Ok(PlacedActivation {
        value,
        lower: Rat::from_integer(lower_integer) * &step,
        upper: Rat::from_integer(upper_integer) * &step,
        grain,
    })
}

fn oriented_pair(
    first: usize,
    second: usize,
    development: &HiddenPointSection,
    control: &HiddenPointSection,
) -> Option<CoordinatePair> {
    let raw = &development.coordinates[first] * &control.coordinates[second]
        - &development.coordinates[second] * &control.coordinates[first];
    if raw.is_zero() {
        return None;
    }
    let (determinant, control_annihilator) = if raw.is_positive() {
        (
            raw,
            [
                control.coordinates[second].clone(),
                -control.coordinates[first].clone(),
            ],
        )
    } else {
        (
            -raw,
            [
                -control.coordinates[second].clone(),
                control.coordinates[first].clone(),
            ],
        )
    };
    let control_factor_octaves = to_aligned_material(&control_annihilator)
        .ok()?
        .entry_octaves;
    Some(CoordinatePair {
        first,
        second,
        determinant,
        control_annihilator,
        control_factor_octaves,
    })
}

fn first_pair(
    development: &HiddenPointSection,
    control: &HiddenPointSection,
) -> Result<CoordinatePair, CultivationDerivationError> {
    if development.coordinates.len() != control.coordinates.len() {
        return Err(CultivationDerivationError::DimensionMismatch);
    }
    if development.coordinates.len() < 2 {
        return Err(CultivationDerivationError::TooFewCoordinates);
    }
    for first in 0..development.coordinates.len() {
        for second in (first + 1)..development.coordinates.len() {
            if let Some(pair) = oriented_pair(first, second, development, control) {
                return Ok(pair);
            }
        }
    }
    Err(CultivationDerivationError::NoSeparatingPair)
}

/// Select the first lexicographic non-collinear coordinate pair and return its control-annihilating
/// direction.
pub fn select_coordinate_pair(
    development: &HiddenPointSection,
    subject_control: &HiddenPointSection,
) -> Result<CoordinatePair, CultivationDerivationError> {
    first_pair(development, subject_control)
}

/// The control-annihilating direction `v = (c_j, -c_i)` for an already selected pair.
pub fn control_annihilator(pair: &CoordinatePair) -> [Rat; 2] {
    pair.control_annihilator.clone()
}

/// Return the least `2^e`, for any integer `e`, for which `target + 2^e * delta > competitor`.
pub fn least_power_of_two_separating(
    target: &Rat,
    competitor: &Rat,
    delta: &Rat,
) -> Result<(i32, Rat, Rat), CultivationDerivationError> {
    let gap = competitor - target;
    if gap <= Rat::zero() || delta <= &Rat::zero() {
        return Err(CultivationDerivationError::NonPositiveGap);
    }
    let mut exponent = 0i32;
    let mut scale = Rat::from_integer(BigInt::one());
    if &scale * delta <= gap {
        while &scale * delta <= gap {
            scale *= rat_integer(2);
            exponent = exponent
                .checked_add(1)
                .ok_or(CultivationDerivationError::GrainOverflow)?;
        }
    } else {
        loop {
            let half = &scale / rat_integer(2);
            if &half * delta <= gap {
                break;
            }
            scale = half;
            exponent = exponent
                .checked_sub(1)
                .ok_or(CultivationDerivationError::GrainOverflow)?;
        }
    }
    Ok((exponent, scale.clone(), target + &scale * delta))
}

/// Derive the bounded two-coordinate W3 return.
pub fn derive_w3_return(
    development: &HiddenPointSection,
    subject_control: &HiddenPointSection,
    target_potential: Rat,
    strongest_competing_upper_face: Rat,
) -> Result<CultivationDerivation, CultivationDerivationError> {
    derive_w3_return_at_grain(
        development,
        subject_control,
        target_potential,
        strongest_competing_upper_face,
        0,
    )
}

/// Derive the return after exact resident placement at `grain` (`2^-grain` spacing).
pub fn derive_w3_return_at_grain(
    development: &HiddenPointSection,
    subject_control: &HiddenPointSection,
    target_potential: Rat,
    strongest_competing_upper_face: Rat,
    grain: i32,
) -> Result<CultivationDerivation, CultivationDerivationError> {
    derive_w3_return_at_grain_with_target(
        development,
        subject_control,
        target_potential,
        strongest_competing_upper_face,
        grain,
        0,
    )
}

/// Derive the return at a resident grain for an explicitly addressed caused target row.
pub fn derive_w3_return_at_grain_with_target(
    development: &HiddenPointSection,
    subject_control: &HiddenPointSection,
    target_potential: Rat,
    strongest_competing_upper_face: Rat,
    grain: i32,
    target_vocabulary: usize,
) -> Result<CultivationDerivation, CultivationDerivationError> {
    if development.coordinates.len() != subject_control.coordinates.len() {
        return Err(CultivationDerivationError::DimensionMismatch);
    }
    if development.coordinates.len() < 2 {
        return Err(CultivationDerivationError::TooFewCoordinates);
    }
    // Search the same complete pair family by a proven lower bound on its aligned carrier width.
    // A pair cannot need fewer octaves than either constituent needs alone; once that lower bound
    // exceeds the best returned pair, the remaining sorted population cannot improve it.
    let mut coordinates = subject_control
        .coordinates
        .iter()
        .enumerate()
        .filter_map(|(index, value)| {
            to_aligned_material(std::slice::from_ref(value))
                .ok()
                .map(|material| (material.entry_octaves, index))
        })
        .collect::<Vec<_>>();
    coordinates.sort();
    let mut chosen: Option<(CoordinatePair, PlacedActivation, i32, Rat, Rat)> = None;
    let mut best_octaves = u32::MAX;
    for left in 0..coordinates.len() {
        if coordinates[left].0 > best_octaves {
            break;
        }
        for right in (left + 1)..coordinates.len() {
            let lower_bound = coordinates[left].0.max(coordinates[right].0);
            if lower_bound > best_octaves {
                break;
            }
            let first = coordinates[left].1.min(coordinates[right].1);
            let second = coordinates[left].1.max(coordinates[right].1);
            let Some(pair) = oriented_pair(first, second, development, subject_control) else {
                continue;
            };
            if pair.control_factor_octaves > best_octaves {
                continue;
            }
            let placed = place_activation(pair.determinant.clone(), grain)?;
            if placed.lower.is_zero() {
                continue;
            }
            let Ok((u_exponent, u_scale, separated_potential)) = least_power_of_two_separating(
                &target_potential,
                &strongest_competing_upper_face,
                &placed.lower,
            ) else {
                continue;
            };
            let address = (pair.first, pair.second);
            let replace = match &chosen {
                None => true,
                Some((standing, _, _, _, _)) => {
                    pair.control_factor_octaves < best_octaves
                        || (pair.control_factor_octaves == best_octaves
                            && address < (standing.first, standing.second))
                }
            };
            if replace {
                best_octaves = pair.control_factor_octaves;
                chosen = Some((pair, placed, u_exponent, u_scale, separated_potential));
            }
        }
    }
    let (pair, placed_activation, u_exponent, u_scale, separated_potential) =
        chosen.ok_or(CultivationDerivationError::NoAdmissiblePair)?;
    let strict_target_gap = &strongest_competing_upper_face - &target_potential;
    let t = pair.determinant.clone();
    let lower_development_delta = &u_scale * &placed_activation.lower;
    let development_delta = &u_scale * &t;
    // A is the forward constrained parameter map.  G_y = [1], G_x = [t / λ], so
    // G_x^-1 A^T G_y = [λ] exactly, including for negative λ exponents.
    let map = ExactRatMatrix::new(vec![vec![t.clone()]])?;
    let domain_metric_value = &t / &u_scale;
    let domain_metric = ExactRatMatrix::new(vec![vec![domain_metric_value.clone()]])?;
    let codomain_metric = ExactRatMatrix::new(vec![vec![Rat::from_integer(BigInt::one())]])?;
    let adjoint = map.metric_adjoint(&domain_metric, &codomain_metric)?;
    let perturbed_domain_metric =
        ExactRatMatrix::new(vec![vec![&domain_metric_value * rat_integer(2)]])?;
    let perturbed_adjoint = map.metric_adjoint(&perturbed_domain_metric, &codomain_metric)?;
    let bare_transpose = map.transpose()?;
    let metric_perturbation = perturbed_adjoint.subtract(&adjoint)?;
    let unit = [Rat::from_integer(BigInt::one())];
    let adjoint_defect =
        map.adjoint_defect(&adjoint, &domain_metric, &codomain_metric, &unit, &unit)?;
    let bare_transpose_defect = map.adjoint_defect(
        &bare_transpose,
        &domain_metric,
        &codomain_metric,
        &unit,
        &unit,
    )?;
    let factorization = map.factorization()?;
    // The cultivated transport defect is the supported target row `u v^T`, not the raw
    // development outer product: its left factor is λ and its right factor is the annihilator.
    let sparse_defect = ExactRatMatrix::new(vec![vec![
        &u_scale * &pair.control_annihilator[0],
        &u_scale * &pair.control_annihilator[1],
    ]])?;
    let sparse_defect_factorization = sparse_defect.factorization()?;
    let reconstruction_fibre = map.preimage_fibre(&[development_delta.clone()])?;

    let mut work = ExactWork::nothing();
    for value in [
        &pair.determinant,
        &placed_activation.lower,
        &placed_activation.upper,
        &u_scale,
        &development_delta,
        &lower_development_delta,
        &separated_potential,
    ] {
        work.wrote(value);
    }
    work.multiplied(5);
    work.added(3);
    work = work
        .then(&factorization.work)
        .then(&sparse_defect_factorization.work);
    let adjoint_on_unit = adjoint.apply(&unit)?[0].clone();

    Ok(CultivationDerivation {
        target_vocabulary,
        pair,
        target_potential,
        strongest_competing_upper_face,
        strict_target_gap,
        u_exponent,
        u_scale,
        placed_activation,
        lower_development_delta,
        development_delta,
        separated_potential,
        map,
        domain_metric,
        codomain_metric,
        adjoint,
        adjoint_defect,
        adjoint_on_unit,
        bare_transpose_defect,
        perturbed_adjoint,
        metric_perturbation,
        rank: factorization.rank,
        factorization,
        sparse_defect,
        sparse_defect_factorization,
        reconstruction_fibre,
        work,
    })
}

/// Alias kept short for callers whose deed already names the W3 context.
pub fn derive(
    development: &HiddenPointSection,
    subject_control: &HiddenPointSection,
    target_potential: Rat,
    strongest_competing_upper_face: Rat,
) -> Result<CultivationDerivation, CultivationDerivationError> {
    derive_w3_return(
        development,
        subject_control,
        target_potential,
        strongest_competing_upper_face,
    )
}

fn dyadic_parts(value: &Rat) -> Option<(BigInt, i32)> {
    let denominator = value.denom();
    let shift = denominator.bits().checked_sub(1)?;
    if denominator != &(BigInt::one() << shift as usize) {
        return None;
    }
    if value.is_zero() {
        return Some((BigInt::zero(), 0));
    }
    let trailing = value
        .numer()
        .magnitude()
        .trailing_zeros()?
        .min(i32::MAX as u64);
    let denominator_shift = i32::try_from(shift).ok()?;
    let numerator_shift = i32::try_from(trailing).ok()?;
    let exponent = numerator_shift.checked_sub(denominator_shift)?;
    Some((value.numer() >> trailing as usize, exponent))
}

fn checked_exponent_delta(
    exponent: i32,
    common: i32,
    index: usize,
) -> Result<i32, CultivationDerivationError> {
    exponent
        .checked_sub(common)
        .ok_or(CultivationDerivationError::AlignmentOverflow { index })
}

/// Convert exact dyadic rational coordinates into the existing dense material carrier.
///
/// This is intentionally separate from [`derive_w3_return`].  It retains zero positions (the
/// support), chooses the lowest exact exponent, and shifts integer significands without rounding.
pub fn to_aligned_material(values: &[Rat]) -> Result<AlignedMaterial, CultivationDerivationError> {
    let parts: Vec<Option<(BigInt, i32)>> = values.iter().map(dyadic_parts).collect();
    for (index, part) in parts.iter().enumerate() {
        if !values[index].is_zero() && part.is_none() {
            return Err(CultivationDerivationError::NonDyadic { index });
        }
    }
    // Zero is exact at every exponent. Letting its normalized denominator (`1`, exponent `0`)
    // participate would rebase a sparse power-of-two factor such as `[0, 8, 0]` from
    // `1·2^3` to `8·2^0`, wasting three carrier octaves for no mathematical reason.
    let common = values
        .iter()
        .zip(&parts)
        .filter_map(|(value, part)| (!value.is_zero()).then_some(part.as_ref()?.1))
        .min()
        .unwrap_or(0);
    let mut entries = Vec::with_capacity(values.len());
    let mut entry_octaves = 0u32;
    let mut negatives = 0u64;
    for (index, value) in values.iter().enumerate() {
        if value.is_zero() {
            entries.push(0);
            continue;
        }
        let (significand, exponent) = parts[index]
            .as_ref()
            .expect("nonzero values were checked above");
        let exponent_delta = checked_exponent_delta(*exponent, common, index)?;
        let shift = usize::try_from(exponent_delta)
            .map_err(|_| CultivationDerivationError::AlignmentOverflow { index })?;
        let integer = significand * (BigInt::one() << shift);
        let entry = integer
            .to_i64()
            .ok_or(CultivationDerivationError::AlignmentOverflow { index })?;
        if entry < 0 {
            negatives += 1;
        }
        entry_octaves = entry_octaves.max(entry.unsigned_abs().max(1).ilog2() + 1);
        entries.push(entry);
    }
    Ok(AlignedMaterial {
        entries,
        exponent: common,
        entry_octaves,
        negatives,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    #[test]
    fn first_nonzero_pair_annihilates_control_and_returns_exact_receipts() {
        let development = HiddenPointSection::new(vec![rat(1, 1), rat(2, 1), rat(5, 1)]);
        let control = HiddenPointSection::new(vec![rat(1, 1), rat(1, 1), rat(0, 1)]);
        let pair = first_pair(&development, &control).expect("non-collinear pair");
        assert_eq!((pair.first, pair.second), (0, 1));
        assert_eq!(pair.determinant, rat(1, 1));
        assert_eq!(pair.control_annihilator, [rat(-1, 1), rat(1, 1)]);
        let result = derive_w3_return_at_grain(
            &HiddenPointSection::new(vec![rat(2, 1), rat(1, 1)]),
            &HiddenPointSection::new(vec![rat(1, 1), rat(1, 1)]),
            rat(0, 1),
            rat(1, 1),
            0,
        )
        .expect("positive separation");
        assert_eq!(result.pair.control_annihilator, [rat(1, 1), rat(-1, 1)]);
        // The determinant is one, so strict separation over a unit gap needs 2^1.
        assert_eq!(result.u_exponent, 1);
        assert_eq!(result.adjoint_on_unit, result.u_scale);
        assert_eq!(result.adjoint_defect, Rat::zero());
        assert!(!result.bare_transpose_defect.is_zero());
        assert_ne!(result.perturbed_adjoint, result.adjoint);
        assert_eq!(result.rank, 1);
        assert_eq!(
            (result.sparse_defect.rows(), result.sparse_defect.columns()),
            (1, 2)
        );
        assert_eq!(result.sparse_defect_factorization.rank, 1);
        let fibre = result.reconstruction_fibre.as_ref().expect("fibre");
        assert_eq!(fibre.0, vec![result.u_scale.clone()]);
        assert!(fibre.1.is_empty());
        assert!(!result.work.entries_written.is_zero());
        let addressed = derive_w3_return_at_grain_with_target(
            &HiddenPointSection::new(vec![rat(2, 1), rat(1, 1)]),
            &HiddenPointSection::new(vec![rat(1, 1), rat(1, 1)]),
            rat(0, 1),
            rat(1, 1),
            0,
            17,
        )
        .expect("addressed return");
        let bytes = addressed
            .canonical_receipt_bytes()
            .expect("canonical bytes");
        assert!(!bytes.is_empty());
        assert_eq!(
            addressed.canonical_receipt_digest().expect("digest").len(),
            64
        );
        assert_eq!(addressed.target_vocabulary, 17);
    }

    #[test]
    fn least_power_of_two_is_strict_and_conversion_preserves_support_and_exponent() {
        let (exponent, scale, separated) =
            least_power_of_two_separating(&rat(0, 1), &rat(3, 1), &rat(1, 1)).expect("scale");
        assert_eq!(exponent, 2);
        assert_eq!(scale, rat(4, 1));
        assert_eq!(separated, rat(4, 1));
        let aligned =
            to_aligned_material(&[rat(0, 1), rat(1, 4), rat(-3, 2)]).expect("dyadic alignment");
        assert_eq!(aligned.entries, vec![0, 1, -6]);
        assert_eq!(aligned.exponent, -2);
        assert_eq!(aligned.negatives, 1);
        let sparse_power =
            to_aligned_material(&[rat(0, 1), rat(8, 1), rat(0, 1)]).expect("sparse power");
        assert_eq!(sparse_power.entries, vec![0, 1, 0]);
        assert_eq!(sparse_power.exponent, 3);
        assert_eq!(sparse_power.entry_octaves, 1);
        assert!(matches!(
            to_aligned_material(&[rat(1, 3)]),
            Err(CultivationDerivationError::NonDyadic { index: 0 })
        ));

        let placed = place_activation(rat(3, 10), 2).expect("placed interval");
        assert_eq!(placed.lower, rat(1, 4));
        assert_eq!(placed.upper, rat(1, 2));
        let rounded = derive_w3_return_at_grain(
            &HiddenPointSection::new(vec![rat(3, 10), rat(0, 1)]),
            &HiddenPointSection::new(vec![rat(1, 1), rat(1, 1)]),
            rat(0, 1),
            rat(3, 4),
            2,
        )
        .expect("rounded strict return");
        assert_eq!(rounded.placed_activation.lower, rat(1, 4));
        assert_eq!(rounded.lower_development_delta, rat(1, 1));
    }

    #[test]
    fn exponent_common_overflow_is_refused_before_integer_conversion() {
        assert!(matches!(
            checked_exponent_delta(i32::MAX, i32::MIN, 4),
            Err(CultivationDerivationError::AlignmentOverflow { index: 4 })
        ));
    }
}
