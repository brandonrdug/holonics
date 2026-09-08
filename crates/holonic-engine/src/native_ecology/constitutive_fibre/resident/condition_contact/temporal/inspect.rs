//! Cold exact observation of a retained temporal condition standing.
//!
//! The native report keeps the integer Gram and cross moment used by the contact.  This
//! decoder reconstructs the exact rational response for inspection only; it never supplies a
//! current to a native passage and never chooses a member of the affine preimage fibre.

use super::*;
use crate::{
    dimensional_wave::ExactComplexWaveCurrent,
    native_ecology::constitutive_fibre::ConstitutiveFibreError,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{Signed, Zero};

/// Exact cold reading of one temporal condition standing.
///
/// Initial standings retain only their supplied rational response.  Contact standings also
/// retain the exact cold operands from the native report tail, allowing the response solve to
/// be checked without reading or replaying a native current.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentTemporalConditionReading {
    pub response: Vec<ExactComplexWaveCurrent>,
    pub prior: Option<Vec<ExactComplexWaveCurrent>>,
    pub gram: Option<Vec<Vec<Rat>>>,
    pub raw_xy: Option<Vec<ExactComplexWaveCurrent>>,
    pub px: Option<Rat>,
    pub py: Option<Rat>,
    pub cden: Option<Rat>,
}

impl ResidentTemporalConditionReading {
    pub fn response(&self) -> &[ExactComplexWaveCurrent] {
        &self.response
    }

    pub fn prior(&self) -> Option<&[ExactComplexWaveCurrent]> {
        self.prior.as_deref()
    }
}

fn uncertain() -> ConstitutiveFibreError {
    ConstitutiveFibreError::Uncertain
}

fn signed_wide(words: &[(i64, i64)], at: usize) -> Result<i128, ConstitutiveFibreError> {
    let lo = words
        .get(at.checked_mul(2).ok_or_else(uncertain)?)
        .ok_or_else(uncertain)?;
    let hi = words
        .get(
            at.checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or_else(uncertain)?,
        )
        .ok_or_else(uncertain)?;
    if lo.0 != lo.1 || hi.0 != hi.1 {
        return Err(uncertain());
    }
    Ok((((hi.0 as u64 as u128) << 64) | lo.0 as u64 as u128) as i128)
}

fn integer(value: i128) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn exact_initial(
    surface: &ResidentSurface<'_>,
    section: &ResidentSection<'_>,
    chart: &TemporalResponseChart,
) -> Result<Vec<ExactComplexWaveCurrent>, ConstitutiveFibreError> {
    let words = surface.read_out(section)?;
    let coordinates = chart.raw_extent.checked_mul(2).ok_or_else(uncertain)?;
    if section.rows() != 1
        || section.grain().0 != 0
        || words.len() != section.width()
        || words.len() <= coordinates
        || words.iter().any(|(lo, hi)| lo != hi)
    {
        return Err(uncertain());
    }
    let denominator = words.last().ok_or_else(uncertain)?.0;
    if denominator <= 0 {
        return Err(uncertain());
    }
    if words[coordinates..words.len() - 1]
        .iter()
        .any(|(value, _)| *value != 0)
    {
        return Err(uncertain());
    }
    let denominator = BigInt::from(denominator);
    Ok((0..chart.raw_extent)
        .map(|index| {
            ExactComplexWaveCurrent::new(
                Rat::new(words[2 * index].0.into(), denominator.clone()),
                Rat::new(words[2 * index + 1].0.into(), denominator.clone()),
            )
        })
        .collect())
}

fn realify(values: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    values
        .iter()
        .flat_map(|value| [value.real.clone(), value.imaginary.clone()])
        .collect()
}

fn complexify(values: &[Rat]) -> Vec<ExactComplexWaveCurrent> {
    values
        .chunks_exact(2)
        .map(|pair| ExactComplexWaveCurrent::new(pair[0].clone(), pair[1].clone()))
        .collect()
}

pub(super) fn solve_exact(
    mut matrix: Vec<Vec<Rat>>,
    mut rhs: Vec<Rat>,
) -> Result<Vec<Rat>, ConstitutiveFibreError> {
    let dimension = rhs.len();
    if dimension == 0
        || matrix.len() != dimension
        || matrix.iter().any(|row| row.len() != dimension)
    {
        return Err(uncertain());
    }
    for column in 0..dimension {
        let pivot = (column..dimension)
            .find(|row| !matrix[*row][column].is_zero())
            .ok_or_else(uncertain)?;
        if pivot != column {
            matrix.swap(pivot, column);
            rhs.swap(pivot, column);
        }
        let divisor = matrix[column][column].clone();
        for entry in &mut matrix[column][column..] {
            *entry /= divisor.clone();
        }
        rhs[column] /= divisor;
        for row in 0..dimension {
            if row == column || matrix[row][column].is_zero() {
                continue;
            }
            let factor = matrix[row][column].clone();
            for j in column..dimension {
                let value = matrix[column][j].clone();
                matrix[row][j] -= &factor * value;
            }
            let pivot_rhs = rhs[column].clone();
            rhs[row] -= factor * pivot_rhs;
        }
    }
    Ok(rhs)
}

struct ContactTail {
    gram: Vec<Vec<Rat>>,
    raw_xy: Vec<ExactComplexWaveCurrent>,
    px: Rat,
    py: Rat,
    cden: Rat,
}

fn contact_tail(
    surface: &ResidentSurface<'_>,
    standing: &TemporalStanding<'_>,
    chart: &TemporalResponseChart,
) -> Result<ContactTail, ConstitutiveFibreError> {
    let words = surface.read_out(&standing.section)?;
    let dimension = chart.raw_extent.checked_mul(2).ok_or_else(uncertain)?;
    let stride = dimension.checked_add(1).ok_or_else(uncertain)?;
    let matrix_count = dimension.checked_mul(dimension).ok_or_else(uncertain)?;
    let tail = stride.checked_mul(8).ok_or_else(uncertain)?;
    let total = tail
        .checked_add(matrix_count)
        .and_then(|n| n.checked_add(dimension))
        .and_then(|n| n.checked_add(3))
        .ok_or_else(uncertain)?;
    if standing.section.rows() != 1
        || standing.section.grain().0 != 0
        || words.len() != total.checked_mul(2).ok_or_else(uncertain)?
    {
        return Err(uncertain());
    }
    let gram = (0..dimension)
        .map(|row| {
            (0..dimension)
                .map(|column| signed_wide(&words, tail + row * dimension + column).map(integer))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let raw = (0..dimension)
        .map(|index| signed_wide(&words, tail + matrix_count + index).map(integer))
        .collect::<Result<Vec<_>, _>>()?;
    let raw_xy = complexify(&raw);
    let px = integer(signed_wide(&words, tail + matrix_count + dimension)?);
    let py = integer(signed_wide(&words, tail + matrix_count + dimension + 1)?);
    let cden = integer(signed_wide(&words, tail + matrix_count + dimension + 2)?);
    if !px.is_positive() || !py.is_positive() || !cden.is_positive() {
        return Err(uncertain());
    }
    Ok(ContactTail {
        gram,
        raw_xy,
        px,
        py,
        cden,
    })
}

fn decode_standing(
    surface: &ResidentSurface<'_>,
    standing: &TemporalStanding<'_>,
    chart: &TemporalResponseChart,
) -> Result<ResidentTemporalConditionReading, ConstitutiveFibreError> {
    match &standing.construction {
        TemporalConstruction::Initial(initial) => Ok(ResidentTemporalConditionReading {
            response: exact_initial(surface, initial, chart)?,
            prior: None,
            gram: None,
            raw_xy: None,
            px: None,
            py: None,
            cden: None,
        }),
        TemporalConstruction::Contact(prior) => {
            let previous = decode_standing(surface, prior, chart)?;
            let tail = contact_tail(surface, standing, chart)?;
            let dimension = chart.raw_extent.checked_mul(2).ok_or_else(uncertain)?;
            let prior_real = realify(&previous.response);
            let raw_real = realify(&tail.raw_xy);
            if prior_real.len() != dimension || raw_real.len() != dimension {
                return Err(uncertain());
            }
            let mut matrix = tail.gram.clone();
            let mut rhs = Vec::with_capacity(dimension);
            for (row, row_values) in matrix.iter_mut().enumerate() {
                if row_values.len() != dimension {
                    return Err(uncertain());
                }
                row_values[row] += &tail.cden;
                rhs.push(&tail.cden * &prior_real[row] + (&tail.px / &tail.py) * &raw_real[row]);
            }
            let response = complexify(&solve_exact(matrix, rhs)?);
            Ok(ResidentTemporalConditionReading {
                response,
                prior: Some(previous.response),
                gram: Some(tail.gram),
                raw_xy: Some(tail.raw_xy),
                px: Some(tail.px),
                py: Some(tail.py),
                cden: Some(tail.cden),
            })
        }
    }
}

impl<'c> ResidentTemporalConditionSnapshot<'c> {
    /// Read the exact temporal response from immutable standing and report tails.
    ///
    /// This is a cold observer.  It reads resident sections and performs rational arithmetic on
    /// the host, but its result cannot be supplied to a native current port by this API.
    pub fn inspect(
        &self,
        surface: &ResidentSurface<'c>,
    ) -> Result<ResidentTemporalConditionReading, ConstitutiveFibreError> {
        if !self.standing.section.belongs_to(surface) {
            return Err(ConstitutiveFibreError::Shape);
        }
        decode_standing(surface, &self.standing, &self.chart)
    }
}
