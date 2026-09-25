//! **The dynamical zeta of the epoch return map.**
//!
//! [definition] Lean `Aeon/Production/Zeta` and the aeon record (A8). A finite **return map** is a
//! square exact matrix `M`, or the navigators' machine of sites
//! ([`crate::navigator::trace::Machine`], block-diagonal companions). Its **transfer determinant**
//! is `det(1 − T·M)` (Mathlib `Matrix.charpolyRev`), its **cycle counts** are `N_n = tr(Mⁿ)`, and its
//! **dynamical zeta** is `ζ(T) = 1/det(1 − T·M)`. The zeta is the exponential of the cycle series,
//!
//! ```text
//! 1/det(1 − T·M) = exp Σ_(n≥1) N_n Tⁿ/n
//! ```
//!
//! coefficientwise over ℚ (Lean `zeta_eq_exp`, through `transferDet_derivative`, Newton's
//! identities). [`zeta`] is the exact reciprocal series of the transfer determinant and
//! [`cycle_exponential`] the exponential of the cycle series, from `k·E_k = Σ_(j=1..k) N_j E_(k−j)`;
//! both are exact power series through a declared degree. For the machine the transfer
//! determinant is `∏ (1 − a_g T + q_g T²)` and the cycle counts are the summed site trace
//! sequences, so its conserved trace faces are its reciprocal zeta (`machine_zeta`).

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::aeon::AeonError;
use crate::navigator::trace::Machine;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;

/// [definition] **A finite return map**: an exact square matrix, or the navigators' machine of
/// sites, read through the same two faces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReturnMap {
    Matrix(ExactRatMatrix),
    Machine(Machine),
}

impl ReturnMap {
    /// **The transfer determinant** `det(1 − T·M)`, lowest power first. For a matrix it is the
    /// characteristic polynomial `det(x·1 − M)` read backwards (`T^d χ(1/T)`, Mathlib
    /// `Matrix.charpolyRev`);
    /// for the machine it is its product of site factors (`machine_charpolyRev`).
    pub fn transfer_determinant(&self) -> Result<Vec<Rat>, AeonError> {
        match self {
            Self::Matrix(matrix) => {
                let characteristic = matrix.characteristic_polynomial()?;
                let mut coefficients = characteristic.coefficients().to_vec();
                coefficients.reverse();
                Ok(coefficients)
            }
            Self::Machine(machine) => Ok(machine.transfer_determinant()),
        }
    }

    /// **The cycle counts** `N_n = tr(Mⁿ)` for `n = 0, …, degree` (Lean `machine_cycle_count` for
    /// the machine, whose counts are its summed site trace sequences).
    pub fn cycle_counts(&self, degree: usize) -> Result<Vec<Rat>, AeonError> {
        match self {
            Self::Matrix(matrix) => {
                if !matrix.is_square() {
                    return Err(AeonError::Shape {
                        what: "square return map",
                        expected: matrix.rows(),
                        found: matrix.columns(),
                    });
                }
                let mut power = ExactRatMatrix::identity(matrix.rows())?;
                let mut counts = Vec::with_capacity(degree + 1);
                for _ in 0..=degree {
                    let trace: Rat = (0..matrix.rows())
                        .map(|index| power.get(index, index).cloned())
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .sum();
                    counts.push(trace);
                    power = power.multiply(matrix)?;
                }
                Ok(counts)
            }
            Self::Machine(machine) => Ok(machine.trace_sequence(degree)),
        }
    }
}

/// [definition] **The dynamical zeta** `1/det(1 − T·M)` through `T^degree`: the exact reciprocal
/// series of the transfer determinant, `Z_0 = 1/D_0`, `Z_k = −(Σ_(j=1..k) D_j Z_(k−j))/D_0`.
pub fn zeta(return_map: &ReturnMap, degree: usize) -> Result<Vec<Rat>, AeonError> {
    let transfer = return_map.transfer_determinant()?;
    let constant = transfer.first().cloned().unwrap_or_else(Rat::zero);
    if !constant.is_one() {
        return Err(AeonError::NotAUnitSeries);
    }
    let mut series: Vec<Rat> = Vec::with_capacity(degree + 1);
    series.push(Rat::one());
    for k in 1..=degree {
        let mut term = Rat::zero();
        for (j, coefficient) in transfer.iter().enumerate().take(k + 1).skip(1) {
            term -= coefficient * &series[k - j];
        }
        series.push(term);
    }
    Ok(series)
}

/// [definition] **The exponential of the cycle series** `exp Σ_(n≥1) N_n Tⁿ/n` through `T^degree`:
/// `E_0 = 1`, `k·E_k = Σ_(j=1..k) N_j E_(k−j)`. Lean `cycleLog`, `(PowerSeries.exp ℚ).subst`.
pub fn cycle_exponential(return_map: &ReturnMap, degree: usize) -> Result<Vec<Rat>, AeonError> {
    let counts = return_map.cycle_counts(degree)?;
    let mut series: Vec<Rat> = Vec::with_capacity(degree + 1);
    series.push(Rat::one());
    for k in 1..=degree {
        let mut term = Rat::zero();
        for j in 1..=k {
            term += &counts[j] * &series[k - j];
        }
        series.push(term / Rat::from_integer(BigInt::from(k)));
    }
    Ok(series)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::navigator::trace::SiteFactor;
    use crate::ratio::linear::vector::integer_matrix;
    use crate::ratio::{integer, rat};

    /// **The dynamical zeta is the exponential of the cycle series**:
    /// `1/det(1 − T·M) = exp Σ tr(Mⁿ) Tⁿ/n` coefficientwise, for integral and rational return
    /// maps, singular or not. Lean `Zeta.zeta_eq_exp`, `transferDet_derivative`.
    #[test]
    fn the_zeta_is_the_exponential_of_the_cycle_series() {
        let maps = [
            integer_matrix(&[&[1, 1], &[1, 0]]).unwrap(),
            integer_matrix(&[&[0, 1, 1], &[1, 0, 0], &[2, 0, 0]]).unwrap(),
            ExactRatMatrix::new(vec![
                vec![rat(1, 2), integer(0), rat(-3, 4)],
                vec![integer(2), rat(1, 3), integer(1)],
                vec![integer(0), rat(5, 2), integer(-1)],
            ])
            .unwrap(),
        ];
        for matrix in maps {
            let map = ReturnMap::Matrix(matrix);
            assert_eq!(
                zeta(&map, 12).unwrap(),
                cycle_exponential(&map, 12).unwrap()
            );
        }
    }

    /// **The machine's conserved trace faces are its reciprocal zeta.** The block-diagonal
    /// companions of the sites have the machine's transfer determinant `∏ (1 − a_g T + q_g T²)`
    /// and its summed trace sequences as cycle counts, and the machine's zeta is the exponential
    /// of those counts. Lean `Zeta.machine_charpolyRev`, `machine_cycle_count`, `machine_zeta`.
    #[test]
    fn the_machine_zeta_is_its_trace_faces() {
        let sites = vec![
            SiteFactor::new(integer(3), integer(2)),
            SiteFactor::new(integer(-1), integer(5)),
            SiteFactor::new(rat(1, 2), rat(3, 4)),
        ];
        let mut rows = vec![vec![Rat::zero(); 6]; 6];
        for (index, site) in sites.iter().enumerate() {
            let companion = site.companion();
            for row in 0..2 {
                for column in 0..2 {
                    rows[2 * index + row][2 * index + column] = companion[row][column].clone();
                }
            }
        }
        let blocks = ReturnMap::Matrix(ExactRatMatrix::new(rows).unwrap());
        let machine = ReturnMap::Machine(Machine::new(sites));
        assert_eq!(
            blocks.transfer_determinant().unwrap(),
            machine.transfer_determinant().unwrap()
        );
        assert_eq!(
            blocks.cycle_counts(9).unwrap(),
            machine.cycle_counts(9).unwrap()
        );
        assert_eq!(
            zeta(&machine, 9).unwrap(),
            cycle_exponential(&machine, 9).unwrap()
        );
    }
}
