//! Positive source geometry with compatible cross-source rows and total target energy.
//! This is the fraction-free Schur return, using the same integer minor/division discipline
//! as `exact_linear`'s integral inverse. Zero pivots preserve the source kernel obligation.
use super::*;

#[derive(Debug, PartialEq, Eq)]
pub struct PositiveSourceEnergy {
    pub source_rank: usize,
    pub remaining_target_energy: Rat,
}
#[derive(Debug, Error, PartialEq, Eq)]
pub enum SourceEnergyError {
    #[error("source and cross-source shapes disagree")]
    Shape,
    #[error("the source form is not positive semidefinite")]
    NegativeSource,
    #[error("a cross-source row is nonzero on the source kernel")]
    SourceKernel,
    #[error("target energy cannot realize the supplied cross-source geometry")]
    TargetEnergy,
    #[error("fraction-free source elimination returned a non-exact division")]
    NonExactDivision,
}

pub fn positive_source_energy(
    form: &SymmetricForm,
    cross: &[Vec<Rat>],
    energy: &Rat,
) -> Result<PositiveSourceEnergy, SourceEnergyError> {
    let n = form.extent();
    if n == 0 || cross.iter().any(|r| r.len() != n) {
        return Err(SourceEnergyError::Shape);
    }
    if energy.is_negative() {
        return Err(SourceEnergyError::TargetEnergy);
    }
    let mut scale = BigInt::one();
    for v in form
        .entries
        .iter()
        .chain(cross.iter().flatten())
        .chain(std::iter::once(energy))
    {
        if &scale % v.denom() != BigInt::zero() {
            let mut a = scale.clone();
            let mut b = v.denom().clone();
            while !b.is_zero() {
                let r = &a % &b;
                a = b;
                b = r;
            }
            scale = scale / a * v.denom();
        }
    }
    let integer = |v: &Rat| v.numer() * (&scale / v.denom());
    let mut g: Vec<Vec<BigInt>> = (0..n)
        .map(|i| (0..n).map(|j| integer(form.at(i, j))).collect())
        .collect();
    let mut b: Vec<Vec<BigInt>> = cross
        .iter()
        .map(|r| r.iter().map(integer).collect())
        .collect();
    let mut remaining = integer(energy);
    let mut previous = BigInt::one();
    let mut rank = 0;
    let divide = |v: BigInt, d: &BigInt| {
        if &v % d != BigInt::zero() {
            Err(SourceEnergyError::NonExactDivision)
        } else {
            Ok(v / d)
        }
    };
    for k in 0..n {
        let pivot = g[k][k].clone();
        if pivot.is_negative() {
            return Err(SourceEnergyError::NegativeSource);
        }
        if pivot.is_zero() {
            if g[k][k + 1..].iter().any(|v| !v.is_zero()) {
                return Err(SourceEnergyError::NegativeSource);
            }
            if b.iter().any(|r| !r[k].is_zero()) {
                return Err(SourceEnergyError::SourceKernel);
            }
            continue;
        }
        let square: BigInt = b.iter().map(|r| &r[k] * &r[k]).sum();
        remaining = divide(&pivot * remaining - square, &previous)?;
        if remaining.is_negative() {
            return Err(SourceEnergyError::TargetEnergy);
        }
        for i in k + 1..n {
            for j in i..n {
                let value = divide(&pivot * &g[i][j] - &g[i][k] * &g[k][j], &previous)?;
                g[i][j] = value.clone();
                g[j][i] = value;
            }
        }
        for row in &mut b {
            for i in k + 1..n {
                row[i] = divide(&pivot * &row[i] - &row[k] * &g[k][i], &previous)?;
            }
            row[k] = BigInt::zero();
        }
        for i in k + 1..n {
            g[k][i] = BigInt::zero();
            g[i][k] = BigInt::zero();
        }
        previous = pivot;
        rank += 1;
    }
    Ok(PositiveSourceEnergy {
        source_rank: rank,
        remaining_target_energy: Rat::new(remaining, previous * scale),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn q(n: i64, d: i64) -> Rat {
        Rat::new(n.into(), d.into())
    }
    #[test]
    fn source_energy_returns_exact_schur_trace_and_preserves_zero_pivots() {
        let a = SymmetricForm::from_integers(&[vec![2, 1], vec![1, 2]]).unwrap();
        let r = positive_source_energy(
            &a,
            &[vec![q(1, 1), q(0, 1)], vec![q(0, 1), q(1, 1)]],
            &q(2, 1),
        )
        .unwrap();
        assert_eq!(r.source_rank, 2);
        assert_eq!(r.remaining_target_energy, q(2, 3));
        let a =
            SymmetricForm::from_rows(vec![vec![q(0, 1), q(0, 1)], vec![q(0, 1), q(2, 3)]]).unwrap();
        let r = positive_source_energy(&a, &[vec![q(0, 1), q(1, 1)]], &q(2, 1)).unwrap();
        assert_eq!(r.source_rank, 1);
        assert_eq!(r.remaining_target_energy, q(1, 2));
        let a = SymmetricForm::from_integers(&[vec![1, 1], vec![1, 1]]).unwrap();
        assert_eq!(
            positive_source_energy(&a, &[vec![q(1, 1), q(1, 1)]], &q(1, 1))
                .unwrap()
                .remaining_target_energy,
            q(0, 1)
        );
        assert_eq!(
            positive_source_energy(&a, &[vec![q(1, 1), q(-1, 1)]], &q(10, 1)),
            Err(SourceEnergyError::SourceKernel)
        );
        assert_eq!(
            positive_source_energy(&a, &[vec![q(1, 1), q(1, 1)]], &q(0, 1)),
            Err(SourceEnergyError::TargetEnergy)
        );
        let bad = SymmetricForm::from_integers(&[vec![0, 1], vec![1, 0]]).unwrap();
        assert_eq!(
            positive_source_energy(&bad, &[], &q(0, 1)),
            Err(SourceEnergyError::NegativeSource)
        );
    }

    #[test]
    fn integer_schur_energy_agrees_with_independent_orthogonal_source_projection() {
        // A finite exact control family, including dependent and zero source rows. The
        // independent receiver projects the original vectors, not their Schur recurrence.
        for seed in 0..16 {
            let x: Vec<Vec<Rat>> = (0..3)
                .map(|row| {
                    (0..4)
                        .map(|column| {
                            q(
                                ((seed + row * column + row) % 5) as i64 - 2,
                                (row + 1) as i64,
                            )
                        })
                        .collect()
                })
                .collect();
            let y: Vec<Vec<Rat>> = (0..2)
                .map(|row| {
                    (0..4)
                        .map(|column| q(((seed * column + row) % 5) as i64 - 2, 2))
                        .collect()
                })
                .collect();
            let dot = |a: &[Rat], b: &[Rat]| a.iter().zip(b).map(|(a, b)| a * b).sum::<Rat>();
            let g = SymmetricForm::from_rows(
                x.iter()
                    .map(|a| x.iter().map(|b| dot(a, b)).collect())
                    .collect(),
            )
            .unwrap();
            let cross: Vec<Vec<Rat>> = y
                .iter()
                .map(|a| x.iter().map(|b| dot(a, b)).collect())
                .collect();
            let energy: Rat = y.iter().map(|a| dot(a, a)).sum();
            let mut basis = Vec::<Vec<Rat>>::new();
            for row in &x {
                let mut r = row.clone();
                for b in &basis {
                    let gain = dot(&r, b) / dot(b, b);
                    for (a, v) in r.iter_mut().zip(b) {
                        *a -= &gain * v;
                    }
                }
                if r.iter().any(|v| !v.is_zero()) {
                    basis.push(r);
                }
            }
            let mut remainder = Rat::zero();
            for row in &y {
                let mut r = row.clone();
                for b in &basis {
                    let gain = dot(&r, b) / dot(b, b);
                    for (a, v) in r.iter_mut().zip(b) {
                        *a -= &gain * v;
                    }
                }
                remainder += dot(&r, &r);
            }
            let actual = positive_source_energy(&g, &cross, &energy).unwrap();
            assert_eq!(actual.source_rank, basis.len());
            assert_eq!(actual.remaining_target_energy, remainder);
        }
    }
}
