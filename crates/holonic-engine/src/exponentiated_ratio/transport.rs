//! Normalized kernel transport and its complete differential in the log-potential chart.
//!
//! K_ij = exp(s_ij), a_ij = K_ij / sum_j K_ij, Y = a V. Rational positive K is
//! the exact log-rational specialization of softmax. Zero entries declare absent contacts.
//! The derivative includes both changing participation and changing transported current.
//! K is supplied positive material. The real log-potential is defined implicitly by the
//! normalized mode E'=E, E(0)=1, E(s)=K; this calculation does not evaluate/store a logarithm
//! or claim that a learner generated K. Its constraint source is retained by this chart.
//! These are reusable exact reference operators; they do not insert a host loop into HNN.

use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalizedKernel {
    kernel: ExactRatMatrix,
    mass: Vec<Rat>,
}

#[derive(Debug, Error)]
pub enum NormalizedKernelError {
    #[error("normalized transport requires nonempty ports and nonnegative kernel entries")]
    InvalidKernel,
    #[error("normalized transport row {0} has no participating mass")]
    EmptyRow(usize),
    #[error("the operand does not have this kernel's port dimensions")]
    Shape,
    #[error(
        "a material step requires a positive rate and must stay in the present positive support"
    )]
    MaterialStep,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

impl NormalizedKernel {
    pub fn new(kernel: ExactRatMatrix) -> Result<Self, NormalizedKernelError> {
        if kernel.rows() == 0
            || kernel.columns() == 0
            || kernel.entries().iter().any(Signed::is_negative)
        {
            return Err(NormalizedKernelError::InvalidKernel);
        }
        let mut mass = Vec::with_capacity(kernel.rows());
        for row in 0..kernel.rows() {
            let total: Rat = kernel.row(row)?.iter().cloned().sum();
            if total.is_zero() {
                return Err(NormalizedKernelError::EmptyRow(row));
            }
            mass.push(total);
        }
        Ok(Self { kernel, mass })
    }

    /// Rows (odds, 1) realize sigmoid(log odds), with the binary complement retained.
    pub fn binary(odds: &[Rat]) -> Result<Self, NormalizedKernelError> {
        if odds.iter().any(|x| !x.is_positive()) {
            return Err(NormalizedKernelError::InvalidKernel);
        }
        Self::new(ExactRatMatrix::new(
            odds.iter().map(|x| vec![x.clone(), Rat::one()]).collect(),
        )?)
    }

    pub fn kernel(&self) -> &ExactRatMatrix {
        &self.kernel
    }

    pub fn probabilities(&self) -> Result<ExactRatMatrix, NormalizedKernelError> {
        Ok(ExactRatMatrix::new(
            (0..self.kernel.rows())
                .map(|i| {
                    self.kernel
                        .row(i)
                        .expect("valid row")
                        .iter()
                        .map(|x| x / &self.mass[i])
                        .collect()
                })
                .collect(),
        )?)
    }

    /// Transport a complete vector-valued section; columns are its retained current axes.
    pub fn apply(&self, values: &ExactRatMatrix) -> Result<ExactRatMatrix, NormalizedKernelError> {
        if values.rows() != self.kernel.columns() || values.columns() == 0 {
            return Err(NormalizedKernelError::Shape);
        }
        Ok(self.probabilities()?.multiply(values)?)
    }

    /// dY = a dV + a (ds - E_a ds) V. ds is the log-kernel differential.
    /// At absent contacts this derivative is zero; admitting a new contact is a different map.
    pub fn differential(
        &self,
        values: &ExactRatMatrix,
        log_kernel_delta: &ExactRatMatrix,
        value_delta: &ExactRatMatrix,
    ) -> Result<ExactRatMatrix, NormalizedKernelError> {
        if values.rows() != self.kernel.columns()
            || values.columns() == 0
            || log_kernel_delta.rows() != self.kernel.rows()
            || log_kernel_delta.columns() != self.kernel.columns()
            || value_delta.rows() != values.rows()
            || value_delta.columns() != values.columns()
        {
            return Err(NormalizedKernelError::Shape);
        }
        let a = self.probabilities()?;
        let mut result = self.apply(value_delta)?.to_rows();
        for i in 0..a.rows() {
            let mean: Rat = (0..a.columns())
                .map(|j| a.get(i, j).unwrap() * log_kernel_delta.get(i, j).unwrap())
                .sum();
            for j in 0..a.columns() {
                let weight = a.get(i, j)? * (log_kernel_delta.get(i, j)? - &mean);
                for (c, out) in result[i].iter_mut().enumerate() {
                    *out += &weight * values.get(j, c)?;
                }
            }
        }
        Ok(ExactRatMatrix::new(result)?)
    }

    /// Pull back a complete output covector to log-potentials and value currents.
    pub fn pullback(
        &self,
        values: &ExactRatMatrix,
        output_covector: &ExactRatMatrix,
    ) -> Result<(ExactRatMatrix, ExactRatMatrix), NormalizedKernelError> {
        let output = self.apply(values)?;
        if output_covector.rows() != output.rows() || output_covector.columns() != output.columns()
        {
            return Err(NormalizedKernelError::Shape);
        }
        let a = self.probabilities()?;
        let mut ds = vec![vec![Rat::zero(); a.columns()]; a.rows()];
        let mut dv = vec![vec![Rat::zero(); values.columns()]; values.rows()];
        for i in 0..a.rows() {
            for j in 0..a.columns() {
                for c in 0..values.columns() {
                    let q = output_covector.get(i, c)?;
                    ds[i][j] += a.get(i, j)? * q * (values.get(j, c)? - output.get(i, c)?);
                    dv[j][c] += a.get(i, j)? * q;
                }
            }
        }
        Ok((ExactRatMatrix::new(ds)?, ExactRatMatrix::new(dv)?))
    }

    pub fn squared_discrepancy(
        &self,
        values: &ExactRatMatrix,
        target: &ExactRatMatrix,
    ) -> Result<Rat, NormalizedKernelError> {
        let output = self.apply(values)?;
        if output.rows() != target.rows() || output.columns() != target.columns() {
            return Err(NormalizedKernelError::Shape);
        }
        Ok(output
            .entries()
            .iter()
            .zip(target.entries())
            .map(|(x, y)| {
                let d = x - y;
                &d * &d
            })
            .sum::<Rat>()
            / Rat::from_integer(2.into()))
    }

    /// One declared Euclidean material step on positive K for half squared receiver error.
    /// This returns the changed operator. It is not a claim of global convergence or a new
    /// incidence law; no zero-support edge is opened and no step size is chosen internally.
    pub fn fit_step(
        &self,
        values: &ExactRatMatrix,
        target: &ExactRatMatrix,
        rate: &Rat,
    ) -> Result<Self, NormalizedKernelError> {
        if !rate.is_positive() {
            return Err(NormalizedKernelError::MaterialStep);
        }
        let output = self.apply(values)?;
        if output.rows() != target.rows() || output.columns() != target.columns() {
            return Err(NormalizedKernelError::Shape);
        }
        let delta = ExactRatMatrix::new(
            (0..output.rows())
                .map(|i| {
                    output
                        .row(i)
                        .unwrap()
                        .iter()
                        .zip(target.row(i).unwrap())
                        .map(|(a, b)| a - b)
                        .collect()
                })
                .collect(),
        )?;
        let (ds, _) = self.pullback(values, &delta)?;
        let mut changed = self.kernel.to_rows();
        for i in 0..self.kernel.rows() {
            for j in 0..self.kernel.columns() {
                let k = self.kernel.get(i, j)?;
                if !k.is_zero() {
                    changed[i][j] -= rate * ds.get(i, j)? / k;
                    if !changed[i][j].is_positive() {
                        return Err(NormalizedKernelError::MaterialStep);
                    }
                }
            }
        }
        Self::new(ExactRatMatrix::new(changed)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn m(v: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            v.iter()
                .map(|r| r.iter().map(|x| Rat::from_integer((*x).into())).collect())
                .collect(),
        )
        .unwrap()
    }
    fn pairing(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Rat {
        a.entries()
            .iter()
            .zip(b.entries())
            .map(|(a, b)| a * b)
            .sum()
    }

    #[test]
    fn binary_sigmoid_and_its_log_potential_derivative() {
        let k = NormalizedKernel::binary(&[Rat::one(), Rat::from_integer(3.into())]).unwrap();
        let v = m(&[&[1], &[0]]);
        let y = k.apply(&v).unwrap();
        assert_eq!(y.get(0, 0).unwrap(), &Rat::new(1.into(), 2.into()));
        assert_eq!(y.get(1, 0).unwrap(), &Rat::new(3.into(), 4.into()));
        let d = k
            .differential(&v, &m(&[&[1, 0], &[1, 0]]), &m(&[&[0], &[0]]))
            .unwrap();
        for i in 0..2 {
            let p = y.get(i, 0).unwrap();
            assert_eq!(d.get(i, 0).unwrap(), &(p * (Rat::one() - p)));
        }
    }

    #[test]
    fn complete_tangent_and_pullback_are_dual_and_keep_the_gauge_null() {
        let k = NormalizedKernel::new(m(&[&[1, 3, 0], &[2, 1, 2]])).unwrap();
        let v = m(&[&[1, -1], &[3, 2], &[-2, 1]]);
        let ds = m(&[&[1, -2, 9], &[2, 0, -1]]);
        let dv = m(&[&[2, 0], &[-1, 3], &[1, -2]]);
        let q = m(&[&[2, -1], &[1, 3]]);
        let dy = k.differential(&v, &ds, &dv).unwrap();
        let (s, x) = k.pullback(&v, &q).unwrap();
        assert_eq!(pairing(&q, &dy), pairing(&s, &ds) + pairing(&x, &dv));
        assert!(
            k.differential(
                &v,
                &m(&[&[7, 7, 7], &[-2, -2, -2]]),
                &m(&[&[0, 0], &[0, 0], &[0, 0]])
            )
            .unwrap()
            .entries()
            .iter()
            .all(Zero::is_zero)
        );
        assert!(s.get(0, 2).unwrap().is_zero());
        for i in 0..s.rows() {
            assert!(s.row(i).unwrap().iter().cloned().sum::<Rat>().is_zero());
        }
    }

    #[test]
    fn a_material_step_changes_the_output_and_reduces_the_declared_error() {
        let k = NormalizedKernel::new(m(&[&[1, 1]])).unwrap();
        let v = m(&[&[1, 0], &[0, 1]]);
        let target = ExactRatMatrix::new(vec![vec![
            Rat::new(1.into(), 4.into()),
            Rat::new(3.into(), 4.into()),
        ]])
        .unwrap();
        let next = k.fit_step(&v, &target, &Rat::one()).unwrap();
        assert!(
            next.squared_discrepancy(&v, &target).unwrap()
                < k.squared_discrepancy(&v, &target).unwrap()
        );
        assert_eq!(
            next.apply(&v).unwrap().get(0, 0).unwrap(),
            &Rat::new(7.into(), 16.into())
        );
        assert!(
            k.fit_step(&v, &target, &Rat::from_integer(16.into()))
                .is_err()
        );
    }
}
