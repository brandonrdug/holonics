//! Exact normalized kernel conduct through its derived independent modes.
//!
//! K = D E is certified by the standing rank-factorization owner. E carries both source mass
//! and weighted currents, so normalization happens after the complete contraction. The retained
//! summary contains no source-event sequence. These are exact algebraic construction/reference
//! owners; device placement uses the existing resident operator boundary.
use super::{ExactLinearError, ExactRatMatrix, ReceiverFactorization};
use crate::exact_work::ExactWork;
use num_traits::Signed;
use relational_geometry::Rat;
use std::sync::Arc;
use thiserror::Error;

#[derive(Debug)]
struct KernelModeCore {
    encoder: ExactRatMatrix,
    decoder: ExactRatMatrix,
}

/// An immutable, derived representation of the complete supplied query kernel.
#[derive(Clone, Debug)]
pub struct KernelModeReduction {
    core: Arc<KernelModeCore>,
}

/// One current in its actual modal frame. The first column is mass, followed by signed currents.
#[derive(Debug)]
pub struct KernelModeSummary {
    core: Arc<KernelModeCore>,
    moments: ExactRatMatrix,
}

/// A source action whose effect factors through the same encoding for every source vector.
#[derive(Debug)]
pub struct KernelModeAction {
    core: Arc<KernelModeCore>,
    action: ExactRatMatrix,
}

#[derive(Debug, Error)]
pub enum KernelModeError {
    #[error("kernel queries and source ports must be nonempty")]
    EmptyKernel,
    #[error("kernel, source masses and source-mass transport must be nonnegative in this chart")]
    NegativeMass,
    #[error("this receiver has no positive admitted mass")]
    NoPositiveMass,
    #[error("summary and operator use different modal frames")]
    ForeignFrame,
    #[error("the source action separates a fibre erased by this encoding")]
    SeparatedFibre {
        source_null: Vec<Rat>,
        returned: Vec<Rat>,
    },
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

impl KernelModeReduction {
    pub fn new(kernel: &ExactRatMatrix) -> Result<Self, KernelModeError> {
        if kernel.rows() == 0 || kernel.columns() == 0 {
            return Err(KernelModeError::EmptyKernel);
        }
        if kernel.entries().iter().any(Signed::is_negative) {
            return Err(KernelModeError::NegativeMass);
        }
        let factor = kernel.rank_factorization()?;
        Ok(Self {
            core: Arc::new(KernelModeCore {
                encoder: factor.right,
                decoder: factor.left,
            }),
        })
    }
    pub fn modes(&self) -> usize {
        self.core.encoder.rows()
    }
    pub fn encoder(&self) -> &ExactRatMatrix {
        &self.core.encoder
    }
    pub fn decoder(&self) -> &ExactRatMatrix {
        &self.core.decoder
    }

    /// Pack the supplied finite source measure and vector currents, then encode once.
    /// Real/imaginary components may be paired columns; neither phase component is scalarized.
    pub fn summarize(
        &self,
        weights: &[Rat],
        values: &ExactRatMatrix,
    ) -> Result<(KernelModeSummary, ExactWork), KernelModeError> {
        if weights.len() != self.core.encoder.columns() || values.rows() != weights.len() {
            return Err(ExactLinearError::ShapeMismatch.into());
        }
        if weights.iter().any(Signed::is_negative) {
            return Err(KernelModeError::NegativeMass);
        }
        let width = values
            .columns()
            .checked_add(1)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let mut work = ExactWork::nothing();
        let rows = weights
            .iter()
            .enumerate()
            .map(|(i, weight)| {
                let mut row = vec![weight.clone()];
                for value in values.row(i)? {
                    let current = weight * value;
                    work.multiplied(1);
                    work.wrote(&current);
                    row.push(current);
                }
                Ok(row)
            })
            .collect::<Result<Vec<_>, ExactLinearError>>()?;
        let packed = ExactRatMatrix::shaped(weights.len(), width, rows)?;
        let (moments, encoded_work) = self.core.encoder.multiply_with_work(&packed)?;
        Ok((
            KernelModeSummary {
                core: Arc::clone(&self.core),
                moments,
            },
            work.then(&encoded_work),
        ))
    }

    /// Read one admitted kernel query without expanding source interiors.
    pub fn read(
        &self,
        summary: &KernelModeSummary,
        query: usize,
    ) -> Result<(Vec<Rat>, ExactWork), KernelModeError> {
        if !Arc::ptr_eq(&self.core, &summary.core) {
            return Err(KernelModeError::ForeignFrame);
        }
        let row = ExactRatMatrix::shaped(
            1,
            self.modes(),
            vec![self.core.decoder.row(query)?.to_vec()],
        )?;
        let (received, mut work) = row.multiply_with_work(&summary.moments)?;
        let mass = received.get(0, 0)?;
        if !mass.is_positive() {
            return Err(KernelModeError::NoPositiveMass);
        }
        let current = received.row(0)?[1..]
            .iter()
            .map(|value| {
                let value = value / mass;
                work.divided(1);
                work.wrote(&value);
                value
            })
            .collect();
        Ok((current, work))
    }

    /// Construct U with U E = E T, or return the full source-null direction T exposes.
    /// This algebraic equality is distinct from a source law's measure/admissibility conditions.
    pub fn compile_source_action(
        &self,
        source_action: &ExactRatMatrix,
    ) -> Result<KernelModeAction, KernelModeError> {
        if source_action.entries().iter().any(Signed::is_negative) {
            return Err(KernelModeError::NegativeMass);
        }
        let target = self.core.encoder.multiply(source_action)?;
        match self.core.encoder.factor_receiver(&target)? {
            ReceiverFactorization::Factored(family) => Ok(KernelModeAction {
                core: Arc::clone(&self.core),
                action: family.particular,
            }),
            ReceiverFactorization::Obstructed {
                source_null,
                returned,
            } => Err(KernelModeError::SeparatedFibre {
                source_null,
                returned,
            }),
        }
    }
}

impl KernelModeSummary {
    pub fn moments(&self) -> &ExactRatMatrix {
        &self.moments
    }
    /// Transport signed value components while retaining the source mass column. This is
    /// the other linear leg of the same summary, including changes of feature/phase frame.
    pub fn transport_values(
        &mut self,
        value_map: &ExactRatMatrix,
    ) -> Result<ExactWork, KernelModeError> {
        let before = self.moments.columns() - 1;
        if value_map.columns() != before {
            return Err(ExactLinearError::ShapeMismatch.into());
        }
        let after = value_map
            .rows()
            .checked_add(1)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let mut rows = vec![vec![Rat::from_integer(1.into())]; 1];
        rows[0].extend((0..before).map(|_| Rat::from_integer(0.into())));
        for row in value_map.to_rows() {
            let mut mapped = vec![Rat::from_integer(0.into())];
            mapped.extend(row);
            rows.push(mapped);
        }
        let lifted = ExactRatMatrix::shaped(after, before + 1, rows)?.transpose()?;
        let (next, work) = self.moments.multiply_with_work(&lifted)?;
        self.moments = next;
        Ok(work)
    }
    /// Stage the changed modal current before replacing this continuing summary.
    pub fn transport(&mut self, action: &KernelModeAction) -> Result<ExactWork, KernelModeError> {
        if !Arc::ptr_eq(&self.core, &action.core) {
            return Err(KernelModeError::ForeignFrame);
        }
        let (next, work) = action.action.multiply_with_work(&self.moments)?;
        self.moments = next;
        Ok(work)
    }
}

impl KernelModeAction {
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.action
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};
    fn q(n: i64) -> Rat {
        Rat::from_integer(n.into())
    }
    fn m(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|r| r.iter().map(|v| q(*v)).collect())
                .collect(),
        )
        .unwrap()
    }
    #[test]
    fn repeated_modes_retain_mass_and_signed_current() {
        let reduction = KernelModeReduction::new(&m(&[&[1, 1, 2], &[2, 2, 1]])).unwrap();
        assert_eq!(reduction.modes(), 2);
        let (mut summary, _) = reduction
            .summarize(&[q(1), q(3), q(2)], &m(&[&[1, -1], &[3, 1], &[2, -2]]))
            .unwrap();
        assert_eq!(
            reduction.read(&summary, 0).unwrap().0,
            vec![q(9) / q(4), -q(3) / q(4)]
        );
        // Deleting a repeated kernel column rather than aggregating its mass changes the result.
        let wrong = KernelModeReduction::new(&m(&[&[1, 2], &[2, 1]])).unwrap();
        let (lost, _) = wrong
            .summarize(&[q(1), q(2)], &m(&[&[1, -1], &[2, -2]]))
            .unwrap();
        assert_ne!(
            wrong.read(&lost, 0).unwrap().0,
            reduction.read(&summary, 0).unwrap().0
        );
        summary.transport_values(&m(&[&[0, -1], &[1, 0]])).unwrap();
        assert_eq!(
            reduction.read(&summary, 0).unwrap().0,
            vec![q(3) / q(4), q(9) / q(4)]
        );
    }
    #[test]
    fn source_transport_descends_or_exhibits_the_separating_fibre() {
        let reduction = KernelModeReduction::new(&m(&[&[1, 1, 0], &[0, 0, 1]])).unwrap();
        let scale = m(&[&[2, 0, 0], &[0, 2, 0], &[0, 0, 3]]);
        let action = reduction.compile_source_action(&scale).unwrap();
        assert_eq!(
            action.matrix().multiply(reduction.encoder()).unwrap(),
            reduction.encoder().multiply(&scale).unwrap()
        );
        let (mut summary, _) = reduction
            .summarize(&[q(1), q(1), q(1)], &m(&[&[1], &[3], &[4]]))
            .unwrap();
        summary.transport(&action).unwrap();
        assert_eq!(reduction.read(&summary, 0).unwrap().0, vec![q(2)]);
        let separating = m(&[&[1, 0, 0], &[0, 2, 0], &[0, 0, 1]]);
        let Err(KernelModeError::SeparatedFibre {
            source_null,
            returned,
        }) = reduction.compile_source_action(&separating)
        else {
            panic!("missing separator")
        };
        assert!(
            reduction
                .encoder()
                .apply(&source_null)
                .unwrap()
                .iter()
                .all(Zero::is_zero)
        );
        assert_eq!(
            reduction
                .encoder()
                .multiply(&separating)
                .unwrap()
                .apply(&source_null)
                .unwrap(),
            returned
        );
        assert!(returned.iter().any(|v| !v.is_zero()));
    }
    #[test]
    fn zero_mass_and_foreign_frames_are_explicit() {
        let kernel = m(&[&[1, 0], &[0, 1]]);
        let reduction = KernelModeReduction::new(&kernel).unwrap();
        let other = KernelModeReduction::new(&kernel).unwrap();
        let (mut summary, _) = reduction
            .summarize(&[Rat::one(), Rat::zero()], &m(&[&[3], &[4]]))
            .unwrap();
        assert!(matches!(
            reduction.read(&summary, 1),
            Err(KernelModeError::NoPositiveMass)
        ));
        assert!(matches!(
            other.read(&summary, 0),
            Err(KernelModeError::ForeignFrame)
        ));
        let foreign = other
            .compile_source_action(&ExactRatMatrix::identity(2).unwrap())
            .unwrap();
        let before = summary.moments().to_rows();
        assert!(matches!(
            summary.transport(&foreign),
            Err(KernelModeError::ForeignFrame)
        ));
        assert_eq!(summary.moments().to_rows(), before);
    }
}
