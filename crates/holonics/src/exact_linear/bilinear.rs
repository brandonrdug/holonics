//! Receiver-oriented bilinear actions using the shared exact matrix/preimage owners.
//! Product cores are immutable reusable material. Application fixes input ports and receiver;
//! reverse use is a preimage family, not an assertion that the operation is invertible.
//!
//! # Holonic tensor interaction
//!
//! In the declared port bases this owner evaluates `|C> = I (|A> tensor |B>)`,
//! or `C[o] = sum(i,j) I[o,i,j] A[i] B[j]`. `BilinearOperator` is the interaction
//! tensor; `BilinearProductCore` retains its factorized input contractions; and
//! `BilinearRealization` binds a receiver to that shared core. The caller supplies
//! the actual frame/contact interpretation of these coordinate ports.
//!
//! `apply` executes the interaction, `then_receiver` contracts its output with a
//! further linear map, `join_receivers` returns multiple faces of the same product,
//! and `then_fixed_right` composes another interaction at a fixed right-hand holon.
//! These are high-level operator compositions, not instructions to reconstruct
//! an occurrence ledger or expand the full tensor for each use. The resident
//! realization belongs to the existing native operator owners.
use super::{ExactLinearError, ExactRatMatrix, LinearMapFamily, ReceiverFactorization};
use num_traits::Zero;
use crate::geometry::Rat;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BilinearOperator {
    left_extent: usize,
    right_extent: usize,
    coefficients: ExactRatMatrix,
}
impl BilinearOperator {
    /// Columns are the ordered tensor chart (left i, right j), index i*right_extent+j.
    pub fn new(
        left_extent: usize,
        right_extent: usize,
        coefficients: ExactRatMatrix,
    ) -> Result<Self, ExactLinearError> {
        if coefficients.columns()
            != left_extent
                .checked_mul(right_extent)
                .ok_or(ExactLinearError::ExtentOverflow)?
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        Ok(Self {
            left_extent,
            right_extent,
            coefficients,
        })
    }
    pub fn coefficients(&self) -> &ExactRatMatrix {
        &self.coefficients
    }
    pub fn left_extent(&self) -> usize {
        self.left_extent
    }
    pub fn right_extent(&self) -> usize {
        self.right_extent
    }
    pub fn apply(&self, left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, ExactLinearError> {
        if left.len() != self.left_extent || right.len() != self.right_extent {
            return Err(ExactLinearError::ShapeMismatch);
        }
        self.coefficients.apply(
            &left
                .iter()
                .flat_map(|a| right.iter().map(move |b| a * b))
                .collect::<Vec<_>>(),
        )
    }

    /// The exact differential of the bilinear action.  The two input variations remain separate
    /// ports; the mixed product is the second-order remainder of a finite change.
    pub fn differential(
        &self,
        left: &[Rat],
        right: &[Rat],
        left_delta: &[Rat],
        right_delta: &[Rat],
    ) -> Result<Vec<Rat>, ExactLinearError> {
        if left.len() != self.left_extent
            || right.len() != self.right_extent
            || left_delta.len() != self.left_extent
            || right_delta.len() != self.right_extent
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut result = vec![Rat::zero(); self.coefficients.rows()];
        for output in 0..self.coefficients.rows() {
            for i in 0..self.left_extent {
                for j in 0..self.right_extent {
                    let coefficient = self.coefficients.get(output, i * self.right_extent + j)?;
                    result[output] += coefficient
                        * (left_delta[i].clone() * &right[j] + &left[i] * &right_delta[j]);
                }
            }
        }
        Ok(result)
    }

    /// Pull back an output covector through this bilinear action to the two input ports.
    /// The returned covectors are kept in their declared input coordinates; no metric or Riesz
    /// identification is silently applied.
    pub fn pullback(
        &self,
        left: &[Rat],
        right: &[Rat],
        output_covector: &[Rat],
    ) -> Result<(Vec<Rat>, Vec<Rat>), ExactLinearError> {
        if left.len() != self.left_extent
            || right.len() != self.right_extent
            || output_covector.len() != self.coefficients.rows()
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let product_covector = self.coefficients.transpose()?.apply(output_covector)?;
        product_pullback(
            left,
            right,
            &product_covector,
            self.left_extent,
            self.right_extent,
        )
    }
    /// Fix the right port. The resulting map returns the whole compatible left-source fibre
    /// through ExactRatMatrix::preimage_fibre; no distinguished inverse is introduced.
    pub fn left_section(&self, right: &[Rat]) -> Result<ExactRatMatrix, ExactLinearError> {
        if right.len() != self.right_extent {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let rows =
            (0..self.coefficients.rows())
                .map(|r| {
                    (0..self.left_extent)
                        .map(|i| {
                            (0..self.right_extent)
                                .map(|j| {
                                    Ok(self.coefficients.get(r, i * self.right_extent + j)?
                                        * &right[j])
                                })
                                .collect::<Result<Vec<Rat>, ExactLinearError>>()
                                .map(|v| v.into_iter().sum())
                        })
                        .collect::<Result<Vec<_>, ExactLinearError>>()
                })
                .collect::<Result<Vec<_>, ExactLinearError>>()?;
        ExactRatMatrix::shaped(self.coefficients.rows(), self.left_extent, rows)
    }
    /// Retain the complete parameter fibre for left = anchor + directions * theta at a
    /// fixed right port. Columns of directions share theta; independent marginal intervals
    /// must not replace them. Varying both ports requires the additional tensor consistency law.
    pub fn left_family_preimage(
        &self,
        right: &[Rat],
        anchor: &[Rat],
        directions: &ExactRatMatrix,
        observed: &[Rat],
    ) -> Result<Option<(Vec<Rat>, Vec<Vec<Rat>>)>, ExactLinearError> {
        let section = self.left_section(right)?;
        if directions.rows() != self.left_extent || observed.len() != self.coefficients.rows() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let baseline = section.apply(anchor)?;
        let residual = observed
            .iter()
            .zip(baseline)
            .map(|(v, b)| v - b)
            .collect::<Vec<_>>();
        section.multiply(directions)?.preimage_fibre(&residual)
    }

    pub fn swap_ports(&self) -> Result<Self, ExactLinearError> {
        let rows = (0..self.coefficients.rows())
            .map(|r| {
                (0..self.right_extent)
                    .flat_map(|j| {
                        (0..self.left_extent).map(move |i| {
                            self.coefficients.get(r, i * self.right_extent + j).cloned()
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(
            self.right_extent,
            self.left_extent,
            ExactRatMatrix::shaped(self.coefficients.rows(), self.coefficients.columns(), rows)?,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BilinearProductCore {
    left_forms: ExactRatMatrix,
    right_forms: ExactRatMatrix,
    tensor_image: ExactRatMatrix,
}
impl BilinearProductCore {
    pub fn new(
        left_forms: ExactRatMatrix,
        right_forms: ExactRatMatrix,
    ) -> Result<Self, ExactLinearError> {
        if left_forms.rows() != right_forms.rows() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let extent = left_forms
            .columns()
            .checked_mul(right_forms.columns())
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let rows = (0..left_forms.rows())
            .map(|r| {
                Ok(left_forms
                    .row(r)?
                    .iter()
                    .flat_map(|a| {
                        right_forms
                            .row(r)
                            .expect("matching checked row")
                            .iter()
                            .map(move |b| a * b)
                    })
                    .collect())
            })
            .collect::<Result<Vec<_>, ExactLinearError>>()?;
        let tensor_image = ExactRatMatrix::shaped(left_forms.rows(), extent, rows)?;
        Ok(Self {
            left_forms,
            right_forms,
            tensor_image,
        })
    }
    pub fn left_forms(&self) -> &ExactRatMatrix {
        &self.left_forms
    }
    pub fn right_forms(&self) -> &ExactRatMatrix {
        &self.right_forms
    }
    pub fn tensor_image(&self) -> &ExactRatMatrix {
        &self.tensor_image
    }
    pub fn products(&self) -> usize {
        self.left_forms.rows()
    }
    pub fn apply(&self, left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, ExactLinearError> {
        let a = self.left_forms.apply(left)?;
        let b = self.right_forms.apply(right)?;
        Ok(a.iter().zip(b).map(|(x, y)| x * y).collect())
    }
    /// First differential of the factorized product map. Callers comparing a finite change can
    /// obtain the separate mixed remainder by applying the same core to both input deltas.
    pub fn differential(
        &self,
        left: &[Rat],
        right: &[Rat],
        left_delta: &[Rat],
        right_delta: &[Rat],
    ) -> Result<Vec<Rat>, ExactLinearError> {
        let a = self.left_forms.apply(left)?;
        let b = self.right_forms.apply(right)?;
        let da = self.left_forms.apply(left_delta)?;
        let db = self.right_forms.apply(right_delta)?;
        Ok(a.iter()
            .zip(b)
            .zip(da.iter().zip(db))
            .map(|((a, b), (da, db))| da * b + a * db)
            .collect())
    }
    /// Pull back a covector on the factorized product to the original left and right ports.
    pub fn pullback(
        &self,
        left: &[Rat],
        right: &[Rat],
        product_covector: &[Rat],
    ) -> Result<(Vec<Rat>, Vec<Rat>), ExactLinearError> {
        let a = self.left_forms.apply(left)?;
        let b = self.right_forms.apply(right)?;
        if product_covector.len() != a.len() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let left_factor = a
            .iter()
            .zip(&b)
            .zip(product_covector)
            .map(|((_, b), weight)| weight * b)
            .collect::<Vec<_>>();
        let right_factor = a
            .iter()
            .zip(product_covector)
            .map(|(a, weight)| weight * a)
            .collect::<Vec<_>>();
        Ok((
            self.left_forms.transpose()?.apply(&left_factor)?,
            self.right_forms.transpose()?.apply(&right_factor)?,
        ))
    }
    pub fn factor_receiver(
        &self,
        target: &BilinearOperator,
    ) -> Result<ReceiverFactorization, ExactLinearError> {
        if self.left_forms.columns() != target.left_extent
            || self.right_forms.columns() != target.right_extent
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        self.tensor_image.factor_receiver(&target.coefficients)
    }
    /// The complete family is retained in the result. Execution below uses its documented
    /// particular coordinate choice; every free row direction vanishes on the product core.
    pub fn bind(
        self: &Arc<Self>,
        target: &BilinearOperator,
    ) -> Result<Result<BilinearRealization, ReceiverFactorization>, ExactLinearError> {
        match self.factor_receiver(target)? {
            ReceiverFactorization::Factored(receiver) => Ok(Ok(BilinearRealization {
                core: Arc::clone(self),
                receiver,
            })),
            obstruction => Ok(Err(obstruction)),
        }
    }
    pub fn swap_ports(&self) -> Result<Self, ExactLinearError> {
        Self::new(self.right_forms.clone(), self.left_forms.clone())
    }
}

fn product_pullback(
    left: &[Rat],
    right: &[Rat],
    product_covector: &[Rat],
    left_extent: usize,
    right_extent: usize,
) -> Result<(Vec<Rat>, Vec<Rat>), ExactLinearError> {
    if left.len() != left_extent
        || right.len() != right_extent
        || product_covector.len()
            != left_extent
                .checked_mul(right_extent)
                .ok_or(ExactLinearError::ExtentOverflow)?
    {
        return Err(ExactLinearError::ShapeMismatch);
    }
    let mut left_covector = vec![Rat::zero(); left_extent];
    let mut right_covector = vec![Rat::zero(); right_extent];
    for i in 0..left_extent {
        for j in 0..right_extent {
            let weight = &product_covector[i * right_extent + j];
            left_covector[i] += weight * &right[j];
            right_covector[j] += weight * &left[i];
        }
    }
    Ok((left_covector, right_covector))
}

#[derive(Clone, Debug)]
pub struct BilinearRealization {
    core: Arc<BilinearProductCore>,
    receiver: LinearMapFamily,
}
impl BilinearRealization {
    pub fn core(&self) -> &Arc<BilinearProductCore> {
        &self.core
    }
    pub fn receiver(&self) -> &LinearMapFamily {
        &self.receiver
    }
    /// Join receivers of this same product occurrence. Every component is read from one
    /// shared core; joining does not independently select a source for each output block.
    pub fn join_receivers(&self, others: &[&Self]) -> Result<Self, ExactLinearError> {
        let mut rows = self.receiver.particular.to_rows();
        for other in others {
            if !Arc::ptr_eq(&self.core, &other.core) {
                return Err(ExactLinearError::DifferentProductCores);
            }
            rows.extend(other.receiver.particular.to_rows());
        }
        let target = BilinearOperator::new(
            self.core.left_forms.columns(),
            self.core.right_forms.columns(),
            ExactRatMatrix::new(rows)?.multiply(&self.core.tensor_image)?,
        )?;
        self.core
            .bind(&target)?
            .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)
    }
    pub fn apply(&self, left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, ExactLinearError> {
        self.receiver
            .particular
            .apply(&self.core.apply(left, right)?)
    }
    /// Differential of the realized bilinear output. The receiver is applied after the shared
    /// factorized product differential, so no full interaction tensor is materialized.
    pub fn differential(
        &self,
        left: &[Rat],
        right: &[Rat],
        left_delta: &[Rat],
        right_delta: &[Rat],
    ) -> Result<Vec<Rat>, ExactLinearError> {
        self.receiver.particular.apply(&self.core.differential(
            left,
            right,
            left_delta,
            right_delta,
        )?)
    }
    /// Pull back an output covector through the receiver and shared product core. The result is
    /// a pair of input covectors, before any declared metric identification.
    pub fn pullback(
        &self,
        left: &[Rat],
        right: &[Rat],
        output_covector: &[Rat],
    ) -> Result<(Vec<Rat>, Vec<Rat>), ExactLinearError> {
        let product_covector = self
            .receiver
            .particular
            .transpose()?
            .apply(output_covector)?;
        self.core.pullback(left, right, &product_covector)
    }
    /// Precompose both input ports and rederive the receiver family on the resulting shared core.
    /// The maps may be noninvertible: this is an input restriction/transport, not a rechart, and a
    /// rank drop is allowed to expose additional receiver freedom.
    pub fn precompose_ports(
        &self,
        left_new_to_old: &ExactRatMatrix,
        right_new_to_old: &ExactRatMatrix,
    ) -> Result<Self, ExactLinearError> {
        if left_new_to_old.rows() != self.core.left_forms.columns()
            || right_new_to_old.rows() != self.core.right_forms.columns()
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let new_core = Arc::new(BilinearProductCore::new(
            self.core.left_forms.multiply(left_new_to_old)?,
            self.core.right_forms.multiply(right_new_to_old)?,
        )?);
        let target = BilinearOperator::new(
            left_new_to_old.columns(),
            right_new_to_old.columns(),
            self.receiver.particular.multiply(&new_core.tensor_image)?,
        )?;
        new_core
            .bind(&target)?
            .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)
    }
    /// Compose a new returned-face map while preserving the complete product core. Re-derive
    /// the entire receiver family, including any newly invisible directions.
    pub fn then_receiver(&self, next: &ExactRatMatrix) -> Result<Self, ExactLinearError> {
        let target = BilinearOperator::new(
            self.core.left_forms.columns(),
            self.core.right_forms.columns(),
            next.multiply(&self.receiver.particular)?
                .multiply(&self.core.tensor_image)?,
        )?;
        self.core
            .bind(&target)?
            .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)
    }
    /// Compile next(self(x,z), fixed_right) into this product core's receiver. Fixing the
    /// following right port makes that action linear: D_next diag(B_next c) A_next.
    /// The full resulting decoder family is re-derived by the existing receiver factorizer.
    pub fn then_fixed_right(
        &self,
        next: &Self,
        fixed_right: &[Rat],
    ) -> Result<Self, ExactLinearError> {
        let amplitudes = next.core.right_forms.apply(fixed_right)?;
        let section = next
            .receiver
            .particular
            .multiply(&ExactRatMatrix::from_diagonal(amplitudes)?)?
            .multiply(&next.core.left_forms)?;
        self.then_receiver(&section)
    }
    pub fn tensor_residual(
        &self,
        target: &BilinearOperator,
    ) -> Result<ExactRatMatrix, ExactLinearError> {
        if self.core.left_forms.columns() != target.left_extent
            || self.core.right_forms.columns() != target.right_extent
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        self.receiver
            .particular
            .multiply(&self.core.tensor_image)?
            .subtract(&target.coefficients)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn q(n: i64) -> Rat {
        Rat::from_integer(n.into())
    }
    fn m(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|r| r.iter().map(|&x| q(x)).collect())
                .collect(),
        )
        .unwrap()
    }
    fn core() -> Arc<BilinearProductCore> {
        Arc::new(
            BilinearProductCore::new(
                m(&[&[1, 0], &[0, 1], &[1, 1]]),
                m(&[&[1, 0], &[0, 1], &[1, 1]]),
            )
            .unwrap(),
        )
    }
    fn complex() -> BilinearOperator {
        BilinearOperator::new(2, 2, m(&[&[1, 0, 0, -1], &[0, 1, 1, 0]])).unwrap()
    }
    fn polynomial() -> BilinearOperator {
        BilinearOperator::new(2, 2, m(&[&[1, 0, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 1]])).unwrap()
    }
    #[test]
    fn one_retained_core_serves_distinct_receivers_and_composition() {
        let core = core();
        let complex = core.bind(&complex()).unwrap().unwrap();
        let polynomial = core.bind(&polynomial()).unwrap().unwrap();
        let (a, b) = (vec![q(2), q(3)], vec![q(4), q(5)]);
        assert_eq!(complex.apply(&a, &b).unwrap(), vec![q(-7), q(22)]);
        assert_eq!(polynomial.apply(&a, &b).unwrap(), vec![q(8), q(22), q(15)]);
        assert!(Arc::ptr_eq(complex.core(), polynomial.core()));
        let middle = polynomial.then_receiver(&m(&[&[0, 1, 0]])).unwrap();
        assert_eq!(middle.apply(&a, &b).unwrap(), vec![q(22)]);
        assert!(Arc::ptr_eq(&core, middle.core()));
    }

    #[test]
    fn factorized_differential_matches_finite_change_with_mixed_correction() {
        let core = BilinearProductCore::new(
            m(&[&[2, 1], &[1, 1], &[1, 2]]),
            m(&[&[1, 2], &[0, 1], &[2, 1]]),
        )
        .unwrap();
        let x = vec![q(2), q(3)];
        let y = vec![q(4), q(5)];
        let dx = vec![q(1), q(-1)];
        let dy = vec![q(2), q(1)];
        let before = core.apply(&x, &y).unwrap();
        let after = core
            .apply(
                &x.iter().zip(&dx).map(|(a, b)| a + b).collect::<Vec<_>>(),
                &y.iter().zip(&dy).map(|(a, b)| a + b).collect::<Vec<_>>(),
            )
            .unwrap();
        let differential = core.differential(&x, &y, &dx, &dy).unwrap();
        let mixed = core.apply(&dx, &dy).unwrap();
        for ((after, before), (differential, mixed)) in after
            .iter()
            .zip(&before)
            .zip(differential.iter().zip(&mixed))
        {
            assert_eq!(after - before, differential + mixed);
        }
    }

    #[test]
    fn realized_pullback_satisfies_exact_adjoint_duality() {
        let realization = core().bind(&complex()).unwrap().unwrap();
        let x = vec![q(2), q(3)];
        let y = vec![q(4), q(5)];
        let dx = vec![q(1), q(-1)];
        let dy = vec![q(2), q(1)];
        let lambda = vec![q(7), q(-2)];
        let differential = realization.differential(&x, &y, &dx, &dy).unwrap();
        let (left_covector, right_covector) = realization.pullback(&x, &y, &lambda).unwrap();
        let lhs: Rat = lambda.iter().zip(&differential).map(|(a, b)| a * b).sum();
        let rhs: Rat = left_covector
            .iter()
            .zip(&dx)
            .map(|(a, b)| a * b)
            .sum::<Rat>()
            + right_covector
                .iter()
                .zip(&dy)
                .map(|(a, b)| a * b)
                .sum::<Rat>();
        assert_eq!(lhs, rhs);
        assert!(realization.pullback(&x, &y, &[q(1)]).is_err());
        assert!(realization.differential(&x, &y, &[q(1)], &dy).is_err());
    }

    #[test]
    fn precomposed_ports_transport_values_and_covectors_in_nonorthogonal_charts() {
        let realization = core().bind(&complex()).unwrap().unwrap();
        let left_map = m(&[&[1], &[2]]);
        let right_map = m(&[&[2, 1], &[1, 1]]);
        let precomposed = realization.precompose_ports(&left_map, &right_map).unwrap();
        let left = vec![q(3)];
        let right = vec![q(4), q(5)];
        let old_left = left_map.apply(&left).unwrap();
        let old_right = right_map.apply(&right).unwrap();
        assert_eq!(
            precomposed.apply(&left, &right).unwrap(),
            realization.apply(&old_left, &old_right).unwrap()
        );
        let lambda = vec![q(7), q(-2)];
        let (old_left_covector, old_right_covector) = realization
            .pullback(&old_left, &old_right, &lambda)
            .unwrap();
        let (left_covector, right_covector) = precomposed.pullback(&left, &right, &lambda).unwrap();
        assert_eq!(
            left_covector,
            left_map
                .transpose()
                .unwrap()
                .apply(&old_left_covector)
                .unwrap()
        );
        assert_eq!(
            right_covector,
            right_map
                .transpose()
                .unwrap()
                .apply(&old_right_covector)
                .unwrap()
        );
    }

    #[test]
    fn precomposition_rederives_receiver_freedom_after_rank_drop() {
        let realization = core().bind(&complex()).unwrap().unwrap();
        let left_map = m(&[&[1], &[0]]);
        let right_map = m(&[&[1], &[0]]);
        let precomposed = realization.precompose_ports(&left_map, &right_map).unwrap();
        assert!(!precomposed.receiver.free_row_directions.is_empty());
        assert!(precomposed
            .precompose_ports(&m(&[&[1, 0]]), &right_map)
            .is_err());
    }

    #[test]
    fn operator_differential_and_pullback_reject_wrong_port_extents() {
        let operator = complex();
        let x = vec![q(2), q(3)];
        let y = vec![q(4), q(5)];
        assert!(operator.differential(&x, &y, &[q(1)], &y).is_err());
        assert!(operator.pullback(&x, &y, &[q(1)]).is_err());
        let differential = operator.differential(&x, &y, &x, &y).unwrap();
        assert_eq!(differential, vec![q(-14), q(44)]);
        let (left, right) = operator.pullback(&x, &y, &[q(7), q(-2)]).unwrap();
        assert_eq!(left, vec![q(18), q(-43)]);
        assert_eq!(right, vec![q(8), q(-25)]);
    }
    #[test]
    fn joint_receivers_keep_order_multiplicity_and_actual_core_identity() {
        let shared = core();
        let a = shared.bind(&complex()).unwrap().unwrap();
        let b = shared.bind(&polynomial()).unwrap().unwrap();
        let joint = a.join_receivers(&[&b, &a]).unwrap();
        assert!(Arc::ptr_eq(joint.core(), &shared));
        assert_eq!(joint.core().products(), 3);
        assert_eq!(
            joint.apply(&[q(2), q(3)], &[q(4), q(5)]).unwrap(),
            vec![q(-7), q(22), q(8), q(22), q(15), q(-7), q(22)]
        );
        let other = core().bind(&complex()).unwrap().unwrap();
        assert_eq!(
            a.join_receivers(&[&other]).unwrap_err(),
            ExactLinearError::DifferentProductCores
        );
    }
    #[test]
    fn collapsed_face_returns_a_separating_direction() {
        let s = complex();
        let target = polynomial();
        let ReceiverFactorization::Obstructed {
            source_null,
            returned,
        } = s
            .coefficients
            .factor_receiver(&target.coefficients)
            .unwrap()
        else {
            panic!("lost polynomial distinction")
        };
        assert!(
            s.coefficients
                .apply(&source_null)
                .unwrap()
                .iter()
                .all(Zero::is_zero)
        );
        assert!(returned.iter().any(|x| !x.is_zero()));
    }
    #[test]
    fn reorientation_retains_inverse_fibres() {
        let s = complex();
        let (a, b) = (vec![q(2), q(3)], vec![q(4), q(5)]);
        let face = s.apply(&a, &b).unwrap();
        assert_eq!(s.swap_ports().unwrap().apply(&b, &a).unwrap(), face);
        let (particular, kernel) = s
            .left_section(&b)
            .unwrap()
            .preimage_fibre(&face)
            .unwrap()
            .unwrap();
        assert_eq!(particular, a);
        assert!(kernel.is_empty());
        let zero = s.left_section(&[q(0), q(0)]).unwrap();
        assert_eq!(
            zero.preimage_fibre(&[q(0), q(0)]).unwrap().unwrap().1.len(),
            2
        );
        assert!(zero.preimage_fibre(&[q(1), q(0)]).unwrap().is_none());
    }
    #[test]
    fn a_fixed_port_observation_retains_correlated_source_parameters() {
        let dot = BilinearOperator::new(2, 2, m(&[&[1, 0, 0, 1]])).unwrap();
        let anchor = vec![q(1), q(1)];
        let directions = m(&[&[1], &[-1]]);
        let family = dot
            .left_family_preimage(&[q(1), q(1)], &anchor, &directions, &[q(2)])
            .unwrap()
            .unwrap();
        assert_eq!(family.1.len(), 1);
        assert!(
            dot.left_family_preimage(&[q(1), q(1)], &anchor, &directions, &[q(3)])
                .unwrap()
                .is_none()
        );
        let separated = dot
            .left_family_preimage(&[q(1), q(2)], &anchor, &directions, &[q(4)])
            .unwrap()
            .unwrap();
        assert_eq!(separated.0, vec![q(-1)]);
        assert!(separated.1.is_empty());
        assert_eq!(dot.apply(&[q(0), q(2)], &[q(1), q(2)]).unwrap(), vec![q(4)]);
    }
    #[test]
    fn support_search_resumes_the_actual_remaining_population() {
        let grammar = m(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]);
        let mut search =
            BilinearSupportSearch::new(complex(), grammar.clone(), grammar, 1..=3).unwrap();
        for _ in 0..17 {
            search.next().unwrap().unwrap();
        }
        let remaining = search.remaining_support().unwrap().to_vec();
        let mut resumed = search.clone();
        assert_eq!(resumed.remaining_support(), Some(remaining.as_slice()));
        let mut count = 17;
        let mut found = 0;
        while let Some(next) = search.next() {
            let a = next.unwrap();
            let b = resumed.next().unwrap().unwrap();
            assert_eq!(a.support, b.support);
            assert_eq!(a.receiver, b.receiver);
            count += 1;
            if matches!(a.receiver, ReceiverFactorization::Factored(_)) {
                found += 1;
            }
        }
        assert!(resumed.next().is_none());
        assert_eq!(count, 696);
        assert_eq!(found, 16);
    }
    #[test]
    fn redundant_products_keep_the_full_decoder_family() {
        let core = Arc::new(BilinearProductCore::new(m(&[&[1], &[1]]), m(&[&[1], &[1]])).unwrap());
        let target = BilinearOperator::new(1, 1, m(&[&[1]])).unwrap();
        let bound = core.bind(&target).unwrap().unwrap();
        assert_eq!(bound.receiver.free_row_directions.len(), 1);
        for direction in &bound.receiver.free_row_directions {
            assert!(
                core.tensor_image
                    .transpose()
                    .unwrap()
                    .apply(direction)
                    .unwrap()
                    .iter()
                    .all(Zero::is_zero)
            );
        }
        assert!(
            bound
                .tensor_residual(&target)
                .unwrap()
                .entries()
                .iter()
                .all(Zero::is_zero)
        );
    }

    #[test]
    fn fixed_right_sequence_compiles_into_the_same_product_core() {
        let first = core().bind(&complex()).unwrap().unwrap();
        let fixed = vec![q(2), q(-1)];
        let compiled = first.then_fixed_right(&first, &fixed).unwrap();
        assert!(Arc::ptr_eq(compiled.core(), first.core()));
        let target = BilinearOperator::new(
            2,
            2,
            complex()
                .left_section(&fixed)
                .unwrap()
                .multiply(complex().coefficients())
                .unwrap(),
        )
        .unwrap();
        assert!(
            compiled
                .tensor_residual(&target)
                .unwrap()
                .entries()
                .iter()
                .all(Zero::is_zero)
        );
        for (x, y) in [
            (vec![q(2), q(3)], vec![q(4), q(5)]),
            (vec![q(1) / q(3), q(2)], vec![q(-1), q(2) / q(5)]),
        ] {
            assert_eq!(
                compiled.apply(&x, &y).unwrap(),
                first.apply(&first.apply(&x, &y).unwrap(), &fixed).unwrap()
            );
        }
        let wide = first.core().bind(&polynomial()).unwrap().unwrap();
        assert!(wide.then_fixed_right(&first, &fixed).is_err());
        assert!(first.then_fixed_right(&first, &[q(1)]).is_err());
    }
}

/// One declared support's complete return. The immutable core survives receiver rebinding.
#[derive(Clone, Debug)]
pub struct BilinearSupportReturn {
    support: Vec<(usize, usize)>,
    core: Arc<BilinearProductCore>,
    receiver: ReceiverFactorization,
}
impl BilinearSupportReturn {
    pub fn support(&self) -> &[(usize, usize)] {
        &self.support
    }
    pub fn core(&self) -> &Arc<BilinearProductCore> {
        &self.core
    }
    pub fn receiver(&self) -> &ReceiverFactorization {
        &self.receiver
    }
    pub fn into_realization(self) -> Result<BilinearRealization, ReceiverFactorization> {
        match self.receiver {
            ReceiverFactorization::Factored(receiver) => Ok(BilinearRealization {
                core: self.core,
                receiver,
            }),
            obstruction => Err(obstruction),
        }
    }
}

/// Streaming finite support search. The coefficient grammar and rank range belong to the
/// caller's aperture. Dropping/pausing the iterator does not establish grammar exhaustion.
/// Search order is a coordinate enumeration, not a native semantic ranking.
#[derive(Clone, Debug)]
pub struct BilinearSupportSearch {
    target: BilinearOperator,
    left: ExactRatMatrix,
    right: ExactRatMatrix,
    atoms: usize,
    maximum: usize,
    next_support: Option<Vec<usize>>,
}
impl BilinearSupportSearch {
    pub fn new(
        target: BilinearOperator,
        left: ExactRatMatrix,
        right: ExactRatMatrix,
        products: std::ops::RangeInclusive<usize>,
    ) -> Result<Self, ExactLinearError> {
        if left.columns() != target.left_extent || right.columns() != target.right_extent {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let atoms = left
            .rows()
            .checked_mul(right.rows())
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let maximum = (*products.end()).min(atoms);
        let minimum = *products.start();
        let next_support = (minimum <= maximum).then(|| (0..minimum).collect());
        Ok(Self {
            target,
            left,
            right,
            atoms,
            maximum,
            next_support,
        })
    }
    pub fn remaining_support(&self) -> Option<&[usize]> {
        self.next_support.as_deref()
    }
    fn advance(&mut self, support: &[usize]) {
        let rank = support.len();
        for i in (0..rank).rev() {
            if support[i] < self.atoms - rank + i {
                let mut next = support.to_vec();
                next[i] += 1;
                for j in i + 1..rank {
                    next[j] = next[j - 1] + 1;
                }
                self.next_support = Some(next);
                return;
            }
        }
        self.next_support = if rank < self.maximum {
            Some((0..rank + 1).collect())
        } else {
            None
        };
    }
}
impl Iterator for BilinearSupportSearch {
    type Item = Result<BilinearSupportReturn, ExactLinearError>;
    fn next(&mut self) -> Option<Self::Item> {
        let support = self.next_support.clone()?;
        self.advance(&support);
        Some((|| {
            let pairs: Vec<_> = support
                .iter()
                .map(|i| (*i / self.right.rows(), *i % self.right.rows()))
                .collect();
            let left = pairs
                .iter()
                .map(|(i, _)| self.left.row(*i).map(<[Rat]>::to_vec))
                .collect::<Result<Vec<_>, _>>()?;
            let right = pairs
                .iter()
                .map(|(_, j)| self.right.row(*j).map(<[Rat]>::to_vec))
                .collect::<Result<Vec<_>, _>>()?;
            let core = Arc::new(BilinearProductCore::new(
                ExactRatMatrix::shaped(pairs.len(), self.left.columns(), left)?,
                ExactRatMatrix::shaped(pairs.len(), self.right.columns(), right)?,
            )?);
            let receiver = core.factor_receiver(&self.target)?;
            Ok(BilinearSupportReturn {
                support: pairs,
                core,
                receiver,
            })
        })())
    }
}
