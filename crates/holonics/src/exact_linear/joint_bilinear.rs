//! Exact preimage constraints for source and condition sharing one affine parameter family.
//! Quadratic monomials are evaluated from those parameters; they are never free source axes.
use super::{
    BilinearOperator, BilinearProductCore, BilinearRealization, ExactLinearError, ExactRatMatrix,
};
use num_traits::{One, Zero};
use relational_geometry::Rat;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointPreimageReduction {
    Affine {
        particular: Vec<Rat>,
        directions: Vec<Vec<Rat>>,
    },
    Empty {
        equation_separator: Vec<Rat>,
    },
    /// The exact nonlinear fibre remains in its owner. This is not an emptiness verdict.
    Nonlinear,
}
#[derive(Clone, Debug)]
pub struct JointBilinearFibre {
    action: BilinearRealization,
    left: ExactRatMatrix,
    right: ExactRatMatrix,
    returned: ExactRatMatrix,
    residual: BilinearRealization,
    polynomial: ExactRatMatrix,
    parameters: usize,
}
impl JointBilinearFibre {
    /// Both affine maps consume the SAME (theta,1). Last columns are their anchors.
    pub fn new(
        action: BilinearRealization,
        left: ExactRatMatrix,
        right: ExactRatMatrix,
        observed: Vec<Rat>,
    ) -> Result<Self, ExactLinearError> {
        if left.columns() == 0 {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let returned = ExactRatMatrix::shaped(
            observed.len(),
            left.columns(),
            observed
                .into_iter()
                .map(|v| {
                    let mut row = vec![Rat::zero(); left.columns()];
                    row[left.columns() - 1] = v;
                    row
                })
                .collect(),
        )?;
        Self::with_affine_return(action, left, right, returned)
    }
    /// The returned face may itself be a coordinate of this same parameter family. This
    /// permits a carried junction z=x*h followed by another constraint, without freeing z.
    pub fn with_affine_return(
        action: BilinearRealization,
        left: ExactRatMatrix,
        right: ExactRatMatrix,
        returned: ExactRatMatrix,
    ) -> Result<Self, ExactLinearError> {
        if left.columns() == 0
            || left.columns() != right.columns()
            || returned.columns() != left.columns()
            || returned.rows() != action.receiver().particular.rows()
        {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let parameters = left.columns() - 1;
        let mut a = action.core().left_forms().multiply(&left)?.to_rows();
        let mut b = action.core().right_forms().multiply(&right)?.to_rows();
        let active = (0..returned.columns())
            .filter(|&i| (0..returned.rows()).any(|r| !returned.get(r, i).unwrap().is_zero()))
            .collect::<Vec<_>>();
        let mut one = vec![Rat::zero(); parameters + 1];
        one[parameters] = Rat::one();
        for &i in &active {
            let mut coordinate = vec![Rat::zero(); parameters + 1];
            coordinate[i] = Rat::one();
            a.push(coordinate);
            b.push(one.clone());
        }
        let core = Arc::new(BilinearProductCore::new(
            ExactRatMatrix::shaped(a.len(), parameters + 1, a)?,
            ExactRatMatrix::shaped(b.len(), parameters + 1, b)?,
        )?);
        let mut output = action.receiver().particular.to_rows();
        for (r, row) in output.iter_mut().enumerate() {
            for &i in &active {
                row.push(-returned.get(r, i)?.clone());
            }
        }
        let d = ExactRatMatrix::shaped(returned.rows(), core.products(), output)?;
        let tensor = d.multiply(core.tensor_image())?;
        let target = BilinearOperator::new(parameters + 1, parameters + 1, tensor.clone())?;
        let residual = core
            .bind(&target)?
            .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)?;
        let quadratic = parameters
            .checked_mul(
                parameters
                    .checked_add(1)
                    .ok_or(ExactLinearError::ExtentOverflow)?,
            )
            .ok_or(ExactLinearError::ExtentOverflow)?
            / 2;
        let width = parameters
            .checked_add(1)
            .and_then(|v| v.checked_add(quadratic))
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let mut rows = Vec::new();
        for r in 0..returned.rows() {
            let mut row = vec![
                tensor
                    .get(r, parameters * (parameters + 1) + parameters)?
                    .clone(),
            ];
            for i in 0..parameters {
                row.push(
                    tensor.get(r, i * (parameters + 1) + parameters)?
                        + tensor.get(r, parameters * (parameters + 1) + i)?,
                );
            }
            for i in 0..parameters {
                for j in i..parameters {
                    row.push(if i == j {
                        tensor.get(r, i * (parameters + 1) + j)?.clone()
                    } else {
                        tensor.get(r, i * (parameters + 1) + j)?
                            + tensor.get(r, j * (parameters + 1) + i)?
                    });
                }
            }
            rows.push(row);
        }
        let polynomial = ExactRatMatrix::shaped(returned.rows(), width, rows)?;
        Ok(Self {
            action,
            left,
            right,
            returned,
            residual,
            polynomial,
            parameters,
        })
    }
    pub fn parameters(&self) -> usize {
        self.parameters
    }
    pub fn polynomial(&self) -> &ExactRatMatrix {
        &self.polynomial
    }
    pub fn source_map(&self) -> &ExactRatMatrix {
        &self.left
    }
    pub fn condition_map(&self) -> &ExactRatMatrix {
        &self.right
    }
    pub fn returned_map(&self) -> &ExactRatMatrix {
        &self.returned
    }
    pub fn residual_realization(&self) -> &BilinearRealization {
        &self.residual
    }
    /// Exact residual F(source(theta),condition(theta))-observed. No independent theta_i theta_j
    /// packet is accepted through this method.
    pub fn evaluate(&self, parameters: &[Rat]) -> Result<Vec<Rat>, ExactLinearError> {
        if parameters.len() != self.parameters {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut homogeneous = parameters.to_vec();
        homogeneous.push(Rat::one());
        self.residual.apply(&homogeneous, &homogeneous)
    }
    pub fn contains(&self, parameters: &[Rat]) -> Result<bool, ExactLinearError> {
        Ok(self.evaluate(parameters)?.iter().all(Zero::is_zero))
    }
    /// Restrict/rechart the parameter family, retaining the common affine lift. The last row
    /// must preserve the homogeneous coordinate, rather than silently changing the anchors.
    pub fn restrict(&self, parameter_map: &ExactRatMatrix) -> Result<Self, ExactLinearError> {
        if parameter_map.rows() != self.parameters + 1 || parameter_map.columns() == 0 {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let last = parameter_map.row(self.parameters)?;
        if !last[..last.len() - 1].iter().all(Zero::is_zero) || last.last() != Some(&Rat::one()) {
            return Err(ExactLinearError::ShapeMismatch);
        }
        Self::with_affine_return(
            self.action.clone(),
            self.left.multiply(parameter_map)?,
            self.right.multiply(parameter_map)?,
            self.returned.multiply(parameter_map)?,
        )
    }
    /// A slice is handed to the existing affine preimage owner only if its entire quadratic
    /// block cancels. Otherwise the implicit polynomial fibre is kept intact.
    pub fn affine_preimage(&self) -> Result<JointPreimageReduction, ExactLinearError> {
        affine_reduction(&self.polynomial, self.parameters)
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
                .map(|r| r.iter().map(|&v| q(v)).collect())
                .collect(),
        )
        .unwrap()
    }
    fn multiply() -> BilinearRealization {
        let core = Arc::new(BilinearProductCore::new(m(&[&[1]]), m(&[&[1]])).unwrap());
        core.bind(&BilinearOperator::new(1, 1, m(&[&[1]])).unwrap())
            .unwrap()
            .unwrap()
    }
    #[test]
    fn shared_square_does_not_accept_a_free_negative_square_coordinate() {
        let f =
            JointBilinearFibre::new(multiply(), m(&[&[1, 0]]), m(&[&[1, 0]]), vec![q(-1)]).unwrap();
        assert_eq!(f.polynomial.to_rows(), vec![vec![q(1), q(0), q(1)]]);
        // The linear relaxation can accept (1,theta,z)=(1,0,-1). The actual parameter lift cannot.
        assert_eq!(
            f.polynomial.apply(&[q(1), q(0), q(-1)]).unwrap(),
            vec![q(0)]
        );
        assert_eq!(f.evaluate(&[q(0)]).unwrap(), vec![q(1)]);
        assert_eq!(
            f.affine_preimage().unwrap(),
            JointPreimageReduction::Nonlinear
        );
    }
    #[test]
    fn pinning_a_condition_returns_the_complete_affine_source_fibre() {
        let f = JointBilinearFibre::new(multiply(), m(&[&[1, 0, 0]]), m(&[&[0, 1, 0]]), vec![q(6)])
            .unwrap();
        assert!(f.contains(&[q(3), q(2)]).unwrap());
        assert!(!f.contains(&[q(1), q(1)]).unwrap());
        let slice = f.restrict(&m(&[&[1, 0], &[0, 2], &[0, 1]])).unwrap();
        assert_eq!(
            slice.affine_preimage().unwrap(),
            JointPreimageReduction::Affine {
                particular: vec![q(3)],
                directions: vec![]
            }
        );
        let impossible = f.restrict(&m(&[&[1, 0], &[0, 0], &[0, 1]])).unwrap();
        assert!(matches!(
            impossible.affine_preimage().unwrap(),
            JointPreimageReduction::Empty { .. }
        ));
    }
    #[test]
    fn source_condition_and_material_keep_their_joining_coordinate() {
        // theta=(x,h,z,m). Retain z=x*h AND m*z=24 at the same parameter occurrence.
        let product = JointBilinearFibre::with_affine_return(
            multiply(),
            m(&[&[1, 0, 0, 0, 0]]),
            m(&[&[0, 1, 0, 0, 0]]),
            m(&[&[0, 0, 1, 0, 0]]),
        )
        .unwrap();
        let material = JointBilinearFibre::new(
            multiply(),
            m(&[&[0, 0, 0, 1, 0]]),
            m(&[&[0, 0, 1, 0, 0]]),
            vec![q(24)],
        )
        .unwrap();
        let system =
            JointBilinearSystem::new(vec![Arc::new(product.clone()), Arc::new(material.clone())])
                .unwrap();
        let actual = [q(2), q(3), q(6), q(4)];
        assert!(product.contains(&actual).unwrap() && material.contains(&actual).unwrap());
        let spurious = [q(2), q(3), q(8), q(3)];
        assert!(!product.contains(&spurious).unwrap());
        assert!(material.contains(&spurious).unwrap());
        assert!(system.contains(&actual).unwrap());
        assert!(!system.contains(&spurious).unwrap());
        assert_eq!(system.evaluate(&spurious).unwrap(), vec![q(-2), q(0)]);
        let material_cut = m(&[&[0, 2], &[0, 3], &[0, 6], &[1, 0], &[0, 1]]);
        assert_eq!(
            system
                .restrict(&material_cut)
                .unwrap()
                .affine_preimage()
                .unwrap(),
            JointPreimageReduction::Affine {
                particular: vec![q(4)],
                directions: vec![]
            }
        );
        let broken_cut = m(&[&[0, 2], &[0, 3], &[0, 8], &[1, 0], &[0, 1]]);
        assert!(matches!(
            system
                .restrict(&broken_cut)
                .unwrap()
                .affine_preimage()
                .unwrap(),
            JointPreimageReduction::Empty { .. }
        ));
        let pinned = product
            .restrict(&m(&[&[1, 0], &[0, 3], &[0, 6], &[0, 4], &[0, 1]]))
            .unwrap();
        assert_eq!(
            pinned.affine_preimage().unwrap(),
            JointPreimageReduction::Affine {
                particular: vec![q(2)],
                directions: vec![]
            }
        );
    }
    #[test]
    fn quadratic_cross_terms_agree_with_the_actual_composed_action() {
        let f =
            JointBilinearFibre::new(multiply(), m(&[&[1, 2, 3]]), m(&[&[4, -1, 2]]), vec![q(5)])
                .unwrap();
        for a in -2..=2 {
            for b in -2..=2 {
                let theta = [q(a), q(b)];
                let actual = f.evaluate(&theta).unwrap();
                let lifted = [q(1), q(a), q(b), q(a * a), q(a * b), q(b * b)];
                assert_eq!(actual, f.polynomial.apply(&lifted).unwrap());
                assert_eq!(actual, vec![q((a + 2 * b + 3) * (4 * a - b + 2) - 5)]);
            }
        }
    }
}

/// A declared conjunction over ONE parameter family. The caller supplies the joint chart;
/// equal dimensions of unrelated observations are not used to infer contact.
#[derive(Clone, Debug)]
pub struct JointBilinearSystem {
    constraints: Vec<Arc<JointBilinearFibre>>,
    residual: BilinearRealization,
    polynomial: ExactRatMatrix,
    parameters: usize,
}
impl JointBilinearSystem {
    pub fn new(constraints: Vec<Arc<JointBilinearFibre>>) -> Result<Self, ExactLinearError> {
        let parameters = constraints
            .first()
            .ok_or(ExactLinearError::ShapeMismatch)?
            .parameters();
        if constraints.iter().any(|f| f.parameters() != parameters) {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let rank = constraints.iter().try_fold(0usize, |s, f| {
            s.checked_add(f.residual.core().products())
                .ok_or(ExactLinearError::ExtentOverflow)
        })?;
        let outputs = constraints.iter().try_fold(0usize, |s, f| {
            s.checked_add(f.polynomial.rows())
                .ok_or(ExactLinearError::ExtentOverflow)
        })?;
        let mut left = Vec::new();
        let mut right = Vec::new();
        let mut decoder = Vec::new();
        let mut polynomials = Vec::new();
        let mut offset = 0;
        for f in &constraints {
            let core = f.residual.core();
            left.extend(core.left_forms().to_rows());
            right.extend(core.right_forms().to_rows());
            for row in f.residual.receiver().particular.to_rows() {
                let mut full = vec![Rat::zero(); rank];
                full[offset..offset + row.len()].clone_from_slice(&row);
                decoder.push(full);
            }
            offset += core.products();
            polynomials.extend(f.polynomial.to_rows());
        }
        let core = Arc::new(BilinearProductCore::new(
            ExactRatMatrix::shaped(rank, parameters + 1, left)?,
            ExactRatMatrix::shaped(rank, parameters + 1, right)?,
        )?);
        let d = ExactRatMatrix::shaped(outputs, rank, decoder)?;
        let target = BilinearOperator::new(
            parameters + 1,
            parameters + 1,
            d.multiply(core.tensor_image())?,
        )?;
        let residual = core
            .bind(&target)?
            .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)?;
        let polynomial =
            ExactRatMatrix::shaped(outputs, constraints[0].polynomial.columns(), polynomials)?;
        Ok(Self {
            constraints,
            residual,
            polynomial,
            parameters,
        })
    }
    pub fn constraints(&self) -> &[Arc<JointBilinearFibre>] {
        &self.constraints
    }
    pub fn parameters(&self) -> usize {
        self.parameters
    }
    pub fn residual_realization(&self) -> &BilinearRealization {
        &self.residual
    }
    pub fn polynomial(&self) -> &ExactRatMatrix {
        &self.polynomial
    }
    pub fn evaluate(&self, theta: &[Rat]) -> Result<Vec<Rat>, ExactLinearError> {
        if theta.len() != self.parameters {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut hom = theta.to_vec();
        hom.push(Rat::one());
        self.residual.apply(&hom, &hom)
    }
    pub fn contains(&self, theta: &[Rat]) -> Result<bool, ExactLinearError> {
        Ok(self.evaluate(theta)?.iter().all(Zero::is_zero))
    }
    pub fn restrict(&self, map: &ExactRatMatrix) -> Result<Self, ExactLinearError> {
        Self::new(
            self.constraints
                .iter()
                .map(|f| f.restrict(map).map(Arc::new))
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
    pub fn affine_preimage(&self) -> Result<JointPreimageReduction, ExactLinearError> {
        affine_reduction(&self.polynomial, self.parameters)
    }
}
fn affine_reduction(
    polynomial: &ExactRatMatrix,
    parameters: usize,
) -> Result<JointPreimageReduction, ExactLinearError> {
    if (0..polynomial.rows()).any(|r| {
        polynomial.row(r).unwrap()[parameters + 1..]
            .iter()
            .any(|v| !v.is_zero())
    }) {
        return Ok(JointPreimageReduction::Nonlinear);
    }
    let equation = ExactRatMatrix::shaped(
        polynomial.rows(),
        parameters,
        (0..polynomial.rows())
            .map(|r| polynomial.row(r).map(|v| v[1..parameters + 1].to_vec()))
            .collect::<Result<Vec<_>, _>>()?,
    )?;
    let rhs = (0..polynomial.rows())
        .map(|r| polynomial.get(r, 0).map(|v| -v))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(match equation.preimage_fibre(&rhs)? {
        Some((particular, directions)) => JointPreimageReduction::Affine {
            particular,
            directions,
        },
        None => JointPreimageReduction::Empty {
            equation_separator: equation
                .preimage_obstruction(&rhs)?
                .ok_or(ExactLinearError::RankFactorizationCertificateFailure)?,
        },
    })
}
