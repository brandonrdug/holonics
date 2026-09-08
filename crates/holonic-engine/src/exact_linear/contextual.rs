//! Exact factorization of source-invisible occurrence combinations through carried context.
//! This is an algebraic construction/reference, not a native learner or a selected cause.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinearMapFamily {
    /// Coordinates for the affine family of maps. This is not installed as an actual map.
    pub particular: ExactRatMatrix,
    /// Each output row may independently vary by any of these input covectors.
    pub free_row_directions: Vec<Vec<Rat>>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContextualObstruction {
    /// Coefficients on the original, ordered occurrence columns.
    pub occurrence_combination: Vec<Rat>,
    pub source: Vec<Rat>,
    pub context: Vec<Rat>,
    pub returned: Vec<Rat>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactContextualLift {
    pub source_kernel: Vec<Vec<Rat>>,
    /// Actual context directions supplied by source-invisible occurrence combinations.
    pub contrast_context: ExactRatMatrix,
    pub contrast_return: ExactRatMatrix,
    /// All maps taking the actually carried contextual contrast to its returned contrast.
    pub contrast_map: LinearMapFamily,
    /// N=C(ker(S) intersect ker(Y)), in the declared present receiver scope.
    pub silent_context: Vec<Vec<Rat>>,
    /// Full quotient C -> C/N. Unobserved context directions have not been dropped.
    pub context_quotient: ExactRatMatrix,
    pub lifted_source: ExactRatMatrix,
    pub returned_map: LinearMapFamily,
    pub demonstrated_context_rank: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContextualFactorization {
    Lifted(ExactContextualLift),
    Obstructed(ContextualObstruction),
}

fn columns(height: usize, columns: Vec<Vec<Rat>>) -> Result<ExactRatMatrix, ExactLinearError> {
    ExactRatMatrix::shaped(columns.len(), height, columns)?.transpose()
}
fn stack(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Result<ExactRatMatrix, ExactLinearError> {
    if a.columns() != b.columns() {
        return Err(ExactLinearError::ShapeMismatch);
    }
    let mut rows = a.to_rows();
    rows.extend(b.to_rows());
    ExactRatMatrix::shaped(a.rows() + b.rows(), a.columns(), rows)
}
fn factor_family(
    source: &ExactRatMatrix,
    target: &ExactRatMatrix,
) -> Result<Option<LinearMapFamily>, ExactLinearError> {
    if source.columns() != target.columns() {
        return Err(ExactLinearError::ShapeMismatch);
    }
    let equations = source.transpose()?;
    let mut rows = Vec::with_capacity(target.rows());
    for row in target.to_rows() {
        let Some((particular, _)) = equations.preimage_fibre(&row)? else {
            return Ok(None);
        };
        rows.push(particular);
    }
    Ok(Some(LinearMapFamily {
        particular: ExactRatMatrix::shaped(target.rows(), source.rows(), rows)?,
        free_row_directions: equations.kernel_basis()?,
    }))
}

impl ExactRatMatrix {
    /// Columns are actual, ordered observations in a declared local rational-linear chart.
    /// `self=S`, `context=C`, `returned=Y`. A lift exists precisely when
    /// ker(S) intersect ker(C) is contained in ker(Y). The returned witness or quotient
    /// retains the full oriented vectors. No score, source label or minimum-norm cause is used.
    pub fn contextual_factorization(
        &self,
        context: &Self,
        returned: &Self,
    ) -> Result<ContextualFactorization, ExactLinearError> {
        if self.columns() != context.columns() || self.columns() != returned.columns() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        for k in stack(self, context)?.kernel_basis()? {
            let response = returned.apply(&k)?;
            if response.iter().any(|v| !v.is_zero()) {
                return Ok(ContextualFactorization::Obstructed(ContextualObstruction {
                    source: self.apply(&k)?,
                    context: context.apply(&k)?,
                    returned: response,
                    occurrence_combination: k,
                }));
            }
        }
        let source_kernel = self.kernel_basis()?;
        let k = columns(self.columns(), source_kernel.clone())?;
        let contrast_context = context.multiply(&k)?;
        let contrast_return = returned.multiply(&k)?;
        let contrast_map = factor_family(&contrast_context, &contrast_return)?
            .ok_or(ExactLinearError::RankFactorizationCertificateFailure)?;
        let silent_occurrences = columns(self.columns(), stack(self, returned)?.kernel_basis()?)?;
        let silent = context.multiply(&silent_occurrences)?;
        let silent_context = silent.image_basis()?;
        // The annihilator has kernel exactly N, independent of its chosen coordinate basis.
        let q = ExactRatMatrix::shaped(
            context.rows() - silent_context.len(),
            context.rows(),
            silent.transpose()?.kernel_basis()?,
        )?;
        let lifted_source = stack(self, &q.multiply(context)?)?;
        let returned_map = factor_family(&lifted_source, returned)?
            .ok_or(ExactLinearError::RankFactorizationCertificateFailure)?;
        if returned_map.particular.multiply(&lifted_source)? != *returned {
            return Err(ExactLinearError::RankFactorizationCertificateFailure);
        }
        let demonstrated_context_rank = contrast_return.rank()?;
        if q.multiply(&contrast_context)?.rank()? != demonstrated_context_rank {
            return Err(ExactLinearError::RankFactorizationCertificateFailure);
        }
        Ok(ContextualFactorization::Lifted(ExactContextualLift {
            source_kernel,
            contrast_context,
            contrast_return,
            contrast_map,
            silent_context,
            context_quotient: q,
            lifted_source,
            returned_map,
            demonstrated_context_rank,
        }))
    }
}
impl ExactContextualLift {
    /// Attempt q T=U q on the complete declared context carrier. Failure returns the
    /// complete columns q T n for the retained silent directions; zero columns stay visible.
    /// Ordered histories are preserved only for generators whose square actually descends.
    pub fn descend_context_generator(
        &self,
        generator: &ExactRatMatrix,
    ) -> Result<Result<ExactRatMatrix, ExactRatMatrix>, ExactLinearError> {
        let q = &self.context_quotient;
        if generator.rows() != q.columns() || generator.columns() != q.columns() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let target = q.multiply(generator)?;
        let defect = target.multiply(&columns(q.columns(), self.silent_context.clone())?)?;
        if defect.entries().iter().any(|v| !v.is_zero()) {
            return Ok(Err(defect));
        }
        let family = factor_family(q, &target)?
            .ok_or(ExactLinearError::RankFactorizationCertificateFailure)?;
        if !family.free_row_directions.is_empty() || family.particular.multiply(q)? != target {
            return Err(ExactLinearError::RankFactorizationCertificateFailure);
        }
        Ok(Ok(family.particular))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn m(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|r| r.iter().map(|v| Rat::from_integer((*v).into())).collect())
                .collect(),
        )
        .unwrap()
    }
    fn lifted(s: &ExactRatMatrix, c: &ExactRatMatrix, y: &ExactRatMatrix) -> ExactContextualLift {
        let ContextualFactorization::Lifted(x) = s.contextual_factorization(c, y).unwrap() else {
            panic!("expected lift")
        };
        x
    }
    #[test]
    fn context_separates_the_actual_source_null_current() {
        let s = m(&[&[1, 1, 1]]);
        let c = m(&[&[1, -1, 0], &[0, 0, 1], &[0, 0, 0]]);
        let y = m(&[&[1, -1, 0]]);
        let l = lifted(&s, &c, &y);
        assert_eq!(l.demonstrated_context_rank, 1);
        assert_eq!(l.context_quotient.rows(), 2); // The unobserved third context direction remains.
        assert!(!l.returned_map.free_row_directions.is_empty());
        assert_eq!(
            l.returned_map
                .particular
                .multiply(&l.lifted_source)
                .unwrap(),
            y
        );
        for n in &l.silent_context {
            assert!(
                l.context_quotient
                    .apply(n)
                    .unwrap()
                    .iter()
                    .all(Zero::is_zero)
            );
        }
    }
    #[test]
    fn insufficient_context_returns_a_lineage_combination() {
        let s = m(&[&[1, 1]]);
        let c = m(&[&[2, 2]]);
        let y = m(&[&[1, -1]]);
        let ContextualFactorization::Obstructed(o) = s.contextual_factorization(&c, &y).unwrap()
        else {
            panic!("expected obstruction")
        };
        assert!(o.source.iter().chain(&o.context).all(Zero::is_zero));
        assert_eq!(y.apply(&o.occurrence_combination).unwrap(), o.returned);
        assert!(o.returned.iter().any(|v| !v.is_zero()));
    }
    #[test]
    fn present_silence_does_not_license_future_collapse() {
        let s = ExactRatMatrix::zero(0, 2).unwrap();
        let c = ExactRatMatrix::identity(2).unwrap();
        let y = m(&[&[1, 0]]);
        let l = lifted(&s, &c, &y);
        assert!(
            l.descend_context_generator(&m(&[&[1, 1], &[0, 1]]))
                .unwrap()
                .is_err()
        );
        let t = m(&[&[-1, 0], &[0, 1]]);
        let u = l.descend_context_generator(&t).unwrap().unwrap();
        assert_eq!(
            l.context_quotient.multiply(&t).unwrap(),
            u.multiply(&l.context_quotient).unwrap()
        );
    }
    #[test]
    fn a_phase_rechart_transports_the_quotient_instead_of_changing_consequence() {
        let s = m(&[&[1, 1, 1]]);
        let c = m(&[&[1, -1, 0], &[0, 0, 1]]);
        let y = m(&[&[1, -1, 0]]);
        let phase = m(&[&[0, -1], &[1, 0]]);
        let first = lifted(&s, &c, &y);
        let second = lifted(&s, &phase.multiply(&c).unwrap(), &y);
        assert_eq!(
            first.demonstrated_context_rank,
            second.demonstrated_context_rank
        );
        let second_on_first = second.context_quotient.multiply(&phase).unwrap();
        let transition = factor_family(&first.context_quotient, &second_on_first)
            .unwrap()
            .unwrap();
        assert!(transition.free_row_directions.is_empty());
        assert_eq!(
            transition.particular.rank().unwrap(),
            first.context_quotient.rows()
        );
    }
    #[test]
    fn empty_observations_leave_the_entire_context_and_map_family_open() {
        let l = lifted(
            &ExactRatMatrix::zero(2, 0).unwrap(),
            &ExactRatMatrix::zero(3, 0).unwrap(),
            &ExactRatMatrix::zero(1, 0).unwrap(),
        );
        assert_eq!(l.context_quotient, ExactRatMatrix::identity(3).unwrap());
        assert_eq!(l.demonstrated_context_rank, 0);
        assert_eq!(l.returned_map.free_row_directions.len(), 5);
    }
}
