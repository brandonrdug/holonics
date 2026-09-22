//! Cold lowering of one compiled machine contact into the native global complex-linear chart.
//!
//! The native chart has six real coordinates per complex-3 site.  For one pair arc the existing
//! helical adapter therefore supplies `K = J C : R^12 -> R^3`, and this module returns three
//! structural rows (rank rows followed by exact zero rows) whose exact algebraic Gram is
//! `w Kᵀ D K`.  No unchecked Cholesky or float midpoint is introduced.

use super::machine::CompiledGeneratorPairArc;
use holonic_engine::{
    edit_rigidity::{EditRigidityRefusal, ExactMetric, MetricCertificate},
    exact_linear::{ExactLinearError, ExactRankFactorization, ExactRatMatrix},
    exact_value::{AlgebraicRoot, ExactInterval, ExactValueError},
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use thiserror::Error;

const NATIVE_ROWS: usize = 3;
const NATIVE_COLUMNS: usize = 12;

/// A signed-128 dyadic centre with an explicit radius.  The represented interval is
/// `(center ± radius) · 2^-grain`; the centre is a carrier coordinate, never a claim that the
/// algebraic coefficient equals that midpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DyadicCenter128 {
    pub center: i128,
    pub radius: i128,
    pub grain: u32,
}

impl DyadicCenter128 {
    pub fn zero(grain: u32) -> Self {
        Self {
            center: 0,
            radius: 0,
            grain,
        }
    }

    pub fn interval(&self) -> Result<ExactInterval, MachineFactorError> {
        let scale = dyadic_scale(self.grain);
        let center = Rat::from_integer(BigInt::from(self.center)) / &scale;
        let radius = Rat::from_integer(BigInt::from(self.radius)) / scale;
        ExactInterval::new(&center - &radius, center + radius).map_err(MachineFactorError::Value)
    }

    pub fn contains_interval(&self, interval: &ExactInterval) -> Result<bool, MachineFactorError> {
        let enclosure = self.interval()?;
        Ok(enclosure.lower <= interval.lower && interval.upper <= enclosure.upper)
    }
}

/// A conservative bound for coefficient error in the returned native factor `B`.  Its words are
/// the L1 sum of all coefficient radii, which bounds the Euclidean operator norm as well.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FactorErrorBound {
    pub words: i128,
    pub grain: u32,
}

impl FactorErrorBound {
    pub fn interval(&self) -> Result<ExactInterval, MachineFactorError> {
        let scale = dyadic_scale(self.grain);
        let bound = Rat::from_integer(BigInt::from(self.words)) / scale;
        ExactInterval::new(-bound.clone(), bound).map_err(MachineFactorError::Value)
    }
}

/// A conservative complete bound for the induced Gram error `B_centreᵀB_centre − BᵀB`, in
/// dyadic words at the requested grain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GramErrorBound {
    pub words: i128,
    pub grain: u32,
}

impl GramErrorBound {
    pub fn interval(&self) -> Result<ExactInterval, MachineFactorError> {
        let scale = dyadic_scale(self.grain);
        let bound = Rat::from_integer(BigInt::from(self.words)) / scale;
        ExactInterval::new(-bound.clone(), bound).map_err(MachineFactorError::Value)
    }
}

/// Exact source and certified native lowering for one contact arc.
#[derive(Clone, Debug)]
pub struct MachineFactor {
    arc_id: String,
    rank: usize,
    response: ExactRatMatrix,
    effective_slip: ExactRatMatrix,
    weight: Rat,
    contact_form: ExactRatMatrix,
    response_factorization: ExactRankFactorization,
    response_reconstruction: ExactRatMatrix,
    metric: Option<ExactMetric>,
    rational_rows: ExactRatMatrix,
    roots: Vec<AlgebraicRoot>,
    native_rows: Vec<Vec<DyadicCenter128>>,
    factor_error: FactorErrorBound,
    gram_error: GramErrorBound,
}

impl MachineFactor {
    /// Lower one compiled pair contact.  `grain` is the native coefficient grain and must be in
    /// `1..=120`; this worker deliberately does not use the signed-64 resident enclosure.
    pub fn from_arc(
        arc: &CompiledGeneratorPairArc,
        grain: u32,
    ) -> Result<Self, MachineFactorError> {
        if !(1..=120).contains(&grain) {
            return Err(MachineFactorError::GrainOutOfRange(grain));
        }
        let contact = arc
            .interaction()
            .interaction()
            .contacts()
            .first()
            .ok_or(MachineFactorError::MissingContact)?;
        let response = form_matrix(contact.face().response())?;
        if response.rows() != 3 || response.columns() != 3 {
            return Err(MachineFactorError::ResponseShape {
                rows: response.rows(),
                columns: response.columns(),
            });
        }
        let effective_slip = arc.interaction().effective_slip().clone();
        if effective_slip.rows() != 3 || effective_slip.columns() != NATIVE_COLUMNS {
            return Err(MachineFactorError::SlipShape {
                rows: effective_slip.rows(),
                columns: effective_slip.columns(),
            });
        }
        let weight = contact.face().weight().clone();
        if !weight.is_positive() {
            return Err(MachineFactorError::NonPositiveWeight);
        }
        let contact_form = effective_slip
            .transpose()?
            .multiply(&response)?
            .multiply(&effective_slip)?
            .scaled(&weight);
        let response_factorization = response.rank_factorization()?;
        let rank = response_factorization.derived_rank;
        let (metric, rational_rows, response_reconstruction, roots, native_rows) = if rank == 0 {
            (
                None,
                ExactRatMatrix::zero(0, NATIVE_COLUMNS)?,
                ExactRatMatrix::zero(3, 3)?,
                Vec::new(),
                zero_rows(grain),
            )
        } else {
            let u = &response_factorization.left;
            let ut = u.transpose()?;
            let utu = ut.multiply(u)?;
            let l = utu.inverse()?.multiply(&ut)?;
            let q = l.multiply(&response)?.multiply(&l.transpose()?)?;
            let metric = ExactMetric::declared(format!("{}|response-image", arc.id()), q)?;
            let lower = &metric.certificate().lower;
            let ul = u.multiply(lower)?;
            let response_reconstruction = ul
                .multiply(&ExactRatMatrix::from_diagonal(
                    metric.certificate().pivots.clone(),
                )?)?
                .multiply(&ul.transpose()?)?;
            if response_reconstruction != response {
                return Err(MachineFactorError::CertificateMismatch(
                    "response reconstruction",
                ));
            }
            let rational_rows = lower
                .transpose()?
                .multiply(&ut.multiply(&effective_slip)?)?;
            let mut roots = Vec::with_capacity(rank);
            for pivot in &metric.certificate().pivots {
                roots.push(AlgebraicRoot::square_root(
                    &(weight.clone() * pivot),
                    grain,
                )?);
            }
            let native_rows = lower_rows(&rational_rows, &roots, grain)?;
            (
                Some(metric),
                rational_rows,
                response_reconstruction,
                roots,
                native_rows,
            )
        };
        let reconstructed_gram = gram_from_rows(
            &rational_rows,
            metric.as_ref().map(|m| m.certificate().pivots.as_slice()),
            &weight,
        )?;
        if reconstructed_gram != contact_form {
            return Err(MachineFactorError::CertificateMismatch("contact Gram law"));
        }
        let factor_error = factor_error(&native_rows, grain)?;
        let gram_error = gram_error(
            &native_rows,
            &rational_rows,
            &weight,
            metric.as_ref(),
            grain,
        )?;
        Ok(Self {
            arc_id: arc.id().to_owned(),
            rank,
            response,
            effective_slip,
            weight,
            contact_form,
            response_factorization,
            response_reconstruction,
            metric,
            rational_rows,
            roots,
            native_rows,
            factor_error,
            gram_error,
        })
    }

    pub fn arc_id(&self) -> &str {
        &self.arc_id
    }
    pub fn rank(&self) -> usize {
        self.rank
    }
    pub fn response(&self) -> &ExactRatMatrix {
        &self.response
    }
    pub fn effective_slip(&self) -> &ExactRatMatrix {
        &self.effective_slip
    }
    pub fn weight(&self) -> &Rat {
        &self.weight
    }
    pub fn contact_form(&self) -> &ExactRatMatrix {
        &self.contact_form
    }
    pub fn response_factorization(&self) -> &ExactRankFactorization {
        &self.response_factorization
    }
    pub fn response_reconstruction(&self) -> &ExactRatMatrix {
        &self.response_reconstruction
    }
    pub fn metric(&self) -> Option<&ExactMetric> {
        self.metric.as_ref()
    }
    pub fn metric_certificate(&self) -> Option<&MetricCertificate> {
        self.metric.as_ref().map(ExactMetric::certificate)
    }
    pub fn rational_rows(&self) -> &ExactRatMatrix {
        &self.rational_rows
    }
    pub fn roots(&self) -> &[AlgebraicRoot] {
        &self.roots
    }
    pub fn native_rows(&self) -> &[Vec<DyadicCenter128>] {
        &self.native_rows
    }
    pub fn factor_error(&self) -> FactorErrorBound {
        self.factor_error
    }
    pub fn gram_error(&self) -> GramErrorBound {
        self.gram_error
    }
}

#[derive(Debug, Error)]
pub enum MachineFactorError {
    #[error("native factor grain {0} is outside 1..=120")]
    GrainOutOfRange(u32),
    #[error("the compiled arc has no contact face")]
    MissingContact,
    #[error("the pair effective slip has shape {rows}×{columns}; expected 3×12")]
    SlipShape { rows: usize, columns: usize },
    #[error("the response has shape {rows}×{columns}; expected 3×3")]
    ResponseShape { rows: usize, columns: usize },
    #[error("the contact weight is not positive")]
    NonPositiveWeight,
    #[error("exact factor certificate failed for {0}")]
    CertificateMismatch(&'static str),
    #[error("signed-128 dyadic carrier overflow")]
    CarrierOverflow,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Metric(#[from] EditRigidityRefusal),
    #[error(transparent)]
    Value(#[from] ExactValueError),
}

fn form_matrix(
    form: &holonic_engine::inertia::SymmetricForm,
) -> Result<ExactRatMatrix, MachineFactorError> {
    ExactRatMatrix::new(
        (0..form.extent())
            .map(|row| {
                (0..form.extent())
                    .map(|column| form.at(row, column).clone())
                    .collect()
            })
            .collect(),
    )
    .map_err(MachineFactorError::Linear)
}

fn gram_from_rows(
    rows: &ExactRatMatrix,
    pivots: Option<&[Rat]>,
    weight: &Rat,
) -> Result<ExactRatMatrix, MachineFactorError> {
    let weighted = match pivots {
        Some(pivots) => {
            ExactRatMatrix::from_diagonal(pivots.iter().map(|pivot| weight * pivot).collect())?
        }
        None => ExactRatMatrix::zero(0, 0)?,
    };
    if rows.rows() == 0 {
        return ExactRatMatrix::zero(rows.columns(), rows.columns()).map_err(Into::into);
    }
    rows.transpose()?
        .multiply(&weighted)?
        .multiply(rows)
        .map_err(Into::into)
}

fn lower_rows(
    rows: &ExactRatMatrix,
    roots: &[AlgebraicRoot],
    grain: u32,
) -> Result<Vec<Vec<DyadicCenter128>>, MachineFactorError> {
    let mut result = zero_rows(grain);
    for row in 0..rows.rows() {
        for column in 0..rows.columns() {
            let coefficient = rows.get(row, column)?.clone();
            let interval =
                ExactInterval::point(coefficient).times(&roots[row].isolating_interval)?;
            result[row][column] = center_interval(&interval, grain)?;
        }
    }
    Ok(result)
}

fn zero_rows(grain: u32) -> Vec<Vec<DyadicCenter128>> {
    vec![vec![DyadicCenter128::zero(grain); NATIVE_COLUMNS]; NATIVE_ROWS]
}

fn center_interval(
    interval: &ExactInterval,
    grain: u32,
) -> Result<DyadicCenter128, MachineFactorError> {
    let scale = dyadic_scale(grain);
    let lower = (&interval.lower * &scale).floor().to_integer();
    let upper = (&interval.upper * &scale).ceil().to_integer();
    let lower = lower.to_i128().ok_or(MachineFactorError::CarrierOverflow)?;
    let upper = upper.to_i128().ok_or(MachineFactorError::CarrierOverflow)?;
    let sum = lower
        .checked_add(upper)
        .ok_or(MachineFactorError::CarrierOverflow)?;
    let center = sum / 2;
    let radius = (center - lower)
        .checked_abs()
        .ok_or(MachineFactorError::CarrierOverflow)?
        .max(
            (upper - center)
                .checked_abs()
                .ok_or(MachineFactorError::CarrierOverflow)?,
        );
    Ok(DyadicCenter128 {
        center,
        radius,
        grain,
    })
}

fn factor_error(
    native_rows: &[Vec<DyadicCenter128>],
    grain: u32,
) -> Result<FactorErrorBound, MachineFactorError> {
    let words = native_rows
        .iter()
        .flat_map(|row| row.iter())
        .try_fold(0i128, |sum, entry| {
            sum.checked_add(entry.radius)
                .ok_or(MachineFactorError::CarrierOverflow)
        })?;
    Ok(FactorErrorBound { words, grain })
}

fn gram_error(
    native_rows: &[Vec<DyadicCenter128>],
    rational_rows: &ExactRatMatrix,
    weight: &Rat,
    metric: Option<&ExactMetric>,
    grain: u32,
) -> Result<GramErrorBound, MachineFactorError> {
    if rational_rows.rows() == 0 {
        return Ok(GramErrorBound { words: 0, grain });
    }
    let pivots = &metric
        .ok_or(MachineFactorError::CertificateMismatch("rank metric"))?
        .certificate()
        .pivots;
    let scale = dyadic_scale(grain);
    let mut max_bound = Rat::zero();
    for left in 0..NATIVE_COLUMNS {
        for right in 0..NATIVE_COLUMNS {
            let mut bound = Rat::zero();
            for row in 0..rational_rows.rows() {
                let c_left =
                    Rat::from_integer(BigInt::from(native_rows[row][left].center)) / &scale;
                let c_right =
                    Rat::from_integer(BigInt::from(native_rows[row][right].center)) / &scale;
                let e_left =
                    Rat::from_integer(BigInt::from(native_rows[row][left].radius)) / &scale;
                let e_right =
                    Rat::from_integer(BigInt::from(native_rows[row][right].radius)) / &scale;
                let scale_factor = &(weight * &pivots[row]);
                bound += scale_factor
                    * (c_left.abs() * &e_right + c_right.abs() * &e_left + &e_left * &e_right);
            }
            if bound > max_bound {
                max_bound = bound;
            }
        }
    }
    let words = (&max_bound * &scale)
        .ceil()
        .to_integer()
        .to_i128()
        .ok_or(MachineFactorError::CarrierOverflow)?;
    Ok(GramErrorBound { words, grain })
}

fn dyadic_scale(grain: u32) -> Rat {
    Rat::from_integer(BigInt::from(BigUint::one() << grain as usize))
}

#[cfg(test)]
#[path = "machine_factor/tests.rs"]
mod tests;
