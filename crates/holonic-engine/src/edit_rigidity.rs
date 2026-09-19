//! **T4 — knot friction and edit torque: the kept receivers of an artifact as a rigidity
//! framework.**
//!
//! [definition] This module is the executable owner of item **T4** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its Lean
//! counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Transport/EditRigidity.lean`
//! (namespace `Soma.Holonics.Transport.EditRigidity`), and the correspondence is the deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `keptJacobian`, `the_kept_face_differential_is_the_rigidity_jacobian` | [`KeptReceiverJacobian::from_rigidity`] |
//! | `kept_rank_nullity`, `kept_self_stress_dimension` | [`kept_reading`]'s two checked identities, and [`identify_with_rigidity_reading`] |
//! | `linear_face_is_its_own_differential` | [`KeptReceiverJacobian::from_linear_faces`] |
//! | `Free`, `free_iff_mem_ker` | [`KeptReading::free_edits`], [`EditVerdict::Free`] |
//! | `Compensating`, `compensating_iff_solves` | [`rethreading_work`]'s one `preimage_fibre` call |
//! | `compensating_family_is_affine` | the returned particular plus `kernel_basis` |
//! | `free_iff_zero_compensates` | `the_free_edit_is_compensated_by_nothing` |
//! | `obstructed_iff_certificate` | [`ObstructionCertificate`], checked before it is returned |
//! | `mem_range_iff_annihilators_vanish` | `exact_linear::{preimage_fibre, preimage_obstruction}` |
//! | `selfStressSpace`, `selfStressSpace_rigidity` | [`KeptReading::self_stresses`] |
//! | `Entangled`, `entangled_iff_dependent` | [`KeptReading::entangled_faces`] |
//! | `dependent_iff_droppingLosesNothing` | [`verify_entanglement_by_dropping`] |
//! | `entanglement_is_self_stress_support` | [`KeptReading::entangled_faces`] beside `rigidity_receiver::removal_sensitivity` |
//! | `a_face_carrying_no_self_stress_forbids_an_edit_of_its_own` | [`face_own_edit`] |
//! | `first_order_edits_always_commute` | `first_order_edits_commute_so_commuting_separates_nothing` |
//! | `sqNorm`, `PosDef`, `positive_definite_of_ldl` | [`ExactMetric`], [`MetricCertificate`] |
//! | `sqNorm_eq_zero_iff`, `work_zero_iff_free` | [`rethreading_work`]'s verdict split, checked |
//! | `normal_equation_gives_the_unique_minimizer` | [`RethreadingReceipt::normal_equation_holds`] |
//! | `torque`, `torque_zero_iff_residual_annihilates_image` | [`edit_torque`], [`EditTorque::is_zero`] |
//! | `residual_expansion`, `stationary_iff_torque_zero` | [`EditTorque::is_zero`] and its test |
//! | `torque_nonzero_has_nonzero_image`, `the_exact_descent_step` | [`descent_step`], [`ExactDescent`] |
//! | `metric_adjoint_pairs_the_residual_with_the_generators` | [`edit_torque`]'s checked `adjoint_defect` probe |
//! | `mulVec_dotProduct_transpose` | `exact_linear::ExactRatMatrix::metric_adjoint` |
//! | `stationarity_is_not_cancellation` | `a_vanishing_torque_is_not_cancellation` |
//! | `pairRow`, `pairRow_pairing` | [`pair_row`] |
//! | `ImpliedBy`, `impliedBy_mono` | [`pair_is_implied_at`], [`knot_ascent`] |
//! | `AmbientKnot`, `ambient_knot_is_downward_closed` | `rigidity_receiver::rigid_clusters`, cited in [`artifact_knots`] |
//! | `induced_implication_does_not_descend` | `the_induced_implication_does_not_descend` |
//!
//! # It founds no second Jacobian
//!
//! [definition] `rigidity_receiver` owns `J = D F(q)`, its two null spaces, the rank–nullity
//! identities, the rigid clusters and the removal sensitivity. This module **consumes** that owner:
//! [`KeptReceiverJacobian::from_rigidity`] takes `RigidityJacobian::matrix` unchanged, and
//! [`identify_with_rigidity_reading`] refuses by name if the reading taken here disagrees with
//! `rigidity_receiver::rigidity_reading` on the rank, the free dimension or the self-stress
//! dimension. Every rank, kernel and cokernel below is one of
//! `exact_linear::ExactRatMatrix::{rank, kernel_basis, cokernel_annihilator, preimage_fibre,
//! preimage_obstruction, metric_adjoint}`; nothing here reimplements them.
//!
//! # What is new: the edit side
//!
//! [definition] `ker J_keep` is the **free edits** — the first-order directions no kept receiver
//! sees, which is `dog → cat` when the surrounding grammar keeps only "singular animal noun". A
//! proposed edit `g` is **compensable** over a declared allowed subspace exactly when one exact
//! linear system is consistent, and **obstructed** exactly when a left-null covector certifies that
//! it is not — the `is → why` case, returned with its certificate. `ker J_keepᵀ` is
//! **entanglement**: a kept face in the support of a self-stress is redundantly held, and the edits
//! its removal would free are exactly the edits the other faces already forbid.
//!
//! # Which of T3's three relations this is
//!
//! [established-bounded] `artifact_release` (T3) proves "independent versus entangled" is three
//! relations — commuting on the family, chartwise locality, constraint entanglement — and that
//! `dog → cat` against `is → why` is separated only by the third. **The linear notion here is the
//! third, at first order, and neither of the other two.** It is not commuting: in a linear chart
//! every pair of first-order edits commutes, because edit directions add, so commuting separates
//! nothing here at all. It is not chartwise locality: a first-order direction has no read/write
//! distinction at all, which is a property of the discrete `EditAction` and not of its
//! differential. The discrete law is T3's; this is its first-order chart.
//!
//! # The scalar is one receiver of the edit, never its identity
//!
//! [definition] `W²` is an exact rational — never a square root and never a float — and it comes
//! with a `presentation_cost::CostReceipt` whose five coordinates carry the compensation's support,
//! the coordinates touched and the kept faces that must be re-read to certify it. Two edits can
//! carry the **same** `W²` with Pareto-incomparable receipts, and a second declared metric can
//! order them in the opposite direction: a ranking of edits by friction is a declared receiver and
//! not a fact about the artifact. The unit metric is one declaration; this module supplies no
//! default.
//!
//! # No floats, and every declared size is bounded before it is used
//!
//! [implemented-exact] Every coordinate, metric entry, compensation, work and torque is an exact
//! `Rat` (`BigRational`); counts are `usize`/`BigUint`. No `f32`/`f64` appears anywhere in this
//! module. Every caller-declared extent — chart dimension, kept-face count, allowed-basis size,
//! generator count, region ladder size and their products — is checked with checked arithmetic
//! against a named ceiling **before** the allocation or elimination it sizes, and exceeding one is
//! a typed [`EditRigidityRefusal`], never a panic.

use std::collections::BTreeSet;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::presentation_cost::{Counted, CostReceipt};
use crate::rigidity_receiver::{
    RigidClusterReading, RigidityError, RigidityJacobian, RigidityReading, rigid_clusters,
};

// -------------------------------------------------------------------------------------------
// Declared ceilings
// -------------------------------------------------------------------------------------------

/// The widest exact linear chart a caller may declare: the number of coordinates in `ℚ^n`.
pub const CHART_CEILING: usize = 4096;
/// The largest kept receiver family a caller may declare, in rows.
pub const KEPT_FACE_CEILING: usize = 4096;
/// The largest allowed-compensation basis a caller may declare, in columns.
pub const ALLOWED_BASIS_CEILING: usize = 4096;
/// The largest admitted generator family a torque reading may declare.
pub const GENERATOR_CEILING: usize = 1024;
/// The largest number of scales one region ladder may declare.
pub const LADDER_SCALE_CEILING: usize = 256;
/// The largest number of regions one scale may declare.
pub const SCALE_REGION_CEILING: usize = 1024;
/// The largest `rows × columns` product any elimination in this module may be handed.
pub const ELIMINATION_WORK_CEILING: usize = 1 << 24;
/// The ceiling on a **repeated** pass: `passes × faces × coordinates` for a function that scans or
/// eliminates the kept chart once per region or once per face. Each factor has its own ceiling;
/// the product is what the machine does, so the product is what is bounded before the first pass.
pub const REPEATED_PASS_WORK_CEILING: usize = 1 << 28;
/// The largest declared probe an adjoint or entanglement check may run over.
pub const PROBE_CEILING: usize = 1 << 20;
/// The largest `extent³` an exact `LDLᵀ` metric factorization may be handed. The factorization is
/// this module's own triple loop, so its cubic work is bounded here and not left to the chart
/// dimension alone.
pub const METRIC_FACTORIZATION_CEILING: usize = 1 << 27;

/// The product of declared extents, or `None` when it overflows the machine integer counting it.
fn declared_work(factors: &[usize]) -> Option<usize> {
    factors
        .iter()
        .try_fold(1usize, |carried, factor| carried.checked_mul((*factor).max(1)))
}

fn bounded(what: &'static str, declared: usize, ceiling: usize) -> Result<(), EditRigidityRefusal> {
    if declared > ceiling {
        return Err(EditRigidityRefusal::DeclarationAboveCeiling {
            what,
            declared,
            ceiling,
        });
    }
    Ok(())
}

fn bounded_product(
    what: &'static str,
    factors: &[usize],
    ceiling: usize,
) -> Result<usize, EditRigidityRefusal> {
    let work = declared_work(factors).ok_or(EditRigidityRefusal::WorkOverflows { what })?;
    bounded(what, work, ceiling)?;
    Ok(work)
}

// -------------------------------------------------------------------------------------------
// Typed refusals
// -------------------------------------------------------------------------------------------

/// Every way this module declines to answer. A refusal is content; nothing here panics.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum EditRigidityRefusal {
    /// The exact linear carrier refused.
    #[error("the exact linear carrier refused: {0}")]
    Linear(#[from] ExactLinearError),
    /// The rigidity receiver refused.
    #[error("the rigidity receiver refused: {0}")]
    Rigidity(#[from] RigidityError),
    /// A declared extent exceeded its named ceiling. Nothing was allocated.
    #[error("{what} declared {declared}, above the ceiling {ceiling}; nothing was allocated")]
    DeclarationAboveCeiling {
        /// What was declared.
        what: &'static str,
        /// The declared extent.
        declared: usize,
        /// The ceiling it exceeded.
        ceiling: usize,
    },
    /// The work a declaration asks for does not fit the machine integer counting it.
    #[error("the work {what} asks for overflows the machine integer counting it; nothing ran")]
    WorkOverflows {
        /// What was declared.
        what: &'static str,
    },
    /// A chart of zero coordinates carries no edit.
    #[error("a chart of zero coordinates carries no edit direction and no kept face")]
    EmptyChart,
    /// A kept receiver family with no face restricts nothing, so it is not a kept family.
    #[error("a kept receiver family with no face restricts nothing and is refused by name")]
    EmptyKeptFamily,
    /// Two declared widths disagree.
    #[error("{what}: a width of {declared} does not pair with one of {found}")]
    WidthDisagrees {
        /// What was compared.
        what: &'static str,
        /// The declared width.
        declared: usize,
        /// The found width.
        found: usize,
    },
    /// A declared coordinate lies outside the chart.
    #[error("coordinate {coordinate} lies outside a chart of {dimension} coordinates")]
    CoordinateOutsideChart {
        /// The coordinate asked for.
        coordinate: usize,
        /// The chart's dimension.
        dimension: usize,
    },
    /// A declared kept-face index lies outside the family.
    #[error("kept face {face} lies outside a family of {faces} faces")]
    FaceOutsideFamily {
        /// The face asked for.
        face: usize,
        /// The family's size.
        faces: usize,
    },
    /// A declared Gram matrix is not symmetric.
    #[error("the declared metric {metric:?} is not symmetric at ({row}, {column})")]
    MetricNotSymmetric {
        /// The metric's declared name.
        metric: String,
        /// The row.
        row: usize,
        /// The column.
        column: usize,
    },
    /// A declared Gram matrix has a non-positive exact `LDLᵀ` pivot, so it is not positive
    /// definite and is refused rather than repaired.
    #[error(
        "the declared metric {metric:?} has the non-positive exact pivot {pivot} at coordinate \
         {coordinate}; a metric that is not positive definite decides no rethreading work"
    )]
    MetricNotPositiveDefinite {
        /// The metric's declared name.
        metric: String,
        /// The coordinate whose pivot failed.
        coordinate: usize,
        /// The exact pivot, as a decimal-free ratio.
        pivot: String,
    },
    /// The exact `LDLᵀ` factorization did not reconstruct the declared Gram matrix.
    #[error(
        "the exact LDL^T factorization of the declared metric {metric:?} does not reconstruct it \
         at ({row}, {column}); the certificate is refused rather than trusted"
    )]
    MetricFactorizationDisagrees {
        /// The metric's declared name.
        metric: String,
        /// The row.
        row: usize,
        /// The column.
        column: usize,
    },
    /// The triangular factor of a declared metric is singular, so the factorization certifies
    /// nothing.
    #[error(
        "the triangular factor of the declared metric {metric:?} has rank {rank} below its extent \
         {extent}, so the LDL^T certificate establishes nothing"
    )]
    MetricFactorSingular {
        /// The metric's declared name.
        metric: String,
        /// The measured rank.
        rank: usize,
        /// The extent it should have had.
        extent: usize,
    },
    /// The reading taken here disagrees with `rigidity_receiver`'s own reading of the same
    /// Jacobian. This module claims to be reading R4's object; if it is not, it says so.
    #[error(
        "the kept reading disagrees with rigidity_receiver's reading of the same Jacobian: \
         {what} is {here} here and {there} there"
    )]
    IdentificationFails {
        /// Which count disagreed.
        what: &'static str,
        /// What this module read.
        here: usize,
        /// What `rigidity_receiver` read.
        there: usize,
    },
    /// Rank–nullity failed on the kept Jacobian; the elimination is wrong and nothing is returned.
    #[error("rank {rank} plus free dimension {free} is not the chart width {dimension}")]
    RankNullityFails {
        /// The measured rank.
        rank: usize,
        /// The measured free dimension.
        free: usize,
        /// The chart width.
        dimension: usize,
    },
    /// The self-stress count failed on the kept Jacobian.
    #[error("rank {rank} plus self-stress dimension {stress} is not the face count {faces}")]
    SelfStressCountFails {
        /// The measured rank.
        rank: usize,
        /// The measured self-stress dimension.
        stress: usize,
        /// The face count.
        faces: usize,
    },
    /// A returned compensation does not actually restore the kept faces.
    #[error(
        "the returned compensation leaves kept face {face} with a nonzero first-order defect; the \
         minimizer is refused rather than reported"
    )]
    CompensationDoesNotCompensate {
        /// The face that still moves.
        face: usize,
    },
    /// The normal equation the minimizer must satisfy does not hold.
    #[error(
        "the returned compensation fails its normal equation at allowed direction {direction}, so \
         it is not the minimizer and is refused"
    )]
    NormalEquationFails {
        /// The allowed direction at which it failed.
        direction: usize,
    },
    /// The normal equations were inconsistent, which a positive-definite metric forbids.
    #[error(
        "the normal equations of the declared metric are inconsistent; a positive-definite metric \
         makes them consistent, so the declared metric or the elimination is wrong"
    )]
    NormalEquationInconsistent,
    /// `W² = 0` and the edit is not free, or the converse. A positive-definite metric forbids it.
    #[error(
        "the squared rethreading work is zero exactly when the edit is free, and here work-is-zero \
         is {work_is_zero} while free is {is_free}"
    )]
    WorkVerdictDisagrees {
        /// Whether `W²` vanished.
        work_is_zero: bool,
        /// Whether the edit was free.
        is_free: bool,
    },
    /// The system was inconsistent and no annihilator was found, which the Fredholm alternative
    /// forbids.
    #[error(
        "the compensating system is inconsistent and no left-null certificate was returned; the \
         Fredholm alternative forbids that, so the elimination is refused"
    )]
    ObstructionWithoutCertificate,
    /// A returned obstruction certificate does not certify.
    #[error(
        "the returned obstruction certificate fails its own check at {what}; it is refused rather \
         than reported"
    )]
    CertificateFails {
        /// Which half failed.
        what: &'static str,
    },
    /// A claimed adjoint failed its characterization on the declared probe.
    #[error(
        "the claimed adjoint has the nonzero defect {defect} at generator {generator} and receiver \
         {receiver}; the adjoint is refused rather than used"
    )]
    AdjointDefect {
        /// The generator coordinate.
        generator: usize,
        /// The receiver coordinate.
        receiver: usize,
        /// The exact defect, as a ratio.
        defect: String,
    },
    /// A check was offered an empty probe. A check over an empty probe is not a check.
    #[error(
        "{what} was offered an empty probe; a conclusion checked at no element is not a checked \
         conclusion and is refused by name"
    )]
    EmptyProbe {
        /// What was being checked.
        what: &'static str,
    },
    /// A descent step was asked of a vanishing torque.
    #[error("a vanishing torque admits no descent step; stationarity is the return")]
    NoDescentFromZeroTorque,
    /// A declared region ladder carries no scale.
    #[error("a region ladder with no scale reads no knot and is refused by name")]
    EmptyLadder,
    /// A declared region carries no coordinate.
    #[error("the scale {scale:?} declares a region with no coordinate, which induces no framework")]
    EmptyRegion {
        /// The scale carrying the empty region.
        scale: String,
    },
    /// A declared scale carries no region.
    #[error("the scale {scale:?} declares no region, so it reads no knot")]
    EmptyScale {
        /// The scale's declared name.
        scale: String,
    },
}

// -------------------------------------------------------------------------------------------
// T4 (a) — the kept-receiver constraint map
// -------------------------------------------------------------------------------------------

/// Where one row of `J_keep` came from. A row is never anonymous: either it is
/// `rigidity_receiver`'s own Jacobian row for a declared squared separation, or it is a declared
/// exact linear form whose differential is itself.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "origin", rename_all = "kebab-case")]
pub enum KeptFaceOrigin {
    /// R4's own row `2(q_i − q_j)` for the constraint at this ordinal of that Jacobian.
    ///
    /// Lean counterpart: `keptJacobian`, with
    /// `the_kept_face_differential_is_the_rigidity_jacobian`.
    RigidityRow {
        /// The presentation the Jacobian was read at.
        presentation_lineage: String,
        /// The constraint's ordinal in that Jacobian's canonical edge order.
        constraint: usize,
    },
    /// A declared exact linear form of the chart coordinates. Its differential is the form.
    ///
    /// Lean counterpart: `linear_face_is_its_own_differential`.
    LinearForm {
        /// The face's declared name.
        name: String,
    },
}

/// **`J_keep`: the exact Jacobian of a declared kept receiver family at one artifact.**
///
/// The fields are private and the only constructors validate: the matrix is exactly as wide as the
/// declared chart, exactly as tall as the origin list, and both extents are bounded before the
/// matrix is formed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct KeptReceiverJacobian {
    schema: String,
    lineage: String,
    dimension: usize,
    origins: Vec<KeptFaceOrigin>,
    matrix: ExactRatMatrix,
}

impl KeptReceiverJacobian {
    /// **The identification.** The kept-receiver Jacobian of a declared family of squared
    /// separations **is** `rigidity_receiver`'s matrix: the rows are taken unchanged and no second
    /// differential is computed.
    ///
    /// Lean counterpart: `Transport/EditRigidity.lean::keptJacobian` and
    /// `the_kept_face_differential_is_the_rigidity_jacobian`, which is
    /// `Foundation/RigidityReceiver.lean::jacobian_is_the_differential` cited.
    pub fn from_rigidity(jacobian: &RigidityJacobian) -> Result<Self, EditRigidityRefusal> {
        jacobian.validated()?;
        let dimension = jacobian.coordinate_freedoms();
        bounded("a kept chart dimension", dimension, CHART_CEILING)?;
        bounded(
            "a kept receiver family size",
            jacobian.constraint_count(),
            KEPT_FACE_CEILING,
        )?;
        if dimension == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        if jacobian.constraint_count() == 0 {
            return Err(EditRigidityRefusal::EmptyKeptFamily);
        }
        let origins = (0..jacobian.constraint_count())
            .map(|constraint| KeptFaceOrigin::RigidityRow {
                presentation_lineage: jacobian.presentation_lineage.clone(),
                constraint,
            })
            .collect();
        Ok(Self {
            schema: KEPT_JACOBIAN_SCHEMA.to_owned(),
            lineage: jacobian.presentation_lineage.clone(),
            dimension,
            origins,
            matrix: jacobian.matrix.clone(),
        })
    }

    /// The Jacobian of a declared family of exact **linear** kept faces. A linear form is its own
    /// differential, so the row is the form.
    pub fn from_linear_faces(
        lineage: impl Into<String>,
        dimension: usize,
        faces: Vec<(String, Vec<Rat>)>,
    ) -> Result<Self, EditRigidityRefusal> {
        if dimension == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        bounded("a kept chart dimension", dimension, CHART_CEILING)?;
        bounded("a kept receiver family size", faces.len(), KEPT_FACE_CEILING)?;
        if faces.is_empty() {
            return Err(EditRigidityRefusal::EmptyKeptFamily);
        }
        bounded_product(
            "a kept Jacobian",
            &[faces.len(), dimension],
            ELIMINATION_WORK_CEILING,
        )?;
        let mut origins = Vec::with_capacity(faces.len());
        let mut rows = Vec::with_capacity(faces.len());
        for (name, row) in faces {
            if row.len() != dimension {
                return Err(EditRigidityRefusal::WidthDisagrees {
                    what: "a declared linear kept face",
                    declared: dimension,
                    found: row.len(),
                });
            }
            origins.push(KeptFaceOrigin::LinearForm { name });
            rows.push(row);
        }
        let matrix = ExactRatMatrix::shaped(origins.len(), dimension, rows)?;
        Ok(Self {
            schema: KEPT_JACOBIAN_SCHEMA.to_owned(),
            lineage: lineage.into(),
            dimension,
            origins,
            matrix,
        })
    }

    /// Two kept families over the same chart, as one Jacobian. The row order is this one's rows
    /// followed by the other's.
    pub fn joined(&self, other: &Self) -> Result<Self, EditRigidityRefusal> {
        if self.dimension != other.dimension {
            return Err(EditRigidityRefusal::WidthDisagrees {
                what: "a joined kept family",
                declared: self.dimension,
                found: other.dimension,
            });
        }
        let faces = self.origins.len() + other.origins.len();
        bounded("a kept receiver family size", faces, KEPT_FACE_CEILING)?;
        bounded_product(
            "a joined kept Jacobian",
            &[faces, self.dimension],
            ELIMINATION_WORK_CEILING,
        )?;
        let mut rows = self.matrix.to_rows();
        rows.extend(other.matrix.to_rows());
        let mut origins = self.origins.clone();
        origins.extend(other.origins.iter().cloned());
        let matrix = ExactRatMatrix::shaped(faces, self.dimension, rows)?;
        Ok(Self {
            schema: KEPT_JACOBIAN_SCHEMA.to_owned(),
            lineage: format!("{}+{}", self.lineage, other.lineage),
            dimension: self.dimension,
            origins,
            matrix,
        })
    }

    /// What this kept family is the kept family of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The chart's dimension: the number of exact rational coordinates.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// How many kept faces the family declares.
    pub fn face_count(&self) -> usize {
        self.origins.len()
    }

    /// Where each row came from.
    pub fn origins(&self) -> &[KeptFaceOrigin] {
        &self.origins
    }

    /// The exact matrix. This is `rigidity_receiver`'s own matrix when the family came from one.
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.matrix
    }

    /// The chart coordinates one kept face reads.
    pub fn face_support(&self, face: usize) -> Result<BTreeSet<usize>, EditRigidityRefusal> {
        if face >= self.origins.len() {
            return Err(EditRigidityRefusal::FaceOutsideFamily {
                face,
                faces: self.origins.len(),
            });
        }
        let row = self.matrix.row(face)?;
        Ok(row
            .iter()
            .enumerate()
            .filter(|(_, entry)| !entry.is_zero())
            .map(|(at, _)| at)
            .collect())
    }

    /// The shape invariants, checked by name.
    pub fn validated(&self) -> Result<(), EditRigidityRefusal> {
        if self.dimension == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        if self.origins.is_empty() {
            return Err(EditRigidityRefusal::EmptyKeptFamily);
        }
        if self.matrix.columns() != self.dimension {
            return Err(EditRigidityRefusal::WidthDisagrees {
                what: "a kept Jacobian's chart",
                declared: self.dimension,
                found: self.matrix.columns(),
            });
        }
        if self.matrix.rows() != self.origins.len() {
            return Err(EditRigidityRefusal::WidthDisagrees {
                what: "a kept Jacobian's face population",
                declared: self.origins.len(),
                found: self.matrix.rows(),
            });
        }
        Ok(())
    }
}

/// **The reading of one kept receiver family: the free edits and the entanglement.**
///
/// Both null spaces come from `exact_linear`, and both rank identities are re-derived at every
/// reading and refuse by name on disagreement — exactly as `rigidity_receiver::rigidity_reading`
/// does, because it is the same object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct KeptReading {
    /// The wire schema.
    pub schema: String,
    /// What the family is the family of.
    pub lineage: String,
    /// The chart's dimension.
    pub dimension: usize,
    /// How many kept faces.
    pub face_count: usize,
    /// `rank J_keep`, exact.
    pub rank: usize,
    /// A basis of `ker J_keep`: the free edit directions, exhibited rather than counted.
    pub free_edits: Vec<Vec<Rat>>,
    /// `dim ker J_keep`.
    pub free_dimension: usize,
    /// A basis of `ker J_keepᵀ`: the self-stresses.
    pub self_stresses: Vec<Vec<Rat>>,
    /// `dim ker J_keepᵀ`.
    pub self_stress_dimension: usize,
    /// **Entanglement**: the kept faces in the support of some self-stress. Each is redundantly
    /// held, and dropping it frees no edit the other faces do not already forbid.
    pub entangled_faces: Vec<usize>,
    /// The kept faces carrying no self-stress. Each forbids an edit of its own, exhibited by
    /// [`face_own_edit`].
    pub load_bearing_faces: Vec<usize>,
}

impl KeptReading {
    /// Whether any kept face is redundantly held.
    pub fn is_redundant(&self) -> bool {
        self.self_stress_dimension > 0
    }

    /// Whether the kept family sees every first-order edit.
    pub fn every_edit_is_seen(&self) -> bool {
        self.free_dimension == 0
    }
}

/// **`rank J_keep`, `ker J_keep` and `ker J_keepᵀ`, with both identities checked.**
pub fn kept_reading(jacobian: &KeptReceiverJacobian) -> Result<KeptReading, EditRigidityRefusal> {
    jacobian.validated()?;
    bounded_product(
        "a kept reading",
        &[jacobian.matrix.rows(), jacobian.matrix.columns()],
        ELIMINATION_WORK_CEILING,
    )?;
    let rank = jacobian.matrix.rank()?;
    let free_edits = jacobian.matrix.kernel_basis()?;
    let free_dimension = free_edits.len();
    if rank + free_dimension != jacobian.dimension {
        return Err(EditRigidityRefusal::RankNullityFails {
            rank,
            free: free_dimension,
            dimension: jacobian.dimension,
        });
    }
    let self_stresses = jacobian.matrix.cokernel_annihilator()?;
    let self_stress_dimension = self_stresses.len();
    if rank + self_stress_dimension != jacobian.face_count() {
        return Err(EditRigidityRefusal::SelfStressCountFails {
            rank,
            stress: self_stress_dimension,
            faces: jacobian.face_count(),
        });
    }
    let mut entangled_faces = Vec::new();
    let mut load_bearing_faces = Vec::new();
    for face in 0..jacobian.face_count() {
        let entangled = self_stresses
            .iter()
            .any(|stress| stress.get(face).is_some_and(|entry| !entry.is_zero()));
        if entangled {
            entangled_faces.push(face);
        } else {
            load_bearing_faces.push(face);
        }
    }
    Ok(KeptReading {
        schema: KEPT_READING_SCHEMA.to_owned(),
        lineage: jacobian.lineage.clone(),
        dimension: jacobian.dimension,
        face_count: jacobian.face_count(),
        rank,
        free_edits,
        free_dimension,
        self_stresses,
        self_stress_dimension,
        entangled_faces,
        load_bearing_faces,
    })
}

/// **The identification, executed.** The reading taken here and `rigidity_receiver`'s own reading
/// of the same Jacobian must agree on the rank, the free dimension and the self-stress dimension.
///
/// Lean counterpart: `kept_rank_nullity` and `kept_self_stress_dimension`, which are R4's own
/// `rank_nullity` and `self_stress_dimension` cited at `keptJacobian`.
pub fn identify_with_rigidity_reading(
    kept: &KeptReading,
    rigidity: &RigidityReading,
) -> Result<(), EditRigidityRefusal> {
    if kept.rank != rigidity.rank {
        return Err(EditRigidityRefusal::IdentificationFails {
            what: "the rank",
            here: kept.rank,
            there: rigidity.rank,
        });
    }
    if kept.free_dimension != rigidity.motion_dimension {
        return Err(EditRigidityRefusal::IdentificationFails {
            what: "the free-edit dimension",
            here: kept.free_dimension,
            there: rigidity.motion_dimension,
        });
    }
    if kept.self_stress_dimension != rigidity.self_stress_dimension {
        return Err(EditRigidityRefusal::IdentificationFails {
            what: "the self-stress dimension",
            here: kept.self_stress_dimension,
            there: rigidity.self_stress_dimension,
        });
    }
    if kept.face_count != rigidity.constraint_count {
        return Err(EditRigidityRefusal::IdentificationFails {
            what: "the kept-face count",
            here: kept.face_count,
            there: rigidity.constraint_count,
        });
    }
    Ok(())
}

/// **The edit a load-bearing face forbids and no other face forbids.**
///
/// Returns a direction free at every kept face but this one, or `None` when the face is entangled —
/// in which case no such direction exists, which is the same theorem read the other way.
///
/// Lean counterpart: `a_face_carrying_no_self_stress_forbids_an_edit_of_its_own`.
pub fn face_own_edit(
    jacobian: &KeptReceiverJacobian,
    face: usize,
) -> Result<Option<Vec<Rat>>, EditRigidityRefusal> {
    jacobian.validated()?;
    if face >= jacobian.face_count() {
        return Err(EditRigidityRefusal::FaceOutsideFamily {
            face,
            faces: jacobian.face_count(),
        });
    }
    let mut rows = jacobian.matrix.to_rows();
    rows[face] = vec![Rat::zero(); jacobian.dimension];
    let dropped = ExactRatMatrix::shaped(rows.len(), jacobian.dimension, rows)?;
    for candidate in dropped.kernel_basis()? {
        let image = jacobian.matrix.apply(&candidate)?;
        if !image[face].is_zero() {
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

/// **Entanglement re-derived by actually dropping the face.**
///
/// The self-stress criterion is a theorem — `dependent_iff_droppingLosesNothing` — so this cannot
/// disagree while the elimination is correct; that is what it is for. Returns how many faces were
/// checked, and **refuses an empty family by name**: a criterion checked at no face is not checked.
pub fn verify_entanglement_by_dropping(
    jacobian: &KeptReceiverJacobian,
    reading: &KeptReading,
    bound: usize,
) -> Result<usize, EditRigidityRefusal> {
    jacobian.validated()?;
    if jacobian.face_count() == 0 {
        return Err(EditRigidityRefusal::EmptyProbe {
            what: "the entanglement cross-check",
        });
    }
    if bound == 0 {
        return Err(EditRigidityRefusal::EmptyProbe {
            what: "the entanglement cross-check",
        });
    }
    bounded("an entanglement cross-check bound", bound, PROBE_CEILING)?;
    let checked = bound.min(jacobian.face_count());
    // One elimination of the dropped chart per checked face: bounded as a product, and each
    // single elimination against its own ceiling rather than by a coincidence of constants.
    bounded_product(
        "a dropped-face elimination",
        &[jacobian.face_count(), jacobian.dimension()],
        ELIMINATION_WORK_CEILING,
    )?;
    bounded_product(
        "an entanglement cross-check",
        &[checked, jacobian.face_count(), jacobian.dimension()],
        REPEATED_PASS_WORK_CEILING,
    )?;
    for face in 0..checked {
        let claimed = reading.entangled_faces.contains(&face);
        let own = face_own_edit(jacobian, face)?;
        // `own.is_some()` means dropping the face frees an edit the others forbid, which is
        // exactly "no self-stress is supported here".
        if claimed == own.is_some() {
            return Err(EditRigidityRefusal::IdentificationFails {
                what: "the entanglement of a kept face against its dropped reading",
                here: usize::from(claimed),
                there: usize::from(own.is_some()),
            });
        }
    }
    Ok(checked)
}

// -------------------------------------------------------------------------------------------
// T4 (b) — edits, allowed compensation and the declared metric
// -------------------------------------------------------------------------------------------

/// **One first-order edit direction** in the chart, with its declared name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EditDirection {
    name: String,
    vector: Vec<Rat>,
}

impl EditDirection {
    /// Declare an edit direction over a chart of the given dimension.
    pub fn declared(
        name: impl Into<String>,
        vector: Vec<Rat>,
    ) -> Result<Self, EditRigidityRefusal> {
        if vector.is_empty() {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        bounded("an edit direction width", vector.len(), CHART_CEILING)?;
        Ok(Self {
            name: name.into(),
            vector,
        })
    }

    /// The edit's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The exact direction.
    pub fn vector(&self) -> &[Rat] {
        &self.vector
    }

    /// The chart's dimension this direction is declared over.
    pub fn dimension(&self) -> usize {
        self.vector.len()
    }

    /// **The coordinates this edit writes.**
    pub fn support(&self) -> BTreeSet<usize> {
        self.vector
            .iter()
            .enumerate()
            .filter(|(_, entry)| !entry.is_zero())
            .map(|(at, _)| at)
            .collect()
    }
}

/// **The declared allowed compensation subspace**: the directions the rethreading is permitted to
/// move, as the columns of an exact rational matrix.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AllowedCompensation {
    name: String,
    dimension: usize,
    basis: Vec<Vec<Rat>>,
}

impl AllowedCompensation {
    /// Declare an allowed subspace by an explicit basis of chart directions.
    pub fn declared(
        name: impl Into<String>,
        dimension: usize,
        basis: Vec<Vec<Rat>>,
    ) -> Result<Self, EditRigidityRefusal> {
        if dimension == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        bounded("an allowed-compensation chart", dimension, CHART_CEILING)?;
        bounded(
            "an allowed-compensation basis",
            basis.len(),
            ALLOWED_BASIS_CEILING,
        )?;
        bounded_product(
            "an allowed-compensation matrix",
            &[basis.len(), dimension],
            ELIMINATION_WORK_CEILING,
        )?;
        for column in &basis {
            if column.len() != dimension {
                return Err(EditRigidityRefusal::WidthDisagrees {
                    what: "an allowed-compensation basis vector",
                    declared: dimension,
                    found: column.len(),
                });
            }
        }
        Ok(Self {
            name: name.into(),
            dimension,
            basis,
        })
    }

    /// The subspace spanned by the declared chart coordinates: "these coordinates may move".
    pub fn coordinates(
        name: impl Into<String>,
        dimension: usize,
        coordinates: impl IntoIterator<Item = usize>,
    ) -> Result<Self, EditRigidityRefusal> {
        let mut basis = Vec::new();
        // The caller's iterator is unbounded, so each element is checked **as it arrives**, the
        // basis can never grow past the chart's own width, and the number of elements consumed is
        // itself bounded — an endless iterator is refused rather than walked.
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut consumed = 0usize;
        for coordinate in coordinates {
            consumed += 1;
            if consumed > CHART_CEILING {
                return Err(EditRigidityRefusal::DeclarationAboveCeiling {
                    what: "an allowed-coordinate declaration",
                    declared: consumed,
                    ceiling: CHART_CEILING,
                });
            }
            if coordinate >= dimension {
                return Err(EditRigidityRefusal::CoordinateOutsideChart {
                    coordinate,
                    dimension,
                });
            }
            if !seen.insert(coordinate) {
                continue;
            }
            let mut column = vec![Rat::zero(); dimension];
            column[coordinate] = Rat::one();
            basis.push(column);
        }
        Self::declared(name, dimension, basis)
    }

    /// Every coordinate **except** the declared ones: the rethreading moves what the edit does not.
    pub fn complement_of(
        name: impl Into<String>,
        dimension: usize,
        excluded: &BTreeSet<usize>,
    ) -> Result<Self, EditRigidityRefusal> {
        for coordinate in excluded {
            if *coordinate >= dimension {
                return Err(EditRigidityRefusal::CoordinateOutsideChart {
                    coordinate: *coordinate,
                    dimension,
                });
            }
        }
        Self::coordinates(
            name,
            dimension,
            (0..dimension).filter(|coordinate| !excluded.contains(coordinate)),
        )
    }

    /// The subspace's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The chart's dimension.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// How many allowed directions.
    pub fn rank_bound(&self) -> usize {
        self.basis.len()
    }

    /// The exact directions.
    pub fn basis(&self) -> &[Vec<Rat>] {
        &self.basis
    }

    /// The `n × k` matrix whose columns are the allowed directions.
    pub fn matrix(&self) -> Result<ExactRatMatrix, EditRigidityRefusal> {
        let rows = (0..self.dimension)
            .map(|row| {
                self.basis
                    .iter()
                    .map(|column| column[row].clone())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Ok(ExactRatMatrix::shaped(self.dimension, self.basis.len(), rows)?)
    }
}

/// The exact `LDLᵀ` certificate of a declared metric's positive definiteness.
///
/// Lean counterpart: `positive_definite_of_ldl`. Every one of that theorem's hypotheses is checked
/// here on the actual data: the Gram matrix is symmetric, the pivots are strictly positive, the
/// factorization reconstructs the Gram matrix exactly, and the triangular factor has full rank.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MetricCertificate {
    /// The exact pivots `d_k`, all strictly positive.
    pub pivots: Vec<Rat>,
    /// The unit lower-triangular factor `L`.
    pub lower: ExactRatMatrix,
    /// The measured rank of `L`, which equals the extent.
    pub factor_rank: usize,
}

/// **A declared exact positive-definite metric.** The unit metric is one declaration; there is no
/// default, and a Gram matrix that fails the certificate is refused rather than repaired.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactMetric {
    name: String,
    gram: ExactRatMatrix,
    certificate: MetricCertificate,
}

impl ExactMetric {
    /// Declare a metric from an exact rational Gram matrix, checking the whole `LDLᵀ` certificate.
    pub fn declared(
        name: impl Into<String>,
        gram: ExactRatMatrix,
    ) -> Result<Self, EditRigidityRefusal> {
        let name = name.into();
        let extent = gram.rows();
        if extent == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        if gram.columns() != extent {
            return Err(EditRigidityRefusal::WidthDisagrees {
                what: "a declared metric",
                declared: extent,
                found: gram.columns(),
            });
        }
        bounded("a declared metric extent", extent, CHART_CEILING)?;
        // The factorization below is a triple loop over the declared extent, so the **cube** is
        // what is bounded, before a single pivot is formed.
        bounded_product(
            "a declared metric factorization",
            &[extent, extent, extent],
            METRIC_FACTORIZATION_CEILING,
        )?;
        for row in 0..extent {
            for column in 0..row {
                if gram.get(row, column)? != gram.get(column, row)? {
                    return Err(EditRigidityRefusal::MetricNotSymmetric {
                        metric: name,
                        row,
                        column,
                    });
                }
            }
        }
        // Exact rational LDL^T. No square root is taken, so nothing leaves the rationals.
        let mut lower = vec![vec![Rat::zero(); extent]; extent];
        let mut pivots = vec![Rat::zero(); extent];
        for k in 0..extent {
            lower[k][k] = Rat::one();
            let mut pivot = gram.get(k, k)?.clone();
            for j in 0..k {
                pivot -= &lower[k][j] * &lower[k][j] * &pivots[j];
            }
            if !pivot.is_positive() {
                return Err(EditRigidityRefusal::MetricNotPositiveDefinite {
                    metric: name,
                    coordinate: k,
                    pivot: format!("{}/{}", pivot.numer(), pivot.denom()),
                });
            }
            pivots[k] = pivot;
            for i in (k + 1)..extent {
                let mut entry = gram.get(i, k)?.clone();
                for j in 0..k {
                    entry -= &lower[i][j] * &lower[k][j] * &pivots[j];
                }
                lower[i][k] = entry / &pivots[k];
            }
        }
        // The certificate certifies nothing unless it reconstructs the declared Gram matrix.
        for row in 0..extent {
            for column in 0..extent {
                let mut entry = Rat::zero();
                for j in 0..extent {
                    entry += &lower[row][j] * &pivots[j] * &lower[column][j];
                }
                if &entry != gram.get(row, column)? {
                    return Err(EditRigidityRefusal::MetricFactorizationDisagrees {
                        metric: name,
                        row,
                        column,
                    });
                }
            }
        }
        let lower = ExactRatMatrix::shaped(extent, extent, lower)?;
        let factor_rank = lower.rank()?;
        if factor_rank != extent {
            return Err(EditRigidityRefusal::MetricFactorSingular {
                metric: name,
                rank: factor_rank,
                extent,
            });
        }
        Ok(Self {
            name,
            gram,
            certificate: MetricCertificate {
                pivots,
                lower,
                factor_rank,
            },
        })
    }

    /// The unit metric. **This is one declaration and not a default**; nothing in this module
    /// supplies it unless a caller asks for it by name.
    pub fn unit(name: impl Into<String>, extent: usize) -> Result<Self, EditRigidityRefusal> {
        bounded("a declared metric extent", extent, CHART_CEILING)?;
        if extent == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        Self::declared(name, ExactRatMatrix::identity(extent)?)
    }

    /// A declared diagonal metric: one exact positive weight per coordinate.
    pub fn diagonal(
        name: impl Into<String>,
        weights: Vec<Rat>,
    ) -> Result<Self, EditRigidityRefusal> {
        bounded("a declared metric extent", weights.len(), CHART_CEILING)?;
        if weights.is_empty() {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        Self::declared(name, ExactRatMatrix::from_diagonal(weights)?)
    }

    /// The metric's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The exact Gram matrix.
    pub fn gram(&self) -> &ExactRatMatrix {
        &self.gram
    }

    /// The checked positive-definiteness certificate.
    pub fn certificate(&self) -> &MetricCertificate {
        &self.certificate
    }

    /// The metric's extent.
    pub fn extent(&self) -> usize {
        self.gram.rows()
    }

    /// **`‖x‖²_M`, exact.** The receiver reports the square; it never takes a root.
    pub fn squared_norm(&self, x: &[Rat]) -> Result<Rat, EditRigidityRefusal> {
        if x.len() != self.extent() {
            return Err(EditRigidityRefusal::WidthDisagrees {
                what: "a metric reading",
                declared: self.extent(),
                found: x.len(),
            });
        }
        let image = self.gram.apply(x)?;
        Ok(x.iter()
            .zip(&image)
            .fold(Rat::zero(), |sum, (left, right)| sum + left * right))
    }
}

// -------------------------------------------------------------------------------------------
// T4 (c) — the compensating family, its minimizer and the obstruction
// -------------------------------------------------------------------------------------------

/// **The left-null covector certifying that no compensation exists.**
///
/// Both halves are checked before this value is constructed: `wᵀ (J_keep A) = 0` and
/// `⟨w, J_keep g⟩ ≠ 0`. An obstruction is a return.
///
/// Lean counterpart: `obstructed_iff_certificate`, which is the Fredholm alternative
/// `mem_range_iff_annihilators_vanish`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ObstructionCertificate {
    /// The covector `w`.
    pub left_null: Vec<Rat>,
    /// `⟨w, J_keep g⟩`, exact and nonzero.
    pub pairing: Rat,
    /// The kept faces the covector is supported at: the faces the edit cannot leave alone.
    pub support: Vec<usize>,
}

/// **What a proposed edit is, read at the declared kept receivers and the declared metric.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum EditVerdict {
    /// The edit is invisible to every kept receiver: `W² = 0` and the zero compensation suffices.
    Free {
        /// `W²`, which is exactly zero.
        squared_work: Rat,
    },
    /// The edit is compensable: the exhibited minimizer restores every kept face.
    Compensable {
        /// The minimizing compensation `δ*`, exact.
        compensation: Vec<Rat>,
        /// `W² = ‖δ*‖²_M`, an exact rational. **Never a root and never a float.**
        squared_work: Rat,
        /// The chart coordinates `δ*` moves: which attached regions had to move together.
        support: Vec<usize>,
        /// The dimension of the compensating family's own kernel: how plural the minimizer's
        /// affine family is before the metric selects inside it.
        family_dimension: usize,
    },
    /// No compensation exists inside the declared allowed subspace, with the certificate.
    Obstructed {
        /// The left-null certificate.
        certificate: ObstructionCertificate,
    },
}

impl EditVerdict {
    /// `W²` when there is one. An obstructed edit has none: the work of an impossible compensation
    /// is not a large number, it is a different return.
    pub fn squared_work(&self) -> Option<&Rat> {
        match self {
            Self::Free { squared_work } | Self::Compensable { squared_work, .. } => {
                Some(squared_work)
            }
            Self::Obstructed { .. } => None,
        }
    }

    /// The coordinates the compensation moves.
    pub fn support(&self) -> BTreeSet<usize> {
        match self {
            Self::Free { .. } | Self::Obstructed { .. } => BTreeSet::new(),
            Self::Compensable { support, .. } => support.iter().copied().collect(),
        }
    }

    /// The arm's name, for receipts and refusals.
    pub fn arm(&self) -> &'static str {
        match self {
            Self::Free { .. } => "free",
            Self::Compensable { .. } => "compensable",
            Self::Obstructed { .. } => "obstructed",
        }
    }
}

/// **The complete return of one rethreading question**: the verdict, the cost receipt beside it,
/// and the declarations both were taken under.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RethreadingReceipt {
    /// The wire schema.
    pub schema: String,
    /// The edit's declared name.
    pub edit: String,
    /// The allowed subspace's declared name.
    pub allowed: String,
    /// The metric's declared name. **`W²` is meaningless without it.**
    pub metric: String,
    /// What the kept family is the kept family of.
    pub lineage: String,
    /// The verdict.
    pub verdict: EditVerdict,
    /// How many allowed directions the returned minimizer's normal equation was checked at. A
    /// direction with a nonzero pairing refuses the whole reading, so this is a count of the
    /// checked obligations and never a claim standing in for them.
    pub normal_equation_directions_checked: usize,
    /// The cost of performing the compensation, as `presentation_cost`'s own receipt. **The scalar
    /// `W²` is one receiver of the edit; this is another, and neither is its identity.**
    pub cost: CostReceipt,
}

/// **`W_knot(g | A)² = inf_{δ ∈ C_g} ‖δ‖²_M`, exactly.**
///
/// One `preimage_fibre` decides consistency; the minimizer over the resulting affine family is one
/// exact normal-equation solve. Every returned value is checked before it is returned: the
/// compensation restores every kept face, the normal equation holds at every allowed direction, and
/// `W² = 0` exactly when the edit is free.
///
/// Lean counterparts: `compensating_iff_solves`, `compensating_family_is_affine`,
/// `obstructed_iff_certificate`, `normal_equation_gives_the_unique_minimizer`, `work_zero_iff_free`.
pub fn rethreading_work(
    jacobian: &KeptReceiverJacobian,
    edit: &EditDirection,
    allowed: &AllowedCompensation,
    metric: &ExactMetric,
) -> Result<RethreadingReceipt, EditRigidityRefusal> {
    jacobian.validated()?;
    let dimension = jacobian.dimension();
    if edit.dimension() != dimension {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "an edit direction against the kept chart",
            declared: dimension,
            found: edit.dimension(),
        });
    }
    if allowed.dimension() != dimension {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "an allowed subspace against the kept chart",
            declared: dimension,
            found: allowed.dimension(),
        });
    }
    if metric.extent() != dimension {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "a declared metric against the kept chart",
            declared: dimension,
            found: metric.extent(),
        });
    }
    bounded_product(
        "a rethreading elimination",
        &[jacobian.face_count(), allowed.rank_bound().max(1), dimension],
        ELIMINATION_WORK_CEILING,
    )?;

    let defect = jacobian.matrix().apply(edit.vector())?;
    let is_free = defect.iter().all(Zero::is_zero);
    let target: Vec<Rat> = defect.iter().map(|entry| -entry.clone()).collect();
    let allowed_matrix = allowed.matrix()?;
    let system = jacobian.matrix().multiply(&allowed_matrix)?;

    let Some((particular, family)) = system.preimage_fibre(&target)? else {
        let Some(left_null) = system.preimage_obstruction(&target)? else {
            return Err(EditRigidityRefusal::ObstructionWithoutCertificate);
        };
        let transposed = system.transpose()?;
        let annihilates = transposed.apply(&left_null)?;
        if annihilates.iter().any(|entry| !entry.is_zero()) {
            return Err(EditRigidityRefusal::CertificateFails {
                what: "the covector does not annihilate the compensable defects",
            });
        }
        let pairing = left_null
            .iter()
            .zip(&defect)
            .fold(Rat::zero(), |sum, (left, right)| sum + left * right);
        if pairing.is_zero() {
            return Err(EditRigidityRefusal::CertificateFails {
                what: "the covector reads the edit's defect as zero",
            });
        }
        let support = left_null
            .iter()
            .enumerate()
            .filter(|(_, entry)| !entry.is_zero())
            .map(|(at, _)| at)
            .collect::<Vec<_>>();
        let certificate = ObstructionCertificate {
            left_null,
            pairing,
            support,
        };
        let verdict = EditVerdict::Obstructed { certificate };
        let cost = compensation_cost(jacobian, edit, &verdict)?;
        return Ok(RethreadingReceipt {
            schema: RETHREADING_SCHEMA.to_owned(),
            edit: edit.name().to_owned(),
            allowed: allowed.name().to_owned(),
            metric: metric.name().to_owned(),
            lineage: jacobian.lineage().to_owned(),
            verdict,
            normal_equation_directions_checked: 0,
            cost,
        });
    };

    // `δ₀ = A c₀` is one point of the affine compensating family; `A K` spans its directions.
    let base = allowed_matrix.apply(&particular)?;
    let family_dimension = family.len();
    let directions: Vec<Vec<Rat>> = family
        .iter()
        .map(|vector| allowed_matrix.apply(vector))
        .collect::<Result<Vec<_>, _>>()?;

    let minimizer = if directions.is_empty() {
        base
    } else {
        // Columns of `P`, then the exact normal equations `(Pᵀ M P) y = −Pᵀ M δ₀`.
        let column_rows = (0..dimension)
            .map(|row| {
                directions
                    .iter()
                    .map(|column| column[row].clone())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let p = ExactRatMatrix::shaped(dimension, directions.len(), column_rows)?;
        let metric_p = metric.gram().multiply(&p)?;
        let normal = p.transpose()?.multiply(&metric_p)?;
        let metric_base = metric.gram().apply(&base)?;
        let rhs = directions
            .iter()
            .map(|direction| {
                -direction
                    .iter()
                    .zip(&metric_base)
                    .fold(Rat::zero(), |sum, (left, right)| sum + left * right)
            })
            .collect::<Vec<_>>();
        let Some((coefficients, _)) = normal.preimage_fibre(&rhs)? else {
            return Err(EditRigidityRefusal::NormalEquationInconsistent);
        };
        let shift = p.apply(&coefficients)?;
        base.iter()
            .zip(&shift)
            .map(|(left, right)| left + right)
            .collect::<Vec<_>>()
    };

    // Checked: the compensation really compensates.
    let corrected: Vec<Rat> = edit
        .vector()
        .iter()
        .zip(&minimizer)
        .map(|(left, right)| left + right)
        .collect();
    let residual = jacobian.matrix().apply(&corrected)?;
    if let Some(face) = residual.iter().position(|entry| !entry.is_zero()) {
        return Err(EditRigidityRefusal::CompensationDoesNotCompensate { face });
    }

    // Checked: the normal equation holds at every allowed direction, which is what makes the
    // returned point the minimizer rather than merely a member of the family.
    let metric_minimizer = metric.gram().apply(&minimizer)?;
    for (at, direction) in directions.iter().enumerate() {
        let pairing = direction
            .iter()
            .zip(&metric_minimizer)
            .fold(Rat::zero(), |sum, (left, right)| sum + left * right);
        if !pairing.is_zero() {
            return Err(EditRigidityRefusal::NormalEquationFails { direction: at });
        }
    }

    let squared_work = metric.squared_norm(&minimizer)?;
    if squared_work.is_zero() != is_free {
        return Err(EditRigidityRefusal::WorkVerdictDisagrees {
            work_is_zero: squared_work.is_zero(),
            is_free,
        });
    }
    let verdict = if is_free {
        EditVerdict::Free { squared_work }
    } else {
        let support = minimizer
            .iter()
            .enumerate()
            .filter(|(_, entry)| !entry.is_zero())
            .map(|(at, _)| at)
            .collect::<Vec<_>>();
        EditVerdict::Compensable {
            compensation: minimizer,
            squared_work,
            support,
            family_dimension,
        }
    };
    let cost = compensation_cost(jacobian, edit, &verdict)?;
    Ok(RethreadingReceipt {
        schema: RETHREADING_SCHEMA.to_owned(),
        edit: edit.name().to_owned(),
        allowed: allowed.name().to_owned(),
        metric: metric.name().to_owned(),
        lineage: jacobian.lineage().to_owned(),
        verdict,
        normal_equation_directions_checked: directions.len(),
        cost,
    })
}

/// The cost of performing one compensation, as `presentation_cost`'s receipt.
///
/// Every coordinate names what it counted. **None of them is `W²`**: the receipt and the scalar are
/// two receivers of one edit, and the plan's finding is that they order edits differently.
fn compensation_cost(
    jacobian: &KeptReceiverJacobian,
    edit: &EditDirection,
    verdict: &EditVerdict,
) -> Result<CostReceipt, EditRigidityRefusal> {
    let edit_support = edit.support();
    let compensation_support = verdict.support();
    let touched: BTreeSet<usize> = edit_support.union(&compensation_support).copied().collect();
    let mut rereads = 0usize;
    for face in 0..jacobian.face_count() {
        let support = jacobian.face_support(face)?;
        if !support.is_disjoint(&touched) {
            rereads += 1;
        }
    }
    let obstructed_faces = match verdict {
        EditVerdict::Obstructed { certificate } => certificate.support.len(),
        _ => 0,
    };
    Ok(CostReceipt {
        presentation: format!("rethreading {:?} at {}", edit.name(), jacobian.lineage()),
        bytes: Counted::measured(
            BigUint::from(edit_support.len()),
            "edit_rigidity::EditDirection::support",
        ),
        decode_work: Counted::derived(
            BigUint::from(touched.len()),
            "the coordinates the edit and its compensation touch together",
        ),
        update_work: Counted::measured(
            BigUint::from(compensation_support.len()),
            "edit_rigidity::EditVerdict::support",
        ),
        certificate_work: Counted::derived(
            BigUint::from(rereads),
            "the kept faces reading a touched coordinate, which must be re-read to certify the \
             compensation",
        ),
        residual: Counted::derived(
            BigUint::from(obstructed_faces),
            "one bit per kept face the obstruction certificate is supported at: the compensation \
             carries none of them, and a compensable edit owes none",
        ),
    })
}

/// **The plural reading over an `Open` kept face.**
///
/// A kept face that may or may not be admitted makes the kept family plural exactly as
/// `physical_constraint_grading` makes the constraint complex plural, so the verdict is a family
/// too: both bounds are constructed and neither is promoted. This founds no third carrier — the
/// caller supplies the two members, which for a placement chart are
/// `rigidity_receiver::rigidity_jacobian_member` at the refusing and admitting laws.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PluralRethreading {
    /// The reading with every open face refused.
    pub refusing: RethreadingReceipt,
    /// The reading with every open face founded.
    pub admitting: RethreadingReceipt,
    /// **The finding on the actual data**: whether the open class changes the verdict's arm.
    pub arms_differ: bool,
    /// Whether the open class changes `W²`.
    pub work_differs: bool,
}

/// Read one edit against both bounds of an open kept family. Neither bound is resolved.
pub fn plural_rethreading(
    refusing: &KeptReceiverJacobian,
    admitting: &KeptReceiverJacobian,
    edit: &EditDirection,
    allowed: &AllowedCompensation,
    metric: &ExactMetric,
) -> Result<PluralRethreading, EditRigidityRefusal> {
    let refusing_receipt = rethreading_work(refusing, edit, allowed, metric)?;
    let admitting_receipt = rethreading_work(admitting, edit, allowed, metric)?;
    let arms_differ = refusing_receipt.verdict.arm() != admitting_receipt.verdict.arm();
    let work_differs =
        refusing_receipt.verdict.squared_work() != admitting_receipt.verdict.squared_work();
    Ok(PluralRethreading {
        refusing: refusing_receipt,
        admitting: admitting_receipt,
        arms_differ,
        work_differs,
    })
}

// -------------------------------------------------------------------------------------------
// T4 (d) — the edit torque
// -------------------------------------------------------------------------------------------

/// **The admitted generator family**: the edit directions the revision process may take, as the
/// columns of the generator matrix.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratorFamily {
    name: String,
    dimension: usize,
    generators: Vec<EditDirection>,
}

impl GeneratorFamily {
    /// Declare a family. **An empty family is refused by name**: a torque read over no generator is
    /// not a torque reading.
    pub fn declared(
        name: impl Into<String>,
        dimension: usize,
        generators: Vec<EditDirection>,
    ) -> Result<Self, EditRigidityRefusal> {
        let name = name.into();
        if generators.is_empty() {
            return Err(EditRigidityRefusal::EmptyProbe {
                what: "a declared generator family",
            });
        }
        bounded("a generator family size", generators.len(), GENERATOR_CEILING)?;
        bounded("a generator chart", dimension, CHART_CEILING)?;
        bounded_product(
            "a generator matrix",
            &[generators.len(), dimension],
            ELIMINATION_WORK_CEILING,
        )?;
        for generator in &generators {
            if generator.dimension() != dimension {
                return Err(EditRigidityRefusal::WidthDisagrees {
                    what: "a declared generator",
                    declared: dimension,
                    found: generator.dimension(),
                });
            }
        }
        Ok(Self {
            name,
            dimension,
            generators,
        })
    }

    /// The family's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The chart's dimension.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// The generators.
    pub fn generators(&self) -> &[EditDirection] {
        &self.generators
    }

    /// How many generators.
    pub fn len(&self) -> usize {
        self.generators.len()
    }

    /// Whether the family is empty. It never is: the constructor refuses one.
    pub fn is_empty(&self) -> bool {
        self.generators.is_empty()
    }

    /// The `n × k` matrix whose columns are the generators.
    pub fn matrix(&self) -> Result<ExactRatMatrix, EditRigidityRefusal> {
        let rows = (0..self.dimension)
            .map(|row| {
                self.generators
                    .iter()
                    .map(|generator| generator.vector()[row].clone())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Ok(ExactRatMatrix::shaped(
            self.dimension,
            self.generators.len(),
            rows,
        )?)
    }
}

/// **The unresolved difference at the declared receivers.** One exact rational per receiver row.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverResidual {
    name: String,
    values: Vec<Rat>,
}

impl ReceiverResidual {
    /// Declare a residual over a receiver family of the given size.
    pub fn declared(name: impl Into<String>, values: Vec<Rat>) -> Result<Self, EditRigidityRefusal> {
        if values.is_empty() {
            return Err(EditRigidityRefusal::EmptyProbe {
                what: "a declared receiver residual",
            });
        }
        bounded("a receiver residual width", values.len(), KEPT_FACE_CEILING)?;
        Ok(Self {
            name: name.into(),
            values,
        })
    }

    /// The residual's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The exact values.
    pub fn values(&self) -> &[Rat] {
        &self.values
    }

    /// How many receivers.
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Whether the residual carries no receiver. It never does: the constructor refuses one.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Whether every receiver reads zero: the difference is resolved at this family.
    pub fn is_zero(&self) -> bool {
        self.values.iter().all(Zero::is_zero)
    }
}

/// **`τ = J_g^† r` in edit coordinates.**
///
/// The adjoint is the **metric** adjoint `M⁻¹ J_gᵀ N`, because the adjoint uses the morphology that
/// produced the forward carriers. A bare transpose is this object only when both declared metrics
/// are the identity, and this value carries whether that is the case on the actual data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EditTorque {
    /// The wire schema.
    pub schema: String,
    /// The generator family's declared name.
    pub generators: String,
    /// The residual's declared name.
    pub residual: String,
    /// The edit-coordinate metric's declared name.
    pub edit_metric: String,
    /// The receiver metric's declared name.
    pub receiver_metric: String,
    /// One exact rational per admitted generator.
    pub values: Vec<Rat>,
    /// `J_gᵀ r`: the bare transpose, carried beside the adjoint so the difference is visible and
    /// not silently assumed away.
    pub bare_transpose: Vec<Rat>,
    /// Whether the two agree on this data.
    pub bare_transpose_agrees: bool,
    /// `τ = 0`: an equilibrium of the revision process **at first order**, which is not
    /// cancellation.
    pub is_zero: bool,
    /// How many `(generator, receiver)` pairs the adjoint characterization was checked at. The
    /// coordinate pairs span both spaces, so a zero defect at all of them is a complete check of a
    /// bilinear identity; that is stated, not assumed.
    pub adjoint_pairs_checked: usize,
}

/// **`τ = J_g^† r`, exact, with the adjoint characterization checked on the coordinate probe.**
///
/// Lean counterparts: `torque`, `torque_zero_iff_residual_annihilates_image`,
/// `stationary_iff_torque_zero`, `metric_adjoint_pairs_the_residual_with_the_generators`.
pub fn edit_torque(
    receivers: &KeptReceiverJacobian,
    generators: &GeneratorFamily,
    residual: &ReceiverResidual,
    edit_metric: &ExactMetric,
    receiver_metric: &ExactMetric,
) -> Result<EditTorque, EditRigidityRefusal> {
    receivers.validated()?;
    if generators.dimension() != receivers.dimension() {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "a generator family against the receiver chart",
            declared: receivers.dimension(),
            found: generators.dimension(),
        });
    }
    if residual.len() != receivers.face_count() {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "a residual against the receiver family",
            declared: receivers.face_count(),
            found: residual.len(),
        });
    }
    if edit_metric.extent() != generators.len() {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "an edit metric against the generator family",
            declared: generators.len(),
            found: edit_metric.extent(),
        });
    }
    if receiver_metric.extent() != receivers.face_count() {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "a receiver metric against the receiver family",
            declared: receivers.face_count(),
            found: receiver_metric.extent(),
        });
    }
    let pairs = bounded_product(
        "an adjoint coordinate probe",
        &[generators.len(), receivers.face_count()],
        PROBE_CEILING,
    )?;
    if pairs == 0 {
        return Err(EditRigidityRefusal::EmptyProbe {
            what: "the adjoint characterization check",
        });
    }
    // Each pair costs one forward application and one adjoint application, so the probe's **work**
    // is the square of its cardinality and that is what is bounded before the loop runs.
    bounded_product(
        "an adjoint characterization check",
        &[pairs, pairs],
        ELIMINATION_WORK_CEILING,
    )?;

    let generator_matrix = generators.matrix()?;
    let response = receivers.matrix().multiply(&generator_matrix)?;
    let adjoint = response.metric_adjoint(edit_metric.gram(), receiver_metric.gram())?;

    // The adjoint characterization, checked at every coordinate pair. Both families are finite and
    // the pairing is bilinear, so the coordinate pairs are a spanning probe and a zero defect at
    // all of them is a complete check. The probe is never empty: it is refused above.
    for generator in 0..generators.len() {
        let mut x = vec![Rat::zero(); generators.len()];
        x[generator] = Rat::one();
        for receiver in 0..receivers.face_count() {
            let mut y = vec![Rat::zero(); receivers.face_count()];
            y[receiver] = Rat::one();
            let defect = response.adjoint_defect(
                &adjoint,
                edit_metric.gram(),
                receiver_metric.gram(),
                &x,
                &y,
            )?;
            if !defect.is_zero() {
                return Err(EditRigidityRefusal::AdjointDefect {
                    generator,
                    receiver,
                    defect: format!("{}/{}", defect.numer(), defect.denom()),
                });
            }
        }
    }

    let values = adjoint.apply(residual.values())?;
    let bare_transpose = response.transpose()?.apply(residual.values())?;
    let bare_transpose_agrees = values == bare_transpose;
    let is_zero = values.iter().all(Zero::is_zero);
    Ok(EditTorque {
        schema: EDIT_TORQUE_SCHEMA.to_owned(),
        generators: generators.name().to_owned(),
        residual: residual.name().to_owned(),
        edit_metric: edit_metric.name().to_owned(),
        receiver_metric: receiver_metric.name().to_owned(),
        values,
        bare_transpose,
        bare_transpose_agrees,
        is_zero,
        adjoint_pairs_checked: pairs,
    })
}

/// **The exact rational descent step a nonzero torque admits**, with the exact decrease it
/// produces, both verified by recomputation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactDescent {
    /// The exact step length `⟨τ, Mτ⟩ / ⟨J_g τ, N J_g τ⟩`.
    pub step: Rat,
    /// The exact decrease in the declared squared residual.
    pub decrease: Rat,
    /// The squared residual before the step.
    pub before: Rat,
    /// The squared residual after it, recomputed rather than predicted.
    pub after: Rat,
}

/// **The exact descent step.** A nonzero torque always admits one, because `⟨τ, Mτ⟩ = ⟨J_g τ, N r⟩`
/// forces `J_g τ ≠ 0`. A vanishing torque returns [`EditRigidityRefusal::NoDescentFromZeroTorque`]:
/// stationarity is the answer, not a step of length zero.
///
/// Lean counterparts: `torque_nonzero_has_nonzero_image`, `the_exact_descent_step`.
pub fn descent_step(
    receivers: &KeptReceiverJacobian,
    generators: &GeneratorFamily,
    residual: &ReceiverResidual,
    edit_metric: &ExactMetric,
    receiver_metric: &ExactMetric,
    torque: &EditTorque,
) -> Result<ExactDescent, EditRigidityRefusal> {
    if torque.is_zero {
        return Err(EditRigidityRefusal::NoDescentFromZeroTorque);
    }
    let generator_matrix = generators.matrix()?;
    let response = receivers.matrix().multiply(&generator_matrix)?;
    let image = response.apply(&torque.values)?;
    let numerator = edit_metric.squared_norm(&torque.values)?;
    // The supplied torque is a caller-held value, so the adjoint identity `⟨τ, Mτ⟩ = ⟨J_g τ, N r⟩`
    // is re-derived here rather than trusted. It holds exactly when `τ` is this residual's own
    // adjoint pullback, so a torque from elsewhere is refused rather than stepped along.
    let receiver_image = receiver_metric.gram().apply(residual.values())?;
    let pairing = image
        .iter()
        .zip(&receiver_image)
        .fold(Rat::zero(), |sum, (left, right)| sum + left * right);
    if pairing != numerator {
        return Err(EditRigidityRefusal::CertificateFails {
            what: "the supplied torque is not this residual's adjoint pullback",
        });
    }
    let denominator = receiver_metric.squared_norm(&image)?;
    if denominator.is_zero() {
        return Err(EditRigidityRefusal::CertificateFails {
            what: "a nonzero torque with a vanishing image, which the adjoint identity forbids",
        });
    }
    let step = &numerator / &denominator;
    let decrease = &numerator * &numerator / &denominator;
    let before = receiver_metric.squared_norm(residual.values())?;
    let after_vector: Vec<Rat> = residual
        .values()
        .iter()
        .zip(&image)
        .map(|(left, right)| left - &step * right)
        .collect();
    let after = receiver_metric.squared_norm(&after_vector)?;
    if &before - &decrease != after {
        return Err(EditRigidityRefusal::CertificateFails {
            what: "the recomputed squared residual after the exact step",
        });
    }
    Ok(ExactDescent {
        step,
        decrease,
        before,
        after,
    })
}

// -------------------------------------------------------------------------------------------
// T4 (e) — the knot
// -------------------------------------------------------------------------------------------

/// **The row of the virtual kept face joining two occurrences of a placement chart:**
/// `2(q_i − q_j)` in block `i` and its negative in block `j`. This is the row law
/// `rigidity_receiver` uses for a declared separation, applied to a pair that may carry no declared
/// face at all — which is what "is this pair held anyway" asks.
///
/// Lean counterpart: `pairRow`, with `pairRow_pairing`.
pub fn pair_row(
    places: &[Vec<Rat>],
    dimension: usize,
    left: usize,
    right: usize,
) -> Result<Vec<Rat>, EditRigidityRefusal> {
    if dimension == 0 {
        return Err(EditRigidityRefusal::EmptyChart);
    }
    let width = bounded_product(
        "a pair row",
        &[places.len(), dimension],
        ELIMINATION_WORK_CEILING,
    )?;
    for occurrence in [left, right] {
        if occurrence >= places.len() {
            return Err(EditRigidityRefusal::CoordinateOutsideChart {
                coordinate: occurrence,
                dimension: places.len(),
            });
        }
        if places[occurrence].len() != dimension {
            return Err(EditRigidityRefusal::WidthDisagrees {
                what: "a declared place",
                declared: dimension,
                found: places[occurrence].len(),
            });
        }
    }
    let two = Rat::from_integer(BigInt::from(2));
    let mut row = vec![Rat::zero(); width];
    for axis in 0..dimension {
        let entry = &two * (&places[left][axis] - &places[right][axis]);
        row[left * dimension + axis] = entry.clone();
        row[right * dimension + axis] = -entry;
    }
    Ok(row)
}

/// **Whether a declared pair row lies in the span of the kept faces induced inside a region.**
///
/// "Induced inside" is exactly the faces whose support is contained in the region; a face reaching
/// outside is not a face of that region's framework. The criterion is an exact rank comparison, so
/// the answer is a theorem about the actual rows and not a count.
///
/// Lean counterpart: `ImpliedBy`.
pub fn pair_is_implied_at(
    jacobian: &KeptReceiverJacobian,
    region: &BTreeSet<usize>,
    pair: &[Rat],
) -> Result<bool, EditRigidityRefusal> {
    jacobian.validated()?;
    if pair.len() != jacobian.dimension() {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "a pair row against the kept chart",
            declared: jacobian.dimension(),
            found: pair.len(),
        });
    }
    for coordinate in region {
        if *coordinate >= jacobian.dimension() {
            return Err(EditRigidityRefusal::CoordinateOutsideChart {
                coordinate: *coordinate,
                dimension: jacobian.dimension(),
            });
        }
    }
    // A pair reaching outside the region is not a pair of that region's framework.
    if pair
        .iter()
        .enumerate()
        .any(|(at, entry)| !entry.is_zero() && !region.contains(&at))
    {
        return Ok(false);
    }
    bounded_product(
        "a region implication reading",
        &[jacobian.face_count() + 1, region.len().max(1)],
        ELIMINATION_WORK_CEILING,
    )?;
    let induced = induced_rows(jacobian, region)?;
    let columns: Vec<usize> = region.iter().copied().collect();
    if columns.is_empty() {
        return Ok(pair.iter().all(Zero::is_zero));
    }
    let mut rows: Vec<Vec<Rat>> = induced
        .iter()
        .map(|face| columns.iter().map(|at| face[*at].clone()).collect())
        .collect();
    let base = if rows.is_empty() {
        0
    } else {
        ExactRatMatrix::shaped(rows.len(), columns.len(), rows.clone())?.rank()?
    };
    rows.push(columns.iter().map(|at| pair[*at].clone()).collect());
    let widened = ExactRatMatrix::shaped(rows.len(), columns.len(), rows)?.rank()?;
    Ok(widened == base)
}

/// The kept faces whose whole support lies inside a declared region, with their full rows.
fn induced_rows(
    jacobian: &KeptReceiverJacobian,
    region: &BTreeSet<usize>,
) -> Result<Vec<Vec<Rat>>, EditRigidityRefusal> {
    let mut induced = Vec::new();
    for face in 0..jacobian.face_count() {
        let support = jacobian.face_support(face)?;
        if support.is_subset(region) {
            induced.push(jacobian.matrix().row(face)?.to_vec());
        }
    }
    Ok(induced)
}

/// **The knot reading of one region at one declared scale.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScaleKnotReading {
    /// The scale's declared name — word, sentence, breath.
    pub scale: String,
    /// The region's ordinal inside its scale.
    pub region: usize,
    /// The region's coordinates.
    pub coordinates: Vec<usize>,
    /// The kept faces induced entirely inside the region.
    pub induced_faces: Vec<usize>,
    /// The rank of the induced framework, restricted to the region's coordinates.
    pub rank: usize,
    /// `|region| − rank`: the region's own free-edit dimension.
    pub free_dimension: usize,
    /// `|induced| − rank`: **the self-stress dimension of the knot at this scale.**
    pub self_stress_dimension: usize,
    /// The induced faces in the support of some self-stress of the induced framework.
    pub redundant_faces: Vec<usize>,
}

/// **The declared region ladder**: word, sentence, breath — a list of scales, each a list of
/// coordinate regions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RegionLadder {
    name: String,
    dimension: usize,
    scales: Vec<(String, Vec<BTreeSet<usize>>)>,
}

impl RegionLadder {
    /// Declare a ladder. An empty ladder and an empty scale are both refused by name: a knot
    /// reading taken at no region is not a reading.
    pub fn declared(
        name: impl Into<String>,
        dimension: usize,
        scales: Vec<(String, Vec<BTreeSet<usize>>)>,
    ) -> Result<Self, EditRigidityRefusal> {
        if dimension == 0 {
            return Err(EditRigidityRefusal::EmptyChart);
        }
        bounded("a region ladder chart", dimension, CHART_CEILING)?;
        if scales.is_empty() {
            return Err(EditRigidityRefusal::EmptyLadder);
        }
        bounded("a region ladder scale count", scales.len(), LADDER_SCALE_CEILING)?;
        for (scale, regions) in &scales {
            if regions.is_empty() {
                return Err(EditRigidityRefusal::EmptyScale {
                    scale: scale.clone(),
                });
            }
            bounded("a scale region count", regions.len(), SCALE_REGION_CEILING)?;
            for region in regions {
                // A region with no coordinate induces no framework: every kept face restricted to
                // it is a zero row, which would read as self-stress with no redundant face.
                if region.is_empty() {
                    return Err(EditRigidityRefusal::EmptyRegion {
                        scale: scale.clone(),
                    });
                }
                for coordinate in region {
                    if *coordinate >= dimension {
                        return Err(EditRigidityRefusal::CoordinateOutsideChart {
                            coordinate: *coordinate,
                            dimension,
                        });
                    }
                }
            }
        }
        Ok(Self {
            name: name.into(),
            dimension,
            scales,
        })
    }

    /// The ladder's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The chart's dimension.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// The scales, coarsening or refining in the order the caller declared.
    pub fn scales(&self) -> &[(String, Vec<BTreeSet<usize>>)] {
        &self.scales
    }
}

/// **The knots of an artifact**: the rigid clusters of the placement chart, cited from R4, and the
/// per-scale self-stress reading of the declared region ladder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ArtifactKnots {
    /// R4's own rigid clusters and implied pairs. Nothing here recomputes them.
    pub clusters: RigidClusterReading,
    /// The self-stress dimension of the whole kept family.
    pub self_stress_dimension: usize,
    /// One reading per region per scale.
    pub scales: Vec<ScaleKnotReading>,
}

/// **The knot reading at every declared scale, beside R4's clusters.**
///
/// Lean counterparts: `AmbientKnot` and `ambient_knot_is_downward_closed` for the clusters;
/// `ImpliedBy` and `impliedBy_mono` for the per-scale reading.
pub fn artifact_knots(
    placement: &RigidityJacobian,
    reading: &RigidityReading,
    kept: &KeptReceiverJacobian,
    ladder: &RegionLadder,
    cluster_bound: usize,
) -> Result<ArtifactKnots, EditRigidityRefusal> {
    let clusters = rigid_clusters(placement, reading, cluster_bound)?;
    let scales = scale_knot_readings(kept, ladder)?;
    Ok(ArtifactKnots {
        clusters,
        self_stress_dimension: reading.self_stress_dimension,
        scales,
    })
}

/// The per-scale knot reading of a declared region ladder.
pub fn scale_knot_readings(
    jacobian: &KeptReceiverJacobian,
    ladder: &RegionLadder,
) -> Result<Vec<ScaleKnotReading>, EditRigidityRefusal> {
    jacobian.validated()?;
    if ladder.dimension() != jacobian.dimension() {
        return Err(EditRigidityRefusal::WidthDisagrees {
            what: "a region ladder against the kept chart",
            declared: jacobian.dimension(),
            found: ladder.dimension(),
        });
    }
    if ladder.scales().is_empty() {
        return Err(EditRigidityRefusal::EmptyLadder);
    }
    // One scan of the kept chart per declared region: the product is bounded before the first.
    let total_regions = ladder
        .scales()
        .iter()
        .try_fold(0usize, |sum, (_, regions)| sum.checked_add(regions.len()))
        .ok_or(EditRigidityRefusal::WorkOverflows {
            what: "a scale knot reading",
        })?;
    bounded_product(
        "a scale knot reading",
        &[total_regions, jacobian.face_count().max(1), jacobian.dimension()],
        REPEATED_PASS_WORK_CEILING,
    )?;
    let mut readings = Vec::new();
    for (scale, regions) in ladder.scales() {
        for (ordinal, region) in regions.iter().enumerate() {
            let columns: Vec<usize> = region.iter().copied().collect();
            let mut induced_faces = Vec::new();
            let mut rows = Vec::new();
            for face in 0..jacobian.face_count() {
                let support = jacobian.face_support(face)?;
                if support.is_subset(region) {
                    induced_faces.push(face);
                    let row = jacobian.matrix().row(face)?;
                    rows.push(columns.iter().map(|at| row[*at].clone()).collect::<Vec<_>>());
                }
            }
            let (rank, redundant_faces) = if rows.is_empty() || columns.is_empty() {
                (0, Vec::new())
            } else {
                bounded_product(
                    "an induced knot elimination",
                    &[rows.len(), columns.len()],
                    ELIMINATION_WORK_CEILING,
                )?;
                let matrix = ExactRatMatrix::shaped(rows.len(), columns.len(), rows)?;
                let rank = matrix.rank()?;
                let stresses = matrix.cokernel_annihilator()?;
                let redundant = induced_faces
                    .iter()
                    .enumerate()
                    .filter(|(at, _)| {
                        stresses
                            .iter()
                            .any(|stress| stress.get(*at).is_some_and(|entry| !entry.is_zero()))
                    })
                    .map(|(_, face)| *face)
                    .collect::<Vec<_>>();
                (rank, redundant)
            };
            readings.push(ScaleKnotReading {
                scale: scale.clone(),
                region: ordinal,
                coordinates: columns.clone(),
                self_stress_dimension: induced_faces.len() - rank,
                induced_faces,
                rank,
                free_dimension: columns.len() - rank,
                redundant_faces,
            });
        }
    }
    Ok(readings)
}

/// **The nesting check, executed.** For every declared `(subregion, region)` pair with
/// `subregion ⊆ region`, the faces induced inside the subregion are induced inside the region too,
/// so everything the subregion's framework holds the region's framework holds. That is the
/// direction that is true.
///
/// Lean counterpart: `impliedBy_mono`, with `induced_implication_does_not_descend` the
/// counterexample to the other direction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct KnotAscent {
    /// How many `(subregion, region)` containments were checked.
    pub pairs_checked: usize,
    /// Whether the induced faces ascended at every one of them.
    pub ascends: bool,
    /// The first failure, if there ever were one.
    pub failure: Option<(usize, usize)>,
}

/// Check the ascent over a declared family of regions. **Refuses an empty family by name**: a law
/// checked at no containment is not a checked law.
pub fn knot_ascent(
    jacobian: &KeptReceiverJacobian,
    regions: &[BTreeSet<usize>],
) -> Result<KnotAscent, EditRigidityRefusal> {
    jacobian.validated()?;
    if regions.is_empty() {
        return Err(EditRigidityRefusal::EmptyProbe {
            what: "the knot ascent check",
        });
    }
    bounded("a knot ascent region family", regions.len(), SCALE_REGION_CEILING)?;
    bounded_product(
        "a knot ascent check",
        &[regions.len(), regions.len()],
        PROBE_CEILING,
    )?;
    // The induced family of each declared region is read **once**, so the check's work is the
    // region family's square plus one pass per region and never a pass per ordered pair. The
    // passes are bounded as a product, before the first.
    bounded_product(
        "a knot ascent region pass",
        &[regions.len(), jacobian.face_count().max(1), jacobian.dimension()],
        REPEATED_PASS_WORK_CEILING,
    )?;
    let induced: Vec<BTreeSet<usize>> = regions
        .iter()
        .map(|region| induced_faces_at(jacobian, region))
        .collect::<Result<Vec<_>, _>>()?;
    let mut pairs_checked = 0usize;
    let mut failure = None;
    for (at, sub) in regions.iter().enumerate() {
        for (to, sup) in regions.iter().enumerate() {
            if at == to || !sub.is_subset(sup) {
                continue;
            }
            pairs_checked += 1;
            if !induced[at].is_subset(&induced[to]) && failure.is_none() {
                failure = Some((at, to));
            }
        }
    }
    if pairs_checked == 0 {
        return Err(EditRigidityRefusal::EmptyProbe {
            what: "the knot ascent check, whose declared regions contain none of each other",
        });
    }
    Ok(KnotAscent {
        pairs_checked,
        ascends: failure.is_none(),
        failure,
    })
}

fn induced_faces_at(
    jacobian: &KeptReceiverJacobian,
    region: &BTreeSet<usize>,
) -> Result<BTreeSet<usize>, EditRigidityRefusal> {
    let mut faces = BTreeSet::new();
    for face in 0..jacobian.face_count() {
        if jacobian.face_support(face)?.is_subset(region) {
            faces.insert(face);
        }
    }
    Ok(faces)
}

// -------------------------------------------------------------------------------------------
// T4 (f) — the receipt family a scalar cannot order
// -------------------------------------------------------------------------------------------

/// **Two edits read together**: whether their squared works agree, and whether their receipts are
/// Pareto-comparable. The plan's finding lives here — equal `W²` with incomparable receipts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EditComparison {
    /// The first edit's declared name.
    pub left: String,
    /// The second's.
    pub right: String,
    /// Whether the two squared works are exactly equal.
    pub equal_squared_work: bool,
    /// Whether the two compensation supports are equal as sets.
    pub equal_support: bool,
    /// Whether neither receipt dominates the other on `presentation_cost`'s product order.
    pub incomparable_receipts: bool,
}

/// Compare two rethreading receipts. **The scalar is one receiver of the edit, never its
/// identity**: this returns the disagreement between the two readings rather than a ranking.
pub fn compare_edits(left: &RethreadingReceipt, right: &RethreadingReceipt) -> EditComparison {
    let equal_squared_work = left.verdict.squared_work() == right.verdict.squared_work();
    let equal_support = left.verdict.support() == right.verdict.support();
    EditComparison {
        left: left.edit.clone(),
        right: right.edit.clone(),
        equal_squared_work,
        equal_support,
        incomparable_receipts: left.cost.incomparable_with(&right.cost),
    }
}

/// **How a declared metric orders a declared family of edits.**
///
/// The order is by the exact rational `W²` and the family is returned with its works attached, so a
/// second metric's order can be compared against it. A reordering between two positive-definite
/// metrics is the plan's finding: **friction is a declared receiver.**
pub fn order_by_squared_work(receipts: &[RethreadingReceipt]) -> Vec<(String, Option<Rat>)> {
    let mut family: Vec<(String, Option<Rat>)> = receipts
        .iter()
        .map(|receipt| {
            (
                receipt.edit.clone(),
                receipt.verdict.squared_work().cloned(),
            )
        })
        .collect();
    // An obstructed edit has no work at all and sorts last by that fact, not by a large number.
    family.sort_by(|left, right| match (&left.1, &right.1) {
        (Some(a), Some(b)) => a.cmp(b).then_with(|| left.0.cmp(&right.0)),
        (Some(_), None) => std::cmp::Ordering::Less,
        (None, Some(_)) => std::cmp::Ordering::Greater,
        (None, None) => left.0.cmp(&right.0),
    });
    family
}

// -------------------------------------------------------------------------------------------
// schemas
// -------------------------------------------------------------------------------------------

/// The kept-receiver Jacobian's wire schema.
pub const KEPT_JACOBIAN_SCHEMA: &str = "holonic-engine.edit-rigidity.kept-jacobian.v1";
/// The kept reading's wire schema.
pub const KEPT_READING_SCHEMA: &str = "holonic-engine.edit-rigidity.kept-reading.v1";
/// The rethreading receipt's wire schema.
pub const RETHREADING_SCHEMA: &str = "holonic-engine.edit-rigidity.rethreading.v1";
/// The edit torque's wire schema.
pub const EDIT_TORQUE_SCHEMA: &str = "holonic-engine.edit-rigidity.edit-torque.v1";

#[cfg(test)]
#[path = "edit_rigidity/tests.rs"]
mod tests;
